import TypedAsm
import TypedAsm.U.Checked

/-!
# Four bytes stored into a number the program made

```asm
_start:
     sub   rsp, 8
     mov   qword [rsp], 0x01020304
     mov   dword [rsp + 4], 5        ; the high half replaced
     mov   dword [rsp], 7            ; and the low
     mov   rdi, [rsp]                ; 0x0000000500000007
     shr   rdi, 32
     mov   eax, 60
     syscall                         ; status 5
```

The number held is known still, with the bytes stored in place: the status
is proved.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Half

inductive L
  | start
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 8)),
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rsp) none 0)) 0x01020304)),
  .ins (.mov .w32 (.rm_i (.mem (.sib (some .rsp) none 4)) 5)),
  .ins (.mov .w32 (.rm_i (.mem (.sib (some .rsp) none 0)) 7)),
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rsp) none 0))),
  .ins (.shift .shr .w64 (.reg .rdi) (.imm 32)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

asm_program code start .start stack 1

#guard exitsWith 5 (runMem linux 100 start)

def pg : Prog := { code := progCode (Asm.table base code), pre := preExits (· == 5) }

def labels : List U.Label := [⟨entry, inProgram 1⟩]

asm_checked code start .start stack 1 program pg labels labels exits (· == 5)

/-- The same program, said to end with seven: as it would if the four bytes
stored last had reached the upper half of the eight. -/
def pgSeven : Prog := { pg with pre := preExits (· == 7) }

-- Refused
#guard !wholeOkWith code .start 1 [] (blocksOf code .start) pgSeven labels (needFuel pgSeven labels [])

end Tests.Written.Half
