import TypedAsm
import TypedAsm.U.Checked

/-!
# A store over the address a function returns to, named where it is refused

```asm
_start:
     call  f
     xor   edi, edi
     mov   eax, 60
     syscall
f:
     sub   rsp, 8
     mov   ecx, 8
     mov   [rsp + rcx], al       ; one past the buffer: where the return address is
     add   rsp, 8
     ret
```

The program is refused, and why says which store the address was lost at.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.RetLost

inductive L
  | start | f
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .call .f,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .f,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 8)),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 8)),
  .ins (.store8 (.sib (some .rsp) (some (.rcx, .s1)) 0) .rax),
  .ins (.alu .add .w64 (.rm_i (.reg .rsp) 8)),
  .ins .ret]

asm_program code start .start stack 1

def pg : Prog := { code := progCode (Asm.table base code) }

def labels : List U.Label :=
  [⟨entry, inProgram 1⟩, ⟨Asm.addr code base .f, inFunction (room := 8)⟩]

/-- Whether a text has another in it. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

#guard !wholeOkWith code .start 1 [] (blocksOf code .start) pg labels (needFuel pg labels [])
#guard has (wholeWhyText code .start 1 [] (blocksOf code .start) pg labels
    (needFuel pg labels []))
  "was held on the stack until `mov byte ptr [rsp+rcx*1], al`"

end Tests.Written.RetLost
