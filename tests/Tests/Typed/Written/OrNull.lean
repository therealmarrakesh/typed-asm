import TypedAsm
import TypedAsm.U.Checked

/-!
# A function that hands its caller a page, or nought

```asm
_start:
     call  alloc
     test  rax, rax
     jz    fail
     mov   qword [rax], 7        ; the page is the caller's
     xor   edi, edi
     mov   eax, 60
     syscall
fail:
     mov   edi, 1
     mov   eax, 60
     syscall
alloc:                            ; rax = a fresh page, or 0
     mov   eax, 9
     xor   edi, edi
     mov   esi, 4096
     mov   edx, 3
     mov   r10d, 0x22
     mov   r8, -1
     xor   r9d, r9d
     syscall
     test  rax, rax
     js    nope
     ret
nope:
     xor   eax, eax
     ret
```

The function returns in one of two ways: with nought and nothing more, or
with an address that is not nought and a page there that is then its
caller's. The code it returns to is typed for each.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.OrNull

inductive L
  | start | fail | alloc | nope
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .call .alloc,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .fail,
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rax) none 0)) 7)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .alloc,
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .ins (.mov .w32 (.rm_i (.reg .r10) 0x22)),
  .ins (.mov .w64 (.rm_i (.reg .r8) (-1))),
  .ins (.alu .xor .w32 (.rm_r (.reg .r9) .r9)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .nope,
  .ins .ret,
  .label .nope,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret]

asm_program code start .start stack 1

-- with nothing said of the world outside, the model's `mmap` refuses
#guard exitsWith 1 (runMem linux 100 start)

def pg : Prog :=
  { code := progCode (Asm.table base code), pre := preExits (fun c => c == 0 || c == 1) }

/-- The function: nought handed back; or an address that is not nought,
and a page there. -/
def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .alloc,
     inFunction (results := [(.rax, 0)])
       (orReturns := [returnsWith (gives := [(.given .rax, 4096)])
         (returns := [(.given .rax, .range 1 (-1))])])⟩]

asm_checked code start .start stack 1 program pg labels labels exits (fun c => c == 0 || c == 1)

end Tests.Written.OrNull
