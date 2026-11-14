import TypedAsm

/-!
# Swapping two fields, proved safe

A complete program that is type-checked and then proved safe by the soundness
theorem. A function that swaps the two fields of a record is typed once and
called from two places whose stacks differ. The caller keeps its pointer in
`rbx` across both calls, relying on `swap` to preserve that register.

```asm
_start:                       ; rdi = pointer to a record of two integers
   0  mov   rbx, rdi          ; keep the pointer in a callee-saved register
   3  call  swap              ; called with an empty stack
   8  push  rbx
   9  mov   rdi, rbx          ; rbx is still a pointer after the call
  12  call  swap              ; called with one slot on the stack
  17  pop   rdi
  18  mov   eax, 60           ; Linux `exit`
  23  xor   edi, edi
  25  syscall
spin:
  27  jmp   spin              ; not reached: `exit` does not return
swap:                         ; rdi = pointer to the record
  32  mov   rax, [rdi]
  35  mov   rcx, [rdi+8]
  39  mov   [rdi], rcx
  42  mov   [rdi+8], rax
  46  ret
```
-/

open TypedAsm

namespace Swap

/-! ## The program -/

def field (disp : BitVec 32) : Mem := .sib (some .rdi) none disp

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterFirst | afterSecond | spin | swap
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rdi)) 3,
  .call .swap,
  .label .afterFirst,
  .ins (.push .rbx) 1,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)) 3,
  .call .swap,
  .label .afterSecond,
  .ins (.pop .rdi) 1,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)) 5,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)) 2,
  .ins .syscall 2,
  .label .spin,
  .jmp .spin,
  .label .swap,
  .ins (.mov .w64 (.r_m .rax (field 0))) 3,
  .ins (.mov .w64 (.r_m .rcx (field 8))) 4,
  .ins (.mov .w64 (.rm_r (.mem (field 0)) .rcx)) 3,
  .ins (.mov .w64 (.rm_r (.mem (field 8)) .rax)) 4,
  .ins .ret 1]

def fetch : Fetch := Asm.fetch 0 code

/-- The starting state: a record holding 3 and 5 at `0x1000`, two free stack
slots below `rsp`, and `rdi` pointing at the record. -/
def start : State :=
  (((State.init.setPerm 0x1000 16 .rw).setPerm 0x7ff0 16 .rw).store64 0x1000 3).store64 0x1008 5
    |>.setReg .rsp 0x8000 |>.setReg .rdi 0x1000

/-! ## Running it -/

def describe : Outcome → String
  | .next s => s!"running: record = ({(s.load64 0x1000).toNat}, {(s.load64 0x1008).toNat})"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

def recordIs (x y : BitVec 64) : Outcome → Bool
  | .next s => s.load64 0x1000 == x && s.load64 0x1008 == y
  | _ => false

-- After the first call returns (seven steps) the fields are exchanged, and
-- after the second (eight more) they are back.
#guard recordIs 5 3 (run fetch linux 7 start)
#guard recordIs 3 5 (run fetch linux 15 start)

end Swap

def main : IO Unit := do
  IO.println (Swap.describe (run Swap.fetch linux 0 Swap.start))
  IO.println (Swap.describe (run Swap.fetch linux 7 Swap.start))
  IO.println (Swap.describe (run Swap.fetch linux 15 Swap.start))
  IO.println (Swap.describe (run Swap.fetch linux 100 Swap.start))
