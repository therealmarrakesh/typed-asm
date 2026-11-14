import TypedAsm

/-!
# A function with a stack frame, proved safe

Exercises stack-frame allocation, locals, 32-bit and byte loads and stores,
a conditional jump in the middle of a block, and a comparison of two exactly
known values.

```asm
_start:                       ; rdi = pointer to a record of two integers
   0  mov   esi, 7
   5  mov   edx, 7
  10  cmp   rsi, rdx
  13  jne   spin              ; never taken, and the types know it
  19  call  pick
  24  mov   edi, eax
  26  mov   eax, 60           ; Linux `exit`
  31  syscall
spin:
  33  jmp   spin
pick:                         ; rdi = pointer to the record; result in rax
  38  sub   rsp, 16           ; two locals
  42  mov   [rsp], rdi        ; local 0: the pointer
  46  mov   eax, [rdi+8]      ; low half of the second field
  49  mov   [rsp+8], rax      ; local 1: that value
  54  mov   [rdi+12], eax     ; 32-bit store into the top half of the second field
  57  mov   [rdi+1], al       ; byte store into the first field
  60  test  rax, rax
  63  je    skip
  69  mov   rcx, [rsp]        ; the local is still a pointer
  73  movzx eax, byte ptr [rcx]
skip:
  76  add   rsp, 16
  80  ret
```
-/

open TypedAsm

namespace Frame

/-! ## The program -/

def rspSlot (disp : BitVec 32) : Mem := .sib (some .rsp) none disp

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterCall | spin | pick | skip
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rsi) 7)) 5,
  .ins (.mov .w32 (.rm_i (.reg .rdx) 7)) 5,
  .ins (.alu .cmp .w64 (.rm_r (.reg .rsi) .rdx)) 3,
  .jcc .ne .spin,
  .call .pick,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)) 2,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)) 5,
  .ins .syscall 2,
  .label .spin,
  .jmp .spin,
  .label .pick,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)) 4,
  .ins (.mov .w64 (.rm_r (.mem (rspSlot 0)) .rdi)) 4,
  .ins (.mov .w32 (.r_m .rax (.sib (some .rdi) none 8))) 3,
  .ins (.mov .w64 (.rm_r (.mem (rspSlot 8)) .rax)) 5,
  .ins (.mov .w32 (.rm_r (.mem (.sib (some .rdi) none 12)) .rax)) 3,
  .ins (.store8 (.sib (some .rdi) none 1) .rax) 3,
  .ins (.test .w64 (.reg .rax) (.reg .rax)) 3,
  .jcc .e .skip,
  .ins (.mov .w64 (.r_m .rcx (rspSlot 0))) 4,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rcx) none 0))) 3,
  .label .skip,
  .ins (.alu .add .w64 (.rm_i (.reg .rsp) 16)) 4,
  .ins .ret 1]

def fetch : Fetch := Asm.fetch 0 code

/-- The starting state: a record holding `0x1234` and 1 at `0x1000`, three
free stack slots below `rsp`, and `rdi` pointing at the record. -/
def start : State :=
  (((State.init.setPerm 0x1000 16 .rw).setPerm 0x7fe8 24 .rw).store64 0x1000 0x1234).store64
      0x1008 1
    |>.setReg .rsp 0x8000 |>.setReg .rdi 0x1000

/-! ## Running it -/

def describe : Outcome → String
  | .next s => s!"still running at rip = {s.rip.toNat}"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

def exitsWith (code : BitVec 32) : Outcome → Bool
  | .exit c => c == code
  | _ => false

-- The second field is not zero, so the result is the low byte of the first: 0x34.
-- (The byte store changed the first field's second byte, not its low byte.)
#guard exitsWith 0x34 (run fetch linux 100 start)

end Frame

def main : IO Unit :=
  IO.println (Frame.describe (run Frame.fetch linux 100 Frame.start))
