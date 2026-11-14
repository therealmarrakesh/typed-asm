import TypedAsm

/-!
# Summing an array, proved safe

A function that sums `n` 64-bit integers through a moving pointer, with a
loop counter. Its safety depends on the counter and the pointer staying in
step, which the typing expresses with types that depend on values: the
contexts inside the loop are indexed by how many elements have been consumed.

```asm
_start:
   0  lea   rdi, [rip + array]   ; the array is at 0x1000
   7  mov   esi, 5
  12  call  sum
  17  mov   edi, eax
  19  mov   eax, 60              ; Linux `exit`
  24  syscall
  26  jmp   26                   ; not reached: `exit` does not return
sum:                             ; rdi = pointer, rsi = count, result in rax
  31  xor   eax, eax
  33  test  rsi, rsi
  36  je    done
loop:
  42  add   rax, [rdi]
  45  add   rdi, 8
  49  sub   rsi, 1
  53  jne   loop
done:
  59  ret
```
-/

open TypedAsm

namespace Sum

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterCall | spin | sum | loop | done
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.lea .w64 .rdi (.rip 0xff9)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 5)),
  .call .sum,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .spin,
  .jmp .spin,
  .label .sum,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.test .w64 (.reg .rsi) (.reg .rsi)),
  .jcc .e .done,
  .label .loop,
  .ins (.alu .add .w64 (.r_m .rax (.sib (some .rdi) none 0))),
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 8)),
  .ins (.alu .sub .w64 (.rm_i (.reg .rsi) 1)),
  .jcc .ne .loop,
  .label .done,
  .ins .ret]

def fetch : Fetch := Asm.fetch 0 code

def array : List (BitVec 64) := [3, 1, 4, 1, 5]

/-- The starting state: the array in read-only memory at `0x1000` and one
free stack slot below `rsp`. No register points anywhere yet. -/
def start : State :=
  let s := (State.init.setPerm 0x1000 40 .ro).setPerm 0x7ff8 8 .rw
  let s := (array.zipIdx).foldl (fun s (v, i) => s.store64 (0x1000 + 8 * BitVec.ofNat 64 i) v) s
  s.setReg .rsp 0x8000

/-! ## Running it -/

def describe : Outcome → String
  | .next s => s!"still running at rip = {s.rip.toNat}"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

def exitsWith (code : BitVec 32) : Outcome → Bool
  | .exit c => c == code
  | _ => false

-- The program exits with status 14 = 3 + 1 + 4 + 1 + 5.
#guard exitsWith 14 (run fetch linux 100 start)

end Sum

def main : IO Unit :=
  IO.println (Sum.describe (run Sum.fetch linux 100 Sum.start))
