import TypedAsm

/-!
# A recursive function, proved safe

Factorial, written the recursive way: each call that is not the last pushes
its argument, calls itself with one less, and multiplies on the way back.

```asm
_start:
     mov   edi, 5
     call  fact
afterCall:
     mov   edi, eax
     mov   eax, 60              ; `exit`
     syscall
fact:                           ; rdi = n; result in rax
     test  rdi, rdi
     jne   again
     mov   eax, 1
     ret
again:
     push  rdi
     sub   rdi, 1
     call  fact
afterAgain:
     pop   rdi
     imul  rax, rdi
     ret
```

Each level of the recursion uses two stack slots, so the stack a call needs
depends on its argument. The typing says exactly that: the function's
signature is indexed by `n`, takes exactly `n` in `rdi`, and needs `2 * n`
slots. A caller must then have that much room, which is what rules out
running off the end of the stack.

`lake exe fact` runs it in the model; `lake exe fact --elf FILE` writes an
executable that Linux can run.
-/

open TypedAsm

namespace Fact

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterCall | fact | again | afterAgain
  deriving DecidableEq, Hashable

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 5)),
  .call .fact,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fact,
  .ins (.test .w64 (.reg .rdi) (.reg .rdi)),
  .jcc .ne .again,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .ret,
  .label .again,
  .ins (.push .rdi),
  .ins (.alu .sub .w64 (.rm_i (.reg .rdi) 1)),
  .call .fact,
  .label .afterAgain,
  .ins (.pop .rdi),
  .ins (.imul2 .w64 .rax (.reg .rdi)),
  .ins .ret]

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it eleven
-- free stack slots below `rsp`, one for the first return address and two for
-- each of the five levels below it.
asm_program code start .start stack 11 named "fact"

-- 5! = 120.
#guard exitsWith 120 (runMem linux 200 start)

end Fact

