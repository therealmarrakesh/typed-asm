import TypedAsm
import TypedAsm.U.Checked

/-!
# What was read, written out in pieces

```asm
_start:
     sub   rsp, 16
     xor   edi, edi
     mov   rsi, rsp
     mov   edx, 16
     xor   eax, eax
     syscall              ; read(0, buf, 16)
     test  rax, rax
     js    done
     jz    done
     mov   rbx, rsp       ; from where to write
     mov   r12, rax       ; how many are left
loop:
     mov   rdx, r12
     mov   rsi, rbx
     mov   edi, 1
     mov   eax, 1
     syscall              ; write(1, rbx, r12): it may take fewer
     test  rax, rax
     js    done
     add   rbx, rax       ; on by as many as it took
     sub   r12, rax
     jne   loop
done:
     xor   edi, edi
     mov   eax, 60
     syscall
```

A `write` may take fewer bytes than it is offered, so a program that means
to write all it read goes round with the rest. Every `write` here is proved
to offer a stretch of what the last `read` stored: the kernel's answer is
known to be no more than was offered, so the pointer stays within what was
read and the count left is what is left of it.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.CatPieces
inductive L
  | start | loop | done
  deriving DecidableEq, Hashable
/-- The program, the pointer moved on by so many times what each `write`
took, and so many bytes more offered than are left. -/
def codeOf (step : Nat) (more : BitVec 32) : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rsp)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 16)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .done,
  .jcc .e .done,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rsp)),
  .ins (.mov .w64 (.rm_r (.reg .r12) .rax)),
  .label .loop,
  .ins (.mov .w64 (.rm_r (.reg .rdx) .r12)),
  .ins (.alu .add .w64 (.rm_i (.reg .rdx) more)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rbx)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .done,
] ++ List.replicate step (.ins (.alu .add .w64 (.rm_r (.reg .rbx) .rax))) ++ [
  .ins (.alu .sub .w64 (.rm_r (.reg .r12) .rax)),
  .jcc .ne .loop,
  .label .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

def code : List (Asm L) := codeOf 1 0

asm_program code start .start stack 2
/-- The buffer: the sixteen bytes the program makes room for. -/
def buf : Val := stackAt 2 [.bytes 16] 0

def pgOf (c : List (Asm L)) : Prog :=
  { code := progCode (Asm.table (Asm.base c) c), pre := preEcho (· == 0) }

/-- The labels: the start; and the loop, where `r12` bytes are left to write
from `rbx`, so far into the buffer that with them it is all that was read,
which the buffer is still said to be. -/
def labelsOf (c : List (Asm L)) : List U.Label :=
  [⟨Asm.addr c (Asm.base c) .start, inProgram 2⟩,
   ⟨Asm.addr c (Asm.base c) .loop, inProgram 2 (pushed := [.bytes 16])
      (regs := [(.rbx, buf + .named 1), (.r12, .named 0)])
      (known := [(.named 0 + .named 1, .range 0 16), (.named 0, .upTo (.named 0 + .named 1) false),
        (.named 1, .upTo (.named 0 + .named 1) false)])
      (rows := [readAt buf (.named 0 + .named 1)])⟩]

/-- Whether the program so made is typed, every `write` to offer a stretch
of the last `read`. -/
def typed (step : Nat) (more : BitVec 32) : Bool :=
  wholeOkWith (codeOf step more) .start 2 [] (blocksOf (codeOf step more) .start)
    (pgOf (codeOf step more)) (labelsOf (codeOf step more))
    (needFuel (pgOf (codeOf step more)) (labelsOf (codeOf step more)) [])

#guard typed 1 0
-- one byte more offered than is left. Refused
#guard !typed 1 1
-- the pointer moved on twice as far as the `write` took: it may pass the end
-- of what was read. Refused
#guard !typed 2 0
-- the pointer not moved on: the count left no longer matches. Refused
#guard !typed 0 0

def pg : Prog := { code := progCode (Asm.table base code), pre := preEcho (· == 0) }

def labels : List U.Label := labelsOf code

asm_checked code start .start stack 2 program pg labels labels exits (· == 0) echoes

end Tests.Written.CatPieces
