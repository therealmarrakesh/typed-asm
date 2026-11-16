import Rejected.Common

/-!
# What a program writes from what it computed

The message is no data of the program's: it is a number the program loads
into a register and pushes. What the `write` then offers from the stack is
the bytes of that number, least significant first, and the program is
proved to write exactly `Hi!` and a new line; a claim that it writes
something else is refused.
-/

open TypedAsm

namespace Rejected.Spell

inductive Label
  | start
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  -- 'H' 'i' '!' and a new line, the first in the lowest byte
  .ins (.mov .w32 (.rm_i (.reg .rax) 0x0a216948)),
  .ins (.push .rax),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.lea .w64 .rsi (.sib (some .rsp) none 0)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 4)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall]

asm_program code start .start stack 1

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)

asm_typing At

-- what it writes is the four bytes of the number it pushed
example : BlocksOk Φ fetch
    (linux.writesOnly fun fd bytes => fd = 1 ∧ bytes = [0x48, 0x69, 0x21, 0x0a]) Ψ := by
  ty_program

-- and nothing else: not five bytes of it, and not other bytes
/--
error: the block at label `start` does not type by itself:
• at address 4194449: `write`: what the program offers is not shown to be what is wanted
• it offers descriptor 1 the 4 bytes [72, 105, 33, 10], of values it stored
• what is wanted of them does not hold, or is not shown to: 1#64 = 1 ∧ [72#8, 105#8, 33#8, 10#8] = [72, 105, 33, 33]
What it needs is said in a block after `ty_program`, beginning `case start`.
-/
#guard_msgs in
example : BlocksOk Φ fetch
    (linux.writesOnly fun fd bytes => fd = 1 ∧ bytes = [0x48, 0x69, 0x21, 0x21]) Ψ := by
  ty_program

end Rejected.Spell

/-! A message of twelve bytes is two numbers, pushed one after the other:
the buffer then reaches over two pieces of the stack. -/

namespace Rejected.Longer

inductive Label
  | start
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  -- "ou!" and a new line, which come last, are pushed first
  .ins (.mov .w32 (.rm_i (.reg .rax) 0x0a21756f)),
  .ins (.push .rax),
  -- "Hello, y"
  .ins (.movAbs .rax 0x79202c6f6c6c6548),
  .ins (.push .rax),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.lea .w64 .rsi (.sib (some .rsp) none 0)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 12)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall]

asm_program code start .start stack 2

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 2)

asm_typing At

example : BlocksOk Φ fetch
    (linux.writesOnly fun fd bytes => fd = 1 ∧
      -- H e l l o , space y o u ! and a new line
      bytes = [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x79, 0x6f, 0x75, 0x21, 0x0a]) Ψ := by
  ty_program

end Rejected.Longer
