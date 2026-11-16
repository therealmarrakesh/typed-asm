import HelloProgram
import TypedAsm.Tactic

/-!
# What a program writes, where it is not what is claimed

`Hello` writes its message on descriptor 1. Claims that it writes something
else, or to somewhere else, are refused; and nothing is known of what is
written from a block that does not say its bytes.
-/

open TypedAsm

namespace Rejected.Said

open Hello

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

asm_typing At data

-- what it does write
example : BlocksOk Φ fetch (linux.writesOnly fun fd bytes => fd = 1 ∧ bytes = message) Ψ := by
  ty_program

/-- error: the block at label `start` does not type by itself:
• left to be shown: 1#64 = 2
What it needs is said in a block after `ty_program`, beginning `case start`. -/
#guard_msgs in
example : BlocksOk Φ fetch (linux.writesOnly fun fd _ => fd = 2) Ψ := by
  ty_program

/-- error: the block at label `start` does not type by itself:
• left to be shown: List.take (14#64).toNat
    (List.drop 0 [72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33, 10]) =
  List.take 5 message
What it needs is said in a block after `ty_program`, beginning `case start`. -/
#guard_msgs in
example : BlocksOk Φ fetch (linux.writesOnly fun _ bytes => bytes = message.take 5) Ψ := by
  ty_program

end Rejected.Said

namespace Rejected.Unsaid

open Hello

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

-- without `data` the message's block says nothing of its bytes
asm_typing At

/-- error: the block at label `start` does not type by itself:
• `write`: what the program writes is being shown, so the buffer's address in `rsi` must be exactly known, but its type is `read-only pointer to 14 bytes`. A pointer's type does not say which block it points into, and only a block that says its bytes (`asm_typing … data`) has its address kept
`rsi` was given its type by `lea rsi, [rip+3903]` at address 4194490
What it needs is said in a block after `ty_program`, beginning `case start`. -/
#guard_msgs in
example : BlocksOk Φ fetch (linux.writesOnly fun fd _ => fd = 1) Ψ := by
  ty_program

end Rejected.Unsaid

/-! A program may look at the bytes it is about to write. The register keeps
the address as the number it is: the load through it is found in the block
by that number, and the `write` after it is still known for what it offers. -/

namespace Rejected.Peek

inductive Label
  | start | msg
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ref (.lea .w64 .rsi (.rip 0)) .msg,
  .ins (.movzx .w32 .rcx .w8 (.mem (.sib (some .rsi) none 1))),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 2)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall,
  .segment .ro,
  .label .msg, .bytes [72, 105]]

asm_program code start .start

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

asm_typing At data

example : BlocksOk Φ fetch (linux.writesOnly fun fd bytes => fd = 1 ∧ bytes = [72, 105]) Ψ := by
  ty_program

end Rejected.Peek
