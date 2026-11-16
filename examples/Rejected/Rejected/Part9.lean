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
