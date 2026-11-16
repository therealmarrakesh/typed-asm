import HelloProgram
import TypedAsm.Tactic

/-!
# Hello: typing, safety, and what it writes

The program is in `HelloProgram.lean`. This file types it and proves it
safe, and proves that what it writes is its message: the block the message
is in says the bytes it holds, and the typing against a system that lets a
`write` through only if it offers exactly those bytes on descriptor 1 is the
proof. It is kept separate so that running the program does not link the
tactics.
-/

open TypedAsm

namespace Hello

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

-- The message is data that is never written, so its block says its bytes.
asm_typing At data

/-! ## Safety, and what is written -/

-- Safe; it ends only with status 0; and wherever it reaches a `write`, the
-- descriptor is 1 and the bytes offered are the message.
asm_safety At.start exits (· = 0) writes (fun fd bytes => fd = 1 ∧ bytes = message)

/-- Everything the program ever adds to the output is the message, or the
first so many bytes of it where the kernel took fewer than it was offered. -/
theorem output_is_message {s s' : State} (h : Entry s) (hs : Steps fetch linux s s') :
    ∃ new, s'.world.writes = new ++ s.world.writes ∧ ∀ w ∈ new, ∃ n, w = message.take n := by
  obtain ⟨new, e, hall⟩ := output_of_entry h s' hs
  refine ⟨new, e, fun w hw => ?_⟩
  obtain ⟨_, _, n, ⟨_, rfl⟩, rfl⟩ := hall w hw
  exact ⟨n, rfl⟩

end Hello
