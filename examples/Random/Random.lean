import RandomProgram
import TypedAsm.Tactic

/-!
# Random: typing and safety

The program is in `RandomProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the
tactics.
-/

open TypedAsm

namespace Random

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and the program uses no stack. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

asm_typing At

/-! ## Safety -/

-- And it ends only with status 0 or 1: 1 where the kernel handed it nothing.
asm_safety At.start exits (fun c => c = 0 ∨ c = 1)

end Random

