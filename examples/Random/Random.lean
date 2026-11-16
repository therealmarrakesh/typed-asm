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

asm_safety At.start

end Random

