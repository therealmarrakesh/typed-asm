import StatProgram
import TypedAsm.Tactic

/-!
# Stat: typing and safety

The program is in `StatProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Stat

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

asm_typing At

/-! ## Safety -/

asm_safety At.start

end Stat

