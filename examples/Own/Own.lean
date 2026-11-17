import OwnProgram
import TypedAsm.Tactic

/-!
# Own: typing and safety

The program is in `OwnProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Own

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and nothing is owned. In particular the program may not arrive at `fail`
still holding a page. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

asm_typing At

/-! ## Safety -/

asm_safety At.start

end Own

