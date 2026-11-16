import PickProgram
import TypedAsm.Tactic

/-!
# Pick: typing and safety

The program is in `PickProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Pick

/-! ## The typing -/

/-- The contexts allowed at each label, one for every number of arguments. -/
inductive At : Label → Ctx → Prop
  | start (c : BitVec 64) : At .start (argsCtx 0 c)

asm_typing At

/-! ## Safety -/

-- Safe however many arguments the program is given.
asm_safety At.start

end Pick
