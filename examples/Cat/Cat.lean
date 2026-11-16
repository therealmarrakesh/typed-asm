import CatProgram
import TypedAsm.Tactic

/-!
# Cat: typing and safety

The program is in `CatProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Cat

/-! ## The typing -/

/-- The context inside the loop, for a program given `c` arguments that is
about to do argument number `v`: `r13` holds exactly `c`, `r14` exactly `v`,
and the stack is as the program found it. -/
def loopCtx (c v : BitVec 64) : Ctx :=
  ⟨fun r => if r = .r13 then .eq c else if r = .r14 then .eq v else .int,
    [.slot (.eq c), .raw (8 * (c.toNat + 4))], 0, Flags.Any, [], 0⟩

/-- The contexts allowed at each label, one for every number of arguments
and, in the loop, every argument reached. The descriptor in `r12` is a
number like any other. -/
inductive At : Label → Ctx → Prop
  | start (c : BitVec 64) : At .start (argsCtx 0 c)
  | file (c v : BitVec 64) : At .file (loopCtx c v)
  | next (c v : BitVec 64) : At .next (loopCtx c v)

asm_typing At

/-! ## Safety -/

-- Safe however many arguments the program is given and whatever they are,
-- whatever files there are and whatever they hold.
-- And it ends only with status 0 or 1: 1 where it stopped at a file it could
-- not open.
asm_safety At.start exits (fun c => c = 0 ∨ c = 1)

end Cat
