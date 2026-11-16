import ArgsProgram
import TypedAsm.Tactic

/-!
# Args: typing and safety

The program is in `ArgsProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Args

/-! ## The typing -/

/-- The stack as the program finds it when given `c` arguments: the count,
the address of each one's text, and four more words. -/
def slots (c : BitVec 64) : List Shape :=
  [.slot (.eq c), (ShapeOf.slot (.str false)).rep c.toNat, .raw 32]

/-- Between arguments: `r13` holds exactly the count `c` and `r14` exactly
the number `v` of the argument to do next. -/
def loopCtx (c v : BitVec 64) : Ctx :=
  ⟨fun r => if r = .r13 then .eq c else if r = .r14 then .eq v else .int, slots c, 0, Flags.Any, [], 0⟩

/-- Within an argument: also `rsi` points at the start of its text and `rdi`
at the place reached in it. -/
def scanCtx (c v : BitVec 64) : Ctx :=
  ⟨fun r => if r = .r13 then .eq c else if r = .r14 then .eq v
      else if r = .rsi then .str false else if r = .rdi then .str false else .int,
    slots c, 0, Flags.Any, [], 0⟩

/-- The contexts allowed at each label, one for every number of arguments
and every argument reached. -/
inductive At : Label → Ctx → Prop
  | start (c : BitVec 64) : At .start (textsCtx 0 c)
  | arg (c v : BitVec 64) : At .arg (loopCtx c v)
  | scan (c v : BitVec 64) : At .scan (scanCtx c v)

-- The program's one block is the byte that ends a line. The texts of its
-- arguments are blocks too, but they are there only when it runs.
asm_typing At

/-! ## Safety -/

-- Safe however many arguments the program is given and whatever they say.
asm_safety At.start

end Args
