import KeepProgram
import TypedAsm.U.Checked

/-!
# Keep: typing and safety

The program is in `KeepProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The function `pause` has a label of its own, so it is typed once, for
every caller. Its label says what every function's does: it returns with
the stack pointer past its return address and the registers a function
keeps as it found them. That is what lets the address the program took
before the call, kept in `rbx`, be used after it.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Keep

/-! ## What the labels want -/

/-- The program for the checker: its instructions; and that it is to end with status nought. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (· == 0) }

/-- The labels: the start, with nothing known; and `pause`, a function that
wants nothing. -/
def labels : List U.Label :=
  [⟨entry, entryOf 3⟩, ⟨Asm.addr code base .pause, inFunction⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 3 program pg labels labels fuel 80 exits (· == 0)

end Keep
