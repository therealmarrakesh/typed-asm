import FactProgram
import TypedAsm.U.Checked

/-!
# Fact: typing and safety

The program is in `FactProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

Only the start is a label. The checker follows the program from there, into
its functions and back: they are checked as this program calls them, not
for every caller. A function given a label of its own is checked for every
caller that label allows; see `Swap` and `Frame`.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Fact

/-! ## What the labels want -/

/-- The program for the checker: its instructions; and that it is to end with status 120, the factorial of five. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (· == 120) }

/-- One label: the start, with nothing known. -/
def labels (n : Nat) : List U.Label := [⟨entry, entryOf n⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 11 program pg labels (labels 11) fuel 80 exits (· == 120)

end Fact
