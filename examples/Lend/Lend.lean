import LendProgram
import TypedAsm.U.Checked

/-!
# Lend: typing and safety

The program is in `LendProgram.lean`. This file says what its labels want
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

namespace Lend

/-! ## What the labels want -/

/-- The program for the checker: its instructions. -/
def pg : Prog :=
  { code := progCode (Asm.table base code) }

/-- One label: the start, with nothing known. -/
def labels (n : Nat) : List U.Label := [⟨entry, entryOf n⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 4 program pg labels (labels 4) fuel 80

end Lend
