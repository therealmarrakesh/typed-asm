import OwnProgram
import TypedAsm.U.Checked

/-!
# Own: typing and safety

The program is in `OwnProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

Only the start is a label: the checker follows the program from there. The
theorems hold wherever the kernel puts the memory the program asks for.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Own

/-! ## What the labels want -/

/-- The blocks the program says its segments are. The record: eight bytes,
not to be written. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(Asm.addr code base .record, plainBlock 8 false)]

/-- The program for the checker: its instructions, and that the record is
one of the blocks said. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks (Asm.addr code base .record) }

/-- One label: the start, with nothing known. The program maps two pages,
gives the second back, keeps a pointer to the record and one to the page
itself in the first, follows them, and gives the first back: each use is
of memory it then holds, and what it has given back it does not touch. -/
def labels : List U.Label := [⟨entry, inProgram 0⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 0 program pg labels labels blocks blocks fuel 120

end Own
