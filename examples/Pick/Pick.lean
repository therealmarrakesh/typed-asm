import PickProgram
import TypedAsm.U.Checked

/-!
# Pick: typing and safety

The program is in `PickProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The theorems hold however many arguments the program is given.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Pick

/-! ## What the labels want -/

/-- The blocks the program says its segments are. The table: thirty-two
bytes, four numbers, not to be written. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(Asm.addr code base .table, plainBlock 32 false)]

/-- The program for the checker: its instructions, and that the table is
one of the blocks said. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks (Asm.addr code base .table) }

/-- One label: the start, where the program finds the count of its
arguments at the stack pointer. It uses the count as an index into the
table only once it has compared it with the table's length. -/
def labels : List U.Label := [⟨entry, inProgram 0⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 0 program pg labels labels blocks blocks

end Pick
