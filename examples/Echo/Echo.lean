import EchoProgram
import TypedAsm.U.Checked

/-!
# Echo: typing and safety

The program is in `EchoProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The theorems hold whatever the world outside holds: so whatever the program
is given to read.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Echo

/-! ## What the labels want -/

/-- The blocks the program says its segments are. The buffer: sixteen bytes that may be written. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(Asm.addr code base .buffer, plainBlock 16 true)]

/-- The program for the checker: its instructions; that the buffer is in
one of the blocks said; and that it is to end with status nought. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks (Asm.addr code base .buffer)
    pre := preExits (· == 0) }

/-- One label: the start, which the program comes back to after each line
it echoes, wanting nothing known. That what was read fits the buffer, and
that no more is written than was read, follows from what the calls
answer. -/
def labels : List U.Label := [⟨entry, entryOf 0⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 0 program pg labels labels blocks blocks fuel 30 exits (· == 0)

end Echo
