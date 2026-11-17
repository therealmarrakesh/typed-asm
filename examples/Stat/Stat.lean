import StatProgram
import TypedAsm.U.Checked

/-!
# Stat: typing and safety

The program is in `StatProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Stat

/-! ## What the labels want -/

/-- The blocks the program says its segments are: the path, text that is
not written and ends in a byte of nought; and the buffer, 144 bytes that
may be written. -/
def blocks : List (BitVec 64 × U.Layout) :=
  blocksWith code .start
    [(Asm.addr code base .path, textBlock (name ++ [0])),
     (Asm.addr code base .buffer, plainBlock 144 true)]

/-- The program for the checker: its instructions; that the path is text;
and that the buffer is one of the blocks said. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticText (Asm.addr code base .path) ++
      staticIn blocks (Asm.addr code base .buffer) }

/-- One label: the start, with nothing known. What each call may be given,
and what may be done with what it answers, is checked at each. -/
def labels : List U.Label := [⟨entry, inProgram 0⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 0 program pg labels labels blocks blocks fuel 60

end Stat
