import RandomProgram
import TypedAsm.U.Checked

/-!
# Random: typing and safety

The program is in `RandomProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Random

/-! ## What the labels want -/

/-- The program for the checker: its instructions; that the buffer is in
the segment it was written in; and that it is to end with status nought or
one. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn (blocksOf code .start) (Asm.addr code base .buffer)
    pre := preExits (fun c => c == 0 || c == 1) }

/-- One label: the start, with nothing known. That the bytes written are no
more than the buffer holds follows from what `getrandom` answers. -/
def labels : List U.Label := [⟨entry, inProgram 0⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 0 program pg labels labels fuel 30
  exits (fun c => c == 0 || c == 1)

end Random
