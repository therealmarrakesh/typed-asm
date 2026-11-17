import CatProgram
import TypedAsm.U.Checked

/-!
# Cat: typing and safety

The program is in `CatProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The theorems hold however many arguments the program is given and whatever
they are, whatever files there are and whatever they hold.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Cat

/-! ## What the labels want -/

/-- The blocks the program says its segments are. The buffer: sixty-four
bytes that may be written. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(Asm.addr code base .buffer, plainBlock 64 true)]

/-- The program for the checker: its instructions; that the buffer is one
of the blocks said; and that it is to end with status nought or one. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks (Asm.addr code base .buffer)
    pre := preExits (fun c => c == 0 || c == 1) }

/-- The labels. At the start the program finds the count of its arguments
at the stack pointer and, after it, a row of that many pointers to text.
Between files, and between reads of one, `r13` holds the count. A file's
name is an argument whose number the program has compared with the count;
the descriptor in `r12` is a number like any other. -/
def labels : List U.Label :=
  [⟨entry, inArgs⟩,
   ⟨Asm.addr code base .file, inArgs [(.r13, argCountV)]⟩,
   ⟨Asm.addr code base .next, inArgs [(.r13, argCountV)]⟩]

/-! ## The check, and what it shows -/

asm_checked_args code start .start stack 0 program pg labels labels blocks blocks fuel 60
  exits (fun c => c == 0 || c == 1)

end Cat
