import LengthsProgram
import TypedAsm.U.Checked

/-!
# Lengths: typing and safety

The program is in `LengthsProgram.lean`. This file says what its labels
want and checks it: one check, run by Lean's kernel, that the code is typed
and that the state the kernel loads the program into starts as its entry
asks. Nothing is proved by hand.

Each function has a label of its own, so it is typed once, for every
caller. Their labels say how much stack below its return address each
uses: `stop` none, `len` sixteen bytes, eight for the register it keeps and
eight for the address `stop` returns to. The program's own labels say it
has four slots of stack below its arguments, one of which, the total, is
pushed at the loop.

The theorems hold however many arguments the program is given and whatever
they say.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Lengths

/-! ## What the labels want -/

/-- The program for the checker: its instructions. -/
def pg : Prog :=
  { code := progCode (Asm.table base code) }

/-- The labels. At the start the program finds the count of its arguments
at the stack pointer and, after it, a row of that many pointers to text;
it has four slots of stack below them. Between arguments `r13` holds the
count and the total is pushed. `len` is a function of text, wanting sixteen
bytes of stack; `stop` one of text too, wanting none. That an argument's
number is below the count is the program's own comparison; that there is
more text is what each byte read says. -/
def labels : List U.Label :=
  [⟨entry, inArgs (stack := 4)⟩,
   ⟨Asm.addr code base .arg, inArgs [(.r13, argCountV)] (stack := 4) (pushed := 8)⟩,
   ⟨Asm.addr code base .len, inFunction (known := [(.was .rdi, .str (.lit 0))]) (room := 16)⟩,
   ⟨Asm.addr code base .stop, inFunction (known := [(.was .rdi, .str (.lit 0))])⟩]

/-! ## The check, and what it shows -/

asm_checked_args code start .start stack 4 program pg labels labels

end Lengths
