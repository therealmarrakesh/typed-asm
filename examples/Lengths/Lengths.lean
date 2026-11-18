import LengthsProgram
import TypedAsm.U.Checked

/-!
# Lengths: typing and safety

The program is in `LengthsProgram.lean`. This file says what its labels
want and checks it: one check, run as compiled code, that the code is typed
and that the state the kernel loads the program into starts as its entry
asks. Nothing is proved by hand.

The function `len` has a label of its own, so it is typed once, for every
caller: it wants eight bytes of stack below its return address, for the
register it keeps. The label of its loop says the function has pushed that
register: so it is held in the stack as it was when the function was
entered, and is given back so. The program's own labels say it has four
slots of stack below its arguments, one of which, the total, is pushed at
its loop.

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
count and the total is pushed. `len` is a function of text, wanting eight
bytes of stack; in its loop it has pushed `r12`, and `rdi` is in text
still. That an argument's number is below the count is the program's own
comparison; that there is more text is what each byte read says. -/
def labels : List U.Label :=
  [⟨entry, inProgram 4⟩,
   ⟨Asm.addr code base .arg, inProgram 4 (pushed := [.any]) (regs := [(.r13, argCountV)])⟩,
   ⟨Asm.addr code base .len, inFunction (known := [(.was .rdi, .str (.lit 0))]) (room := 8)⟩,
   ⟨Asm.addr code base .scan,
     inFunction (known := [(.was .rdi, .str (.lit 0))]) (room := 8) (pushed := [.saved .r12])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 4 program pg labels labels

end Lengths
