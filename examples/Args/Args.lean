import ArgsProgram
import TypedAsm.U.Checked

/-!
# Args: typing and safety

The program is in `ArgsProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The theorems hold however many arguments the program is given and whatever
they say.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Args

/-! ## What the labels want -/

/-- The program for the checker: its instructions, and that it is to end
with status nought. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (· == 0) }

/-- The labels. At the start the program finds the count of its arguments
at the stack pointer and, after it, a row of that many pointers to text.
Between arguments `r13` holds the count; within one, `rdi` also points into
its text. That an argument's number is below the count is the program's own
comparison; that there is more text is what each byte read says. -/
def labels : List U.Label :=
  [⟨entry, inArgs⟩,
   ⟨Asm.addr code base .arg, inArgs [(.r13, argCountV)]⟩,
   ⟨Asm.addr code base .scan, inArgs [(.r13, argCountV)] [(.was .rdi, .str (.lit 0))]⟩]

/-! ## The check, and what it shows -/

asm_checked_args code start .start stack 0 program pg labels labels exits (· == 0)

end Args
