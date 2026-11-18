import DoubleProgram
import TypedAsm.U.Checked

/-!
# Double: typing and safety

The program is in `DoubleProgram.lean`. This file says what its labels want
and checks it: one check, run as compiled code, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The theorems hold whatever the program is given to read and wherever the
kernel puts the memory it asks for.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Double

/-! ## What the labels want -/

/-- The program for the checker: its instructions. -/
def pg : Prog := { code := progCode (Asm.table base code) }

/-- The labels. `double` takes from its caller the page at the address in
`rdi`, and gives it back when it returns: while it runs the page is its
own, and after it the caller's again. The loop inside it is the same. -/
def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .double, inFunction (takes := [(.was .rdi, 4096)])⟩,
   ⟨Asm.addr code base .loop, inFunction (takes := [(.was .rdi, 4096)])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 1 program pg labels labels

end Double
