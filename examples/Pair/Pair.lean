import PairProgram
import TypedAsm.U.Checked

/-!
# Pair: typing and safety

The program is in `PairProgram.lean`. This file says what its labels want
and checks it: one check, run as compiled code, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The function `two` has a label of its own, so it is typed once, for every
caller: it uses eight bytes of stack, and hands its caller two pages, one
at the address it returns in `rax` and one at the address it returns in
`rdx`. The program calls it through a register. The checker knows the
register holds the function's address, and so what is wanted there and
what comes back.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Pair

/-! ## What the labels want -/

/-- The program for the checker: its instructions. -/
def pg : Prog :=
  { code := progCode (Asm.table base code) }

/-- The labels: the start, with nothing known; and `two`, which uses eight
bytes of stack and hands its caller a page at each of the addresses it
returns in `rax` and `rdx`. -/
def labels : List U.Label :=
  [⟨entry, inProgram 2⟩,
   ⟨Asm.addr code base .two, inFunction (room := 8) (gives := [(.rax, 4096), (.rdx, 4096)])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 2 program pg labels labels

end Pair
