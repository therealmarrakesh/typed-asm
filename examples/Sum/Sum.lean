import SumProgram
import TypedAsm.U.Checked

/-!
# Sum: typing and safety

The program is in `SumProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Sum

/-! ## What the labels want -/

/-- The blocks the program says its segments are. The array: a row of five
values, not to be written. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(Asm.addr code base .array, rowBlock 5 .any false)]

/-- The program for the checker: its instructions, and that the array is a
row of five values. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticRow (Asm.addr code base .array) 5 .any }

/-- `rdi` is the address of a row of as many values as `rsi` says. -/
def row : List (Val × TyS) := [(.was .rdi, .arr (.was .rsi) .any)]

/-- The labels. `sum` takes in `rdi` a row of as many values as `rsi` says:
whatever row, and however many. Going round the loop the same is so of what
is left, and there is some left: the rest of a row is a row, and the count
was not nought. A function gives back the registers it must as it found
them: that is checked, not said here. -/
def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .sum, inFunction (known := row)⟩,
   ⟨Asm.addr code base .loop, inFunction (known := row ++ [(.was .rsi, .range 1 (-1))])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 1 program pg labels labels blocks blocks fuel 30

end Sum
