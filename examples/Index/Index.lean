import IndexProgram
import TypedAsm.U.Checked

/-!
# Index: typing and safety

The program is in `IndexProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Index

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

/-- The labels. `get` takes in `rdi` a row of as many values as `rsi` says:
whatever row, and however many. In `rdx` it takes any number at all as the
index: the comparison it makes with `rsi` is what lets it read. -/
def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .get, inFunction (known := [(.was .rdi, .arr (.was .rsi) .any)])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 1 program pg labels labels blocks blocks fuel 30

end Index
