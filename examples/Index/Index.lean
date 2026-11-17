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

/-- Where the array is. -/
def arr : Val := .lit (Asm.addr code base .array)

/-- The program for the checker: its instructions, and that the array is in
the segment it was written in. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn (blocksOf code .start) (Asm.addr code base .array) }

/-- The labels. `get` takes the array in `rdi`, its length in `rsi`, and in
`rdx` any number at all as the index: the comparison it makes is what lets
it read. -/
def labels : List U.Label :=
  [⟨entry, entryOf 1⟩,
   ⟨Asm.addr code base .get, inFunction [(.rdi, arr), (.rsi, 5)]⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 1 program pg labels labels fuel 30

end Index
