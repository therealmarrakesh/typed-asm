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

/-- Where the array is. -/
def arr : Val := .lit (Asm.addr code base .array)

/-- How many elements the loop has taken. -/
def i : Val := .named 0

/-- The program for the checker: its instructions, and that the array is in
the segment it was written in. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn (blocksOf code .start) (Asm.addr code base .array) }

/-- The labels. `sum` is entered with the array in `rdi` and its length in
`rsi`; going round the loop, `rdi` is at element `i` and `rsi` is what is
left, for `i` at most four. A function gives back the registers it must as
it found them: that is checked, not said here. -/
def labels : List U.Label :=
  [⟨entry, entryOf 1⟩,
   ⟨Asm.addr code base .sum, inFunction [(.rdi, arr), (.rsi, 5)]⟩,
   ⟨Asm.addr code base .loop,
     inFunction [(.rdi, arr + (i <<< 3)), (.rsi, 5 - i)] [(i, .range 0 4)]⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 1 program pg labels labels fuel 14

end Sum
