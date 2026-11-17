import SwapProgram
import TypedAsm.U.Checked

/-!
# Swap: typing and safety

The program is in `SwapProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Swap

/-! ## What the labels want -/

/-- The program for the checker: its instructions; that the record is in
the segment it was written in; and that it is to end with status nought. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn (blocksOf code .start) (Asm.addr code base .record)
    pre := preExits (· == 0) }

/-- The labels. `swap` takes in `rdi` a pointer to memory it may write, and
gives back the registers a function must as it found them. That the
pointer is still in `rbx` after each call follows; it is not said. -/
def labels : List U.Label :=
  [⟨entry, entryOf 2⟩,
   ⟨Asm.addr code base .swap, inFunction [] [(.was .rdi, .ptr (.mk 4096 .nil) true 0)]⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 2 program pg labels labels fuel 20 exits (· == 0)

end Swap
