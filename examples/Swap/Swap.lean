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

/-- The blocks the program says its segments are. The record: sixteen bytes that may be written. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(Asm.addr code base .record, plainBlock 16 true)]

/-- The program for the checker: its instructions; that the record is in
one of the blocks said; and that it is to end with status nought. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks (Asm.addr code base .record)
    pre := preExits (· == 0) }

/-- The labels. `swap` takes in `rdi` a pointer to memory it may write, and
gives back the registers a function must as it found them. That the
pointer is still in `rbx` after each call follows; it is not said. -/
def labels : List U.Label :=
  [⟨entry, inProgram 2⟩,
   ⟨Asm.addr code base .swap, inFunction [] [(.was .rdi, .ptr (.mk 16 .nil) true 0)]⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 2 program pg labels labels blocks blocks fuel 20 exits (· == 0)

end Swap
