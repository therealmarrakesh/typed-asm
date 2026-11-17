import FrameProgram
import TypedAsm.U.Checked

/-!
# Frame: typing and safety

The program is in `FrameProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Frame

/-! ## What the labels want -/

/-- The program for the checker: its instructions, and that the record is
in the segment it was written in. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn (blocksOf code .start) (Asm.addr code base .record) }

/-- The labels. `pick` takes in `rdi` a pointer to memory it may write, and
uses sixteen bytes of stack below its return address. `spin` goes round for
ever, wanting nothing more than the program's start does. -/
def labels : List U.Label :=
  [⟨entry, entryOf 3⟩,
   ⟨Asm.addr code base .spin, entryOf 3⟩,
   ⟨Asm.addr code base .pick,
     inFunction [] [(.was .rdi, .ptr (.mk 4096 .nil) true 0)] (room := 16)⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 3 program pg labels labels fuel 30

end Frame
