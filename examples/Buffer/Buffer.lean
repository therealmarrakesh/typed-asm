import BufferProgram
import TypedAsm.U.Checked

/-!
# Buffer: typing and safety

The program is in `BufferProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Buffer

/-! ## What the labels want -/

/-- The program for the checker: its instructions, and that it is to end
with status nought. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (· == 0) }

/-- The labels: the start; and the loop, where the stack pointer is the
sixteen bytes of the buffer below where it started. -/
def labels : List U.Label :=
  [⟨entry, inProgram 2⟩,
   ⟨Asm.addr code base .loop, inProgram 2 (pushed := 16)⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 2 program pg labels labels fuel 30 exits (· == 0)

end Buffer
