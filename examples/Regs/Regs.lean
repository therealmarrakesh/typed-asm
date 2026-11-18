import RegsProgram
import TypedAsm.U.Checked

/-!
# Regs: typing, safety, and that it ends with nought

The program is in `RegsProgram.lean`. This file checks it: one check, run by
Lean's kernel. Nothing is proved by hand, and one label is said, where the
program starts.

That it ends only with status nought is the model of the kernel's word that
a call leaves alone every register but `rax`, `rcx` and `r11`, and puts in
`rcx` the address of the instruction after it: each comparison the program
makes after a call is then of a register with what the checker knows it to
hold, and the way to the other ending is never taken.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Regs

/-- The program for the checker: its instructions; and that it is to end
with status nought. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (· == 0) }

/-- One label: where the program starts. -/
def labels : List U.Label := [⟨entry, inProgram 20⟩]

asm_checked code start .start stack 20 program pg labels labels exits (· == 0)

end Regs
