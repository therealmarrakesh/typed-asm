import FreshProgram
import TypedAsm.U.Checked

/-!
# Fresh: typing and safety

The program is in `FreshProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The theorems hold whatever the program is given to read and wherever the
kernel puts the memory it asks for.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Fresh

/-! ## What the labels want -/

/-- The program for the checker: its instructions. -/
def pg : Prog := { code := progCode (Asm.table base code) }

/-- The labels. `page` hands its caller a page of memory, at the address it
returns in `rax`: for whatever address the kernel chose. In the loop the
program holds that page, at the address in `rbx`, besides its stack. -/
def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .page, inFunction (gives := [(.rax, 4096)])⟩,
   ⟨Asm.addr code base .loop, inProgram 1 (held := [(.was .rbx, ⟨4096, []⟩)])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 1 program pg labels labels

end Fresh
