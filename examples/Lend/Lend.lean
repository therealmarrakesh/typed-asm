import LendProgram
import TypedAsm.U.Checked

/-!
# Lend: typing, safety, and what it computes

The program is in `LendProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

Each function has a label of its own, so each is typed once, for every
caller. `fill` is handed sixteen bytes at the address in `rdi`: its label
says it takes them and gives them back, holding three and four. `work` has
those sixteen bytes on its own stack. Nothing need be said for the call:
the checker finds that the bytes `fill` wants are part of what `work`
holds, hands that part over, keeps the rest, and has the whole again when
`fill` returns, now holding what `fill` left there. So `work` is seen to
return seven, and the program to end with it.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Lend

/-! ## What the labels want -/

/-- The program for the checker: its instructions, and that it is to end
with status 7. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (· == 7) }

/-- The labels. The start, with nothing known. `work` uses twenty-four
bytes of stack below its return address, its local and the return address
of its call, and returns seven. `fill` takes sixteen bytes at the address
in `rdi` and gives them back holding three and four. -/
def labels : List U.Label :=
  [⟨entry, entryOf 4⟩,
   ⟨Asm.addr code base .work, inFunction (room := 24) (results := [(.rax, 7)])⟩,
   ⟨Asm.addr code base .fill,
     inFunction (takes := [(.rdi, 16)]) (leaves := [(.rdi, [(0, 3), (8, 4)])])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 4 program pg labels labels fuel 80 exits (· == 7)

end Lend
