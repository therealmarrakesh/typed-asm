import ListProgram
import TypedAsm.U.Checked

/-!
# List: typing and safety

The program is in `ListProgram.lean`. This file says what its labels want
and checks it: one check, run as compiled code, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace List3

/-! ## What the labels want -/

/-- A link: nought, or a pointer to a node. -/
def link : TyS := .nullable (.ref 1 false 0)

/-- A node: a number, then a link. -/
def node : ShapeS := .mk 16 (.cons 8 link .nil)

/-- The one kind of block there is: kind 1 is a node. -/
def kinds : List (Nat × ShapeS) := [(1, node)]

/-- A node at a label of the data. -/
def nodeAt (l : Label) : BitVec 64 × U.LayoutS :=
  (Asm.addr code base l, { shape := node, writable := false, tag := some 1 })

/-- The blocks the program says its segments are: the three nodes. That
each one's link is nought or the address of a node is read from the
program's bytes. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [nodeAt .first, nodeAt .second, nodeAt .third]

/-- The program for the checker: its instructions; its kinds; and that the
first node is a node. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    kinds := kindsOf kinds
    statics := staticRef blocks (Asm.addr code base .first) }

/-- The labels: the start; and the loop, where `rdi` is a link. The program
never loads through the nought that ends the list: its own test of the link
is what lets it load. -/
def labels : List U.Label :=
  [⟨entry, inProgram 0⟩,
   ⟨Asm.addr code base .loop, inProgram 0 (known := [(.was .rdi, link)])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 0 program pg labels labels blocks blocks kinds kinds

end List3
