import AllocProgram
import TypedAsm.U.Checked

/-!
# Alloc: typing and safety

The program is in `AllocProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

The theorems hold whatever the program is given to read and wherever the
kernel puts the memory it asks for.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Alloc

/-! ## What the labels want -/

/-- A link: nought, or a pointer to a node that may be written. -/
def link : TyS := .nullable (.ref 1 true 0)

/-- A node: the page `mmap` hands back, with a link in its first eight
bytes. The count and the bytes read are plain bytes after it. -/
def node : ShapeS := .mk 4096 (.cons 0 link .nil)

/-- The one kind of block there is: kind 1 is a node. -/
def kinds : List (Nat × ShapeS) := [(1, node)]

/-- The program for the checker: its instructions; its kinds; and where a
page it holds becomes a node others may point to: once the link has been
stored in it, before its address is kept in `rbx`. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    kinds := kindsOf kinds
    pubs := [⟨instrAddr code 13, .r12, node, some 1⟩] }

/-- The labels: the start; and the two loops, where `rbx` is a link. That
memory was handed back is asked of each `mmap` before it is used. -/
def labels : List U.Label :=
  [⟨entry, inProgram 0⟩,
   ⟨Asm.addr code base .next, inProgram 0 (known := [(.was .rbx, link)])⟩,
   ⟨Asm.addr code base .print, inProgram 0 (known := [(.was .rbx, link)])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 0 program pg labels labels kinds kinds

end Alloc
