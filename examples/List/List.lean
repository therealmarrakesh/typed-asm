import ListProgram
import TypedAsm.Tactic

/-!
# List: typing and safety

The program is in `ListProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace List3

-- Where the list is loaded. Each node is sixteen bytes.
asm_label dataBase .first

/-! ## The typing -/

/-- What a node's link holds: zero, or the address of a node. Nodes are the
blocks of kind 1. -/
def link : Ty := .nullable (.ref 1 false 0)

/-- A node: sixteen bytes, a value and then a link. -/
def nodeShape : Shape := ⟨16, [(8, link)]⟩

def nodeLayout : Layout := ⟨nodeShape, false, some 1, 0, none⟩

/-- In the loop `rdi` holds a link. -/
def walking : Ctx := ⟨fun r => if r = .rdi then link else .int, [], 0, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | loop : At .loop walking

/-- Three memory blocks, one for each node. -/
def blocks : List (BitVec 64 × Layout) :=
  [(dataBase, nodeLayout), (dataBase + 16, nodeLayout), (dataBase + 32, nodeLayout)]

-- The blocks, and the one kind of block there is: kind 1 is a node.
asm_typing At blocks blocks kinds [(1, nodeShape)]

/-! ## Safety -/

-- Each node's link holds what the data says, the address of the next node or
-- zero: read from the program's bytes. The program never loads through the
-- zero that ends the list.
asm_safety At.start

end List3
