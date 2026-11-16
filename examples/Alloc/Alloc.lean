import AllocProgram
import TypedAsm.Tactic

/-!
# Alloc: typing and safety

The program is in `AllocProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Alloc

/-! ## The typing -/

/-- A link: null, or a writable pointer to a node. -/
def link : Ty := .nullable (.ref 1 true 0)

/-- A node, 80 bytes: the link to the node before it, how many bytes it
holds, and room for 64 of them. The link admits zero, so fresh memory is a
node. -/
def nodeShape : Shape := ⟨80, [(0, link)]⟩

/-- The list so far is in `rbx`; nothing is known about the other registers. -/
def listCtx : Ctx := ⟨fun r => if r = .rbx then link else .int, [], 0, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | next : At .next listCtx
  | print : At .print listCtx

-- No blocks of note to begin with, and one kind of block there will be: kind 1
-- is a node.
asm_typing At kinds [(1, nodeShape)]

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program
  case start =>
    -- xor ebx, ebx: the empty list, and on into `next`
    ty_into At.next
  case next =>
    -- the arguments, then the `mmap` for a node
    ty_steps
    ty_mmap_kind 1
    ty_block

/-! ## Safety -/

-- Safe whatever the program is given to read and wherever the kernel puts the
-- memory it asks for.
asm_safety At.start

end Alloc
