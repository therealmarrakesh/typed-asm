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

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- No memory blocks to begin with. -/
def blocks : List (BitVec 64 × Layout) := []

/-- No blocks, and one kind of block there will be: kind 1 is a node. -/
def Ψ : MemTy := .ofList blocks [(1, nodeShape)]

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

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory. Nothing is asked of the input, or of how requests for
memory are answered. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry parts blocks 0 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, whatever it is given to
read and wherever the kernel puts the memory it asks for, the program is
safe on the machine that fetches instructions by decoding memory.** It never
gets stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe whatever input it is given and however its
requests for memory are answered. -/
theorem safeMem (input : List ReadEvent) (place : Nat → Option (BitVec 64)) :
    SafeMem linux (startWith input place) :=
  safeMem_of_entry (start_entry.withWorld _)

end Alloc

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Alloc.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Alloc.safeMem
