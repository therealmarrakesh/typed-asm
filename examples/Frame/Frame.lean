import FrameProgram
import TypedAsm.Tactic

/-!
# Frame: typing and safety

The program is in `FrameProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Frame

/-! ## The typing -/

/-- A pointer to a writable record of sixteen plain bytes: two numbers. -/
def pair : Ty := .ptr (.raw 16) true 0

/-- `pick` takes the pointer in `rdi`, uses two stack slots, and preserves
the callee-saved registers. -/
def pickSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 16

/-- Nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 24, Flags.Any, []⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 3)
  | afterCall : At .afterCall fin
  | spin : At .spin fin
  | pick (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    pickSig.CallerOk saved ret rest room → At .pick (pickSig.entry saved ret rest room)
  /-- At `skip` the frame is still allocated: sixteen bytes, the first eight
  of them holding the pointer. -/
  | skip (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (m : Nat) :
    pickSig.CallerOk saved ret rest (m + 16) →
    At .skip ⟨fun r => if calleeSaved r then saved r else .int,
      ⟨16, [(0, pair)]⟩ :: .slot (.code ret) :: rest, m, Flags.Any, ret.owned⟩

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

def recordLayout : Layout := ⟨.raw 16, true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, recordLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + record]
    ty_step
    -- `rdi` holds exactly the record's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .rdi) (base := dataBase) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    ty_block
    ty_call pickSig
  | afterCall => ty_block
  | spin => ty_block
  | pick saved ret rest room hK =>
    -- make the two slots the signature guarantees visible, so the frame can be allocated
    obtain ⟨m, rfl⟩ := hK.room_split
    ty_block
  | skip saved ret rest m hK => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, the record readable and writable, and three writable stack slots below `rsp` that
do not overlap it. This is the contract with whatever loads the program;
for the ELF file, with the Linux kernel. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase recordBytes blocks 3 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck,
never faults: no page fault, no invalid opcode and no divide error. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks, recordLayout]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

/-- It is also safe on the table machine, which is what the type system reasons about. -/
theorem safe : Safe fetch linux start :=
  start_entry.safe blocksOk memOk At.start (Entry.plain (by simp [blocks, recordLayout]))

end Frame

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Frame.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.safeMem
