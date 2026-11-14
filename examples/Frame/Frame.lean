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

/-- A pointer to a writable record of two integers. -/
def pair : Ty := .ptr [.int, .int] true 0

/-- `pick` takes the pointer in `rdi`, uses two stack slots, and preserves
the callee-saved registers. -/
def pickSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 2

/-- Nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 3, Flags.Any⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 3)
  | afterCall : At .afterCall fin
  | spin : At .spin fin
  | pick (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    pickSig.CallerOk saved ret rest room → At .pick (pickSig.entry saved ret rest room)
  /-- At `skip` the frame is still allocated: local 0 is the pointer, local 1 an integer. -/
  | skip (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (m : Nat) :
    pickSig.CallerOk saved ret rest (m + 2) →
    At .skip ⟨fun r => if calleeSaved r then saved r else .int,
      pair :: .int :: .code ret :: rest, m, Flags.Any⟩

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

def recordLayout : Layout := ⟨[.int, .int], true⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, recordLayout)]

def Ψ : MemTy := .ofList blocks

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
abbrev Entry : State → Prop := TypedAsm.Entry entry base image blocks 3

/-- Any state meeting the entry contract is well typed. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s :=
  ⟨entryCtx 3, by rw [h.rip]; exact .intro At.start,
    fun _ => h.matches HasTy.int (by simp [blocks, recordLayout])⟩

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck,
never page-faults and never executes an invalid opcode. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk (linuxOk fetch Ψ) h.stateOk)

theorem image_length : image.length = 88 := by decide

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start :=
  Entry.ofLoad (by rw [image_length]; decide) (by decide) (by decide) (by decide) (by decide)
    (by simp only [image_length]; decide) (by rw [image_length]; decide)

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

/-- It is also safe on the table machine, which is what the type system reasons about. -/
theorem safe : Safe fetch linux start :=
  soundness_blocks blocksOk memOk (linuxOk fetch Ψ) start_entry.stateOk

end Frame
