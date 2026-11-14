import OpsProgram
import TypedAsm.Tactic

/-!
# Ops: typing and safety

The program is in `OpsProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Ops

/-! ## The typing -/

/-- A pointer to a writable record of two integers. -/
def pair : Ty := .ptr [.int, .int] true 0

/-- `compute` takes the pointer in `rdi`, uses two stack slots, and
preserves the callee-saved registers. -/
def computeSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 2

/-- After the call: nothing is known about any register, and the slot that
held the function pointer is still allocated. -/
def afterCtx : Ctx := ⟨fun _ => .int, [.int], 3, Flags.Any⟩

/-- Nothing is known about any register, and the stack is empty. -/
def fin : Ctx := ⟨fun _ => .int, [], 4, Flags.Any⟩

/-- What the function pointer in `_start` points to: `compute`, entered by a
caller with one slot on its stack that returns to `afterCall`. -/
def computeCtx : Ctx := computeSig.entry (fun _ => .int) afterCtx [.int] 2

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 4)
  | afterCall : At .afterCall afterCtx
  | finish : At .finish fin
  | spin : At .spin fin
  /-- No state matches this context: its flags predicate is never true. So
  nothing can jump here, and the `ud2` is never executed. -/
  | trap : At .trap ⟨fun _ => .int, [], 0, fun _ => False⟩
  | compute (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    computeSig.CallerOk saved ret rest room → At .compute (computeSig.entry saved ret rest room)

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
    -- lea rax, [rip + compute]
    ty_step
    -- `rax` holds exactly the address of `compute`, so it is a pointer to that function
    ty_code_ptr .rax to computeCtx
    -- the pointer is stored in a stack slot and called through it
    ty_steps
    ty_call computeSig
  | afterCall =>
    ty_steps
    -- `rcx` holds exactly the address of `finish`
    ty_code_ptr .rcx to fin
    ty_block
  | finish => ty_block
  | spin => ty_block
  | trap => ty_block
  | compute saved ret rest room hK =>
    -- make the two slots the signature guarantees visible, so the frame can be allocated
    obtain ⟨m, rfl⟩ := hK.room_split
    ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, the record readable and writable, and four writable stack slots below `rsp` that
do not overlap it. This is the contract with whatever loads the program;
for the ELF file, with the Linux kernel. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image blocks 4

/-- Any state meeting the entry contract is well typed. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s :=
  ⟨entryCtx 4, by rw [h.rip]; exact .intro At.start,
    fun _ => h.matches HasTy.int (by simp [blocks, recordLayout])⟩

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck,
never faults: no page fault, no invalid opcode and no divide error. The two
divisions are by constants that are not zero, which is what the typing of a
divide demands. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk (linuxOk fetch Ψ) h.stateOk)

theorem image_length : image.length = 198 := by decide +kernel

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

end Ops
