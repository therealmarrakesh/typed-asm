import SwapProgram
import TypedAsm.Tactic

/-!
# Swap: typing and safety

The program is in `SwapProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Swap

/-! ## The typing -/

/-- A pointer to a writable record of two integers. -/
def pair : Ty := .ptr [.int, .int] true 0

/-- `swap` takes the pointer in `rdi`, promises nothing about the registers
it uses, and preserves the callee-saved registers. -/
def swapSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- Register types with the pointer in one register and nothing known about the rest. -/
def only (reg : Reg) : Reg → Ty := fun r => if r = reg then pair else .int

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 2)
  /-- After the first call the pointer is still in `rbx`. -/
  | afterFirst : At .afterFirst ⟨only .rbx, [], 2, Flags.Any⟩
  | afterSecond : At .afterSecond ⟨only .rbx, [pair], 1, Flags.Any⟩
  | swap (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    swapSig.CallerOk saved ret rest room → At .swap (swapSig.entry saved ret rest room)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

def recordLayout : Layout := ⟨[.int, .int], true⟩

/-- One memory block: the record. -/
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
    ty_call swapSig
  | afterFirst => ty_block; ty_call swapSig
  | afterSecond => ty_block
  | swap saved ret rest room hK => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, the record readable and writable, and two writable stack slots below `rsp` that
do not overlap it. This is the contract with whatever loads the program;
for the ELF file, with the Linux kernel. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image blocks 2

/-- Any state meeting the entry contract is well typed. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s :=
  ⟨entryCtx 2, by rw [h.rip]; exact .intro At.start,
    fun _ => h.matches HasTy.int (by simp [blocks, recordLayout])⟩

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck,
never faults: no page fault, no invalid opcode and no divide error. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk h.stateOk)

theorem image_length : image.length = 49 := by decide

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start :=
  Entry.ofLoad (by rw [image_length]; decide) (by decide) (by decide) (by decide) (by decide)
    (by simp only [image_length]; decide) (by rw [image_length]; decide)

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

/-- It is also safe on the table machine, which is what the type system reasons about. -/
theorem safe : Safe fetch linux start :=
  soundness_blocks blocksOk memOk start_entry.stateOk

end Swap
