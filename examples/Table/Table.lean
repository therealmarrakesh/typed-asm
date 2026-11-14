import TableProgram
import TypedAsm.Tactic

/-!
# Table: typing and safety

The program is in `TableProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Table

/-! ## The typing -/

/-- A pointer to a writable record of two integers. -/
def pair : Ty := .ptr [.int, .int] true 0

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- The table: one field, a pointer to the record. -/
def tableLayout : Layout := ⟨[pair], false, none⟩

def recordLayout : Layout := ⟨[.int, .int], true, none⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, tableLayout), (recordAddr, recordLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, its data in memory, readable, and the record writable. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase dataBytes blocks 0

/-- Any state meeting the entry contract is well typed. The table's entry
is a pointer to the record because the data says so. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s :=
  ⟨entryCtx 0, by rw [h.rip]; exact .intro At.start, fun _ => h.matches HasTy.int (by
    intro x hx i τ hi
    simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · -- the table: its one field holds the address of the record
      match i, hi with
      | 0, hi =>
        cases hi
        have hv : s.load64 (dataBase + BitVec.ofNat 64 (8 * 0)) = recordAddr := by
          rw [h.data.load64 (i := 8 * 0) (by decide)]
          decide
        rw [hv]
        exact hasTy_ptr.mpr ⟨recordAddr, recordLayout, rfl, rfl, fun _ => rfl, by decide⟩
      | i + 1, hi => simp [tableLayout] at hi
    · -- the record: both fields are integers
      have hτ : τ = .int := by
        have := List.mem_of_getElem? hi
        simpa [recordLayout] using this
      rw [hτ]
      exact HasTy.int _)⟩

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck
and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk h.stateOk)

theorem image_length : image.length = 20 := by decide

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start :=
  Entry.ofLoad (by rw [image_length]; decide) (by decide)
    ((State.hasData_loadData _ _ _ _ (by decide)).congr rfl) (by rw [image_length]; decide)
    (by decide) (by decide) (by decide)
    (by simp only [image_length]; decide) (by rw [image_length]; decide)

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

end Table
