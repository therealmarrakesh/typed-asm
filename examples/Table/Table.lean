import TableProgram
import TypedAsm.Tactic

/-!
# Table: typing and safety

The program is in `TableProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Table

-- Where the data is loaded: the table first, then the record.
asm_label dataBase .table
-- Where the record is.
asm_label recordAddr .record

/-! ## The typing -/

/-- A pointer to a writable record of sixteen plain bytes: two numbers. -/
def pair : Ty := .ptr (.raw 16) true 0

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

/-- The table: eight bytes, holding a pointer to the record. -/
def tableLayout : Layout := ⟨⟨8, [(0, pair)]⟩, false, none, 0⟩

def recordLayout : Layout := ⟨.raw 16, true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, tableLayout), (recordAddr, recordLayout)]

asm_typing At blocks blocks room 0

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program

/-! ## The memory typing and the entry contract -/

/-- The data has the types the blocks claim. The table's entry is a pointer
to the record because the data says so. -/
theorem Entry.valuesOk {s : State} (h : Entry s) (n : Nat) :
    ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy fetch linux Ψ n p.2 (s.load64 (x.1 + BitVec.ofNat 64 p.1)) := by
  intro x hx p hp
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · -- the table: its eight bytes hold the address of the record
    simp only [tableLayout, List.mem_singleton] at hp
    subst hp
    have hv : s.load64 (dataBase + BitVec.ofNat 64 0) = recordAddr := by
      rw [(h.hasData (a := dataBase) (bytes := dataBytes) (by decide +kernel)).load64 (i := 0)
        (by decide)]
      decide
    rw [hv]
    exact hasTy_ptr.mpr ⟨recordAddr, recordLayout, rfl, rfl, fun _ => rfl, by decide⟩
  · -- the record is plain bytes
    simp [recordLayout] at hp

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck
and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start h.valuesOk

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

end Table

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Table.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Table.safeMem
