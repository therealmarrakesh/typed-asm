import TypedAsm.U.Writes
import TypedAsm.Image
import TypedAsm.Segments
import TypedAsm.U.Loader

/-!
# A program as written, for the checker

A program is written as lines: instructions, labels, data. Assembled at an
address it has a table of its instructions, each with its address and
length, which is what the machine that looks instructions up fetches from.
Here that table is what the checker is given; and that each of its entries
is what the machine fetches at its address is decided by looking each up.
-/

namespace TypedAsm.U

open TypedAsm

/-- An instruction table, its addresses as machine words. -/
def progCode (table : List (Nat × Instr × BitVec 64)) : List (BitVec 64 × Instr × BitVec 64) :=
  table.map fun e => (BitVec.ofNat 64 e.1, e.2.1, e.2.2)

/-- Whether each entry of a table is an address a machine word holds, and is
what looking its address up in the table gives. -/
def tableOk (table : List (Nat × Instr × BitVec 64)) : Bool :=
  table.all fun e =>
    decide (e.1 < 18446744073709551616) && (Lookup.first table e.1 == some (e.2.1, e.2.2))

/-- **Where it is, the machine that looks instructions up in the assembled
program fetches each entry at its address.** -/
theorem hcode_of_tableOk {L : Type} [DecidableEq L] {base : BitVec 64} {prog : List (Asm L)}
    (h : tableOk (Asm.table base prog) = true) :
    ∀ e ∈ progCode (Asm.table base prog), Asm.fetch base prog e.1 = some (e.2.1, e.2.2) := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  have := List.all_eq_true.mp h x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  show Lookup.first (Asm.table base prog) (BitVec.ofNat 64 x.1).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this.1]
  exact this.2

/-! ## The memory a loaded program has -/

/-- The stretches of pages given a permission as segments are placed in
turn, after those given before. -/
def segStretches (segs : List (Nat × Perm × List Byte)) (rs : List (BitVec 64 × BitVec 64)) :
    List (BitVec 64 × BitVec 64) :=
  segs.foldl (fun rs g => (BitVec.ofNat 64 g.1, BitVec.ofNat 64 g.2.2.length) :: rs) rs

/-- **Placing segments gives memory only on their pages.** -/
theorem PermsWithin.loadSegs : (segs : List (Nat × Perm × List Byte)) → {s : State} →
    {rs : List (BitVec 64 × BitVec 64)} → PermsWithin s rs →
    PermsWithin (s.loadSegs segs) (segStretches segs rs)
  | [], _, _, h => h
  | g :: segs, s, _, h =>
    PermsWithin.loadSegs segs (s := s.loadData (BitVec.ofNat 64 g.1) g.2.2 g.2.1)
      ((h.setPerm (BitVec.ofNat 64 g.1) (BitVec.ofNat 64 g.2.2.length) g.2.1).congr rfl)

end TypedAsm.U
