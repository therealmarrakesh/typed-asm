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

/-- Whether a table's addresses go up from each entry to the next, the last
of them one a machine word holds: seen in one pass. -/
def tableUp : List (Nat × Instr × BitVec 64) → Bool
  | [] => true
  | [e] => decide (e.1 < 18446744073709551616)
  | e :: e' :: rest => decide (e.1 < e'.1) && tableUp (e' :: rest)

theorem tableUp_tail {e : Nat × Instr × BitVec 64} :
    {rest : List (Nat × Instr × BitVec 64)} → tableUp (e :: rest) = true → tableUp rest = true
  | [], _ => rfl
  | _ :: _, h => by
    simp only [tableUp, Bool.and_eq_true] at h
    exact h.2

theorem tableUp_lt : {e : Nat × Instr × BitVec 64} → {rest : List (Nat × Instr × BitVec 64)} →
    tableUp (e :: rest) = true → ∀ x ∈ rest, e.1 < x.1
  | _, [], _, x, hx => nomatch hx
  | e, e' :: rest, h, x, hx => by
    simp only [tableUp, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (tableUp_lt h.2 x hx)

theorem tableUp_bound : {t : List (Nat × Instr × BitVec 64)} → tableUp t = true →
    ∀ e ∈ t, e.1 < 18446744073709551616
  | [], _, e, he => nomatch he
  | [e₀], h, e, he => by
    cases List.mem_singleton.mp he
    simpa only [tableUp, decide_eq_true_eq] using h
  | e₀ :: e₁ :: rest, h, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · have h1 := tableUp_lt h e₁ List.mem_cons_self
      have h2 := tableUp_bound (tableUp_tail h) e₁ List.mem_cons_self
      exact Nat.lt_trans h1 h2
    · exact tableUp_bound (tableUp_tail h) e he

theorem tableUp_first : {t : List (Nat × Instr × BitVec 64)} → tableUp t = true →
    ∀ e ∈ t, Lookup.first t e.1 = some (e.2.1, e.2.2)
  | [], _, e, he => nomatch he
  | (a, i, len) :: rest, h, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · simp only [Lookup.first, ↓reduceIte]
    · have hlt := tableUp_lt h e he
      have hne : e.1 ≠ a := Nat.ne_of_gt hlt
      simp only [Lookup.first, hne, ↓reduceIte]
      exact tableUp_first (tableUp_tail h) e he

/-- Whether each entry of a table is an address a machine word holds, and is
what looking its address up in the table gives: as it is where the
addresses go up, which is seen in one pass; or else entry by entry. -/
def tableOk (table : List (Nat × Instr × BitVec 64)) : Bool :=
  tableUp table ||
    table.all fun e =>
      decide (e.1 < 18446744073709551616) && (Lookup.first table e.1 == some (e.2.1, e.2.2))

/-- **Where it is, the machine that looks instructions up in the assembled
program fetches each entry at its address.** -/
theorem hcode_of_tableOk {L : Type} [DecidableEq L] {base : BitVec 64} {prog : List (Asm L)}
    (h : tableOk (Asm.table base prog) = true) :
    ∀ e ∈ progCode (Asm.table base prog), Asm.fetch base prog e.1 = some (e.2.1, e.2.2) := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  have key : x.1 < 18446744073709551616 ∧
      Lookup.first (Asm.table base prog) x.1 = some (x.2.1, x.2.2) := by
    rcases Bool.or_eq_true _ _ |>.mp h with hup | hall
    · exact ⟨tableUp_bound hup x hx, tableUp_first hup x hx⟩
    · have := List.all_eq_true.mp hall x hx
      simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this
  show Lookup.first (Asm.table base prog) (BitVec.ofNat 64 x.1).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt key.1]
  exact key.2

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
