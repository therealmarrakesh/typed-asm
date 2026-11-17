import TypedAsm.U.Stack

/-!
# The permissions of a loaded program's pages

Segments placed on pages of their own leave each page with the permission
of the segment that is on it. This is said without looking at any byte: by
where the segments are.
-/

namespace TypedAsm.U

open TypedAsm

/-- Whether an address is on a page of a stretch. -/
def onPages (a len x : Nat) : Prop :=
  (State.pagesOf a len).1 ≤ x / 4096 ∧ x / 4096 < (State.pagesOf a len).1 + (State.pagesOf a len).2

instance (a len x : Nat) : Decidable (onPages a len x) := by unfold onPages; infer_instance

/-- Whether two segments are on no page in common. -/
def pagesApart2 (g h : Nat × Perm × List Byte) : Bool :=
  decide ((State.pagesOf g.1 g.2.2.length).1 + (State.pagesOf g.1 g.2.2.length).2
      ≤ (State.pagesOf h.1 h.2.2.length).1 ∨
    (State.pagesOf h.1 h.2.2.length).1 + (State.pagesOf h.1 h.2.2.length).2
      ≤ (State.pagesOf g.1 g.2.2.length).1)

/-- Whether no two segments of a list are on a page in common, and each is
of a place and a length a machine word holds. -/
def pagesApart : List (Nat × Perm × List Byte) → Bool
  | [] => true
  | g :: t =>
    decide (g.1 < 18446744073709551616) && decide (g.2.2.length < 18446744073709551616) &&
      t.all (pagesApart2 g) && pagesApart t

theorem pagesApart_bounds : (segs : List (Nat × Perm × List Byte)) → pagesApart segs = true →
    ∀ g ∈ segs, g.1 < 18446744073709551616 ∧ g.2.2.length < 18446744073709551616
  | [], _, g, hg => nomatch hg
  | h :: t, hap, g, hg => by
    simp only [pagesApart, Bool.and_eq_true, decide_eq_true_eq] at hap
    rcases List.mem_cons.mp hg with rfl | hgt
    · exact ⟨hap.1.1.1, hap.1.1.2⟩
    · exact pagesApart_bounds t hap.2 g hgt

/-- Placing segments changes no permission off their pages. -/
theorem perm_loadSegs_out {x : BitVec 64} : (segs : List (Nat × Perm × List Byte)) → (s : State) →
    (∀ g ∈ segs, g.1 < 18446744073709551616 ∧ g.2.2.length < 18446744073709551616 ∧
      ¬ onPages g.1 g.2.2.length x.toNat) →
    (s.loadSegs segs).perm x = s.perm x
  | [], _, _ => rfl
  | g :: segs, s, h => by
    show ((s.loadData (BitVec.ofNat 64 g.1) g.2.2 g.2.1).loadSegs segs).perm x = _
    rw [perm_loadSegs_out segs _ fun g' hg' => h g' (List.mem_cons_of_mem _ hg')]
    obtain ⟨h1, h2, h3⟩ := h g List.mem_cons_self
    show ((s.setPerm (BitVec.ofNat 64 g.1) (BitVec.ofNat 64 g.2.2.length) g.2.1).perm x) = _
    rw [State.perm_setPerm, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2]
    split
    · next hc => exact absurd hc.2 h3
    · rfl

/-- **Each page of a segment placed among segments on pages of their own
has the segment's permission.** -/
theorem perm_loadSegs_in {x : BitVec 64} (hx : x.toNat < addrTop) :
    (segs : List (Nat × Perm × List Byte)) → (s : State) → pagesApart segs = true →
    ∀ g ∈ segs, onPages g.1 g.2.2.length x.toNat → (s.loadSegs segs).perm x = g.2.1
  | [], _, _, g, hg, _ => nomatch hg
  | h :: t, s, hap, g, hg, hin => by
    simp only [pagesApart, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hap
    obtain ⟨⟨⟨h1, h2⟩, hall⟩, hrest⟩ := hap
    show ((s.loadData (BitVec.ofNat 64 h.1) h.2.2 h.2.1).loadSegs t).perm x = _
    rcases List.mem_cons.mp hg with rfl | hgt
    · rw [perm_loadSegs_out t _ fun g' hg' => ?_]
      · show ((s.setPerm (BitVec.ofNat 64 g.1) (BitVec.ofNat 64 g.2.2.length) g.2.1).perm x) = _
        rw [State.perm_setPerm, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
          Nat.mod_eq_of_lt h2]
        split
        · rfl
        · next hc => exact absurd ⟨hx, hin⟩ hc
      · have hg2 := hall g' hg'
        simp only [pagesApart2, decide_eq_true_eq] at hg2
        obtain ⟨hb1, hb2⟩ := pagesApart_bounds t hrest g' hg'
        refine ⟨hb1, hb2, fun hon => ?_⟩
        unfold onPages at hin hon
        omega
    · exact perm_loadSegs_in hx t _ hrest g hgt hin

end TypedAsm.U
