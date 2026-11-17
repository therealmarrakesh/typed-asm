import TypedAsm.U.Start

/-!
# The bytes of a page a program is loaded on

A program's bytes are placed where it puts them, and the pages they are on
are given to it whole. So a page holds the program's bytes where it put
some, and nought everywhere else: what was never written is as it began.
Here that is said without looking at any byte: of the bytes placed, by
where the segments are.
-/

namespace TypedAsm.U

open TypedAsm

/-- The state with no memory holds nought everywhere. -/
theorem mem_init (x : BitVec 64) : State.init.mem x = 0 := by
  show Memory.get _ x = 0
  simp only [State.init, BitVec.ofNat_eq_ofNat, Memory.get, Std.TreeMap.contains_emptyc,
    Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getD_emptyc]

/-- Placing segments changes no byte outside them. -/
theorem mem_loadSegs_out {x : BitVec 64} : (segs : List (Nat × Perm × List Byte)) → (s : State) →
    (∀ g ∈ segs, g.2.2.length < 2 ^ 64 ∧
      BitVec.ofNat 64 g.2.2.length ≤ x - BitVec.ofNat 64 g.1) →
    (s.loadSegs segs).mem x = s.mem x
  | [], _, _ => rfl
  | g :: segs, s, h => by
    show ((s.loadData (BitVec.ofNat 64 g.1) g.2.2 g.2.1).loadSegs segs).mem x = _
    rw [mem_loadSegs_out segs _ fun g' hg' => h g' (List.mem_cons_of_mem _ hg')]
    exact storeBytes_mem_out _ _ _ _ (h g List.mem_cons_self).1 (h g List.mem_cons_self).2

/-- Whether a run of bytes, from an address for so many, keeps clear of
every segment. -/
def segsClear (segs : List (Nat × Perm × List Byte)) (lo n : Nat) : Bool :=
  decide (lo + n ≤ 18446744073709551616) &&
    segs.all fun g =>
      decide (g.1 + g.2.2.length < 18446744073709551616) &&
        decide (g.1 + g.2.2.length ≤ lo ∨ lo + n ≤ g.1)

/-- **Bytes that keep clear of every segment are as they were before the
segments were placed.** -/
theorem mem_loadSegs_clear {segs : List (Nat × Perm × List Byte)} {lo n : Nat}
    (h : segsClear segs lo n = true) (s : State) {k : Nat} (hk : k < n) :
    (s.loadSegs segs).mem (BitVec.ofNat 64 lo + BitVec.ofNat 64 k)
      = s.mem (BitVec.ofNat 64 lo + BitVec.ofNat 64 k) := by
  simp only [segsClear, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlo, hall⟩ := h
  refine mem_loadSegs_out segs s fun g hg => ?_
  obtain ⟨hlt, hcl⟩ := hall g hg
  refine ⟨by omega, ?_⟩
  generalize g.2.2.length = len at hlt hcl ⊢
  generalize g.1 = a at hlt hcl ⊢
  bv_omega

/-- **A page that holds some bytes and then nought holds them all**: the
bytes a block of it says. -/
theorem said_of_data_zeros {s : State} {A : BitVec 64} {bytes : List Byte} {n : Nat}
    (hd : s.HasData A bytes)
    (hz : ∀ k, k < n → s.mem (A + BitVec.ofNat 64 (bytes.length + k)) = 0) :
    ∀ k (hk : k < (bytes ++ List.replicate n (0 : Byte)).length),
      s.mem (A + BitVec.ofNat 64 k) = (bytes ++ List.replicate n (0 : Byte))[k] := by
  intro k hk
  by_cases hlt : k < bytes.length
  · rw [List.getElem_append_left hlt]
    exact hd k hlt
  · rw [List.getElem_append_right (by omega), List.getElem_replicate]
    have hkn : k - bytes.length < n := by
      simp only [List.length_append, List.length_replicate] at hk
      omega
    have := hz (k - bytes.length) hkn
    rwa [show bytes.length + (k - bytes.length) = k by omega] at this

end TypedAsm.U
