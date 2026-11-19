import TypedAsm.Shape
import TypedAsm.Bytes

/-!
# Ranges of bytes, and what may be read and written of them

Facts of the machine's memory and its permissions that no type system is
needed to state: ranges apart, parts of ranges that may be read or written,
and what a store leaves as it was.
-/

namespace TypedAsm

/-! ## Ranges of addresses -/

theorem Disjoint.symm {a b : BitVec 64} {n m : Nat} (h : Disjoint a n b m) : Disjoint b m a n :=
  ⟨h.2, h.1⟩

/-- Non-empty sub-ranges of disjoint ranges are disjoint. -/
theorem Disjoint.mono {a b : BitVec 64} {n m o p n' m' : Nat} (h : Disjoint a n b m)
    (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (ho : o + n' ≤ n) (hp : p + m' ≤ m)
    (hn' : 0 < n') (hm' : 0 < m') :
    Disjoint (a + BitVec.ofNat 64 o) n' (b + BitVec.ofNat 64 p) m' := by
  have h' := h.of_pos (by omega) (by omega)
  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega

namespace State

theorem canRead_iff {s : State} {a : BitVec 64} {n : Nat} :
    s.canRead a n = true ↔ ∀ i, i < n → (s.perm (a + BitVec.ofNat 64 i)).readable = true := by
  simp [canRead, List.all_eq_true]

theorem canWrite_iff {s : State} {a : BitVec 64} {n : Nat} :
    s.canWrite a n = true ↔ ∀ i, i < n → (s.perm (a + BitVec.ofNat 64 i)).writable = true := by
  simp [canWrite, List.all_eq_true]

/-- A readable range's sub-ranges are readable. -/
theorem canRead_sub {s : State} {a : BitVec 64} {n o m : Nat} (h : s.canRead a n = true)
    (hle : o + m ≤ n) : s.canRead (a + BitVec.ofNat 64 o) m = true := by
  rw [canRead_iff] at *
  intro i hi
  have := h (o + i) (by omega)
  rwa [BitVec.ofNat_add, ← BitVec.add_assoc] at this

/-- A writable range's sub-ranges are writable. -/
theorem canWrite_sub {s : State} {a : BitVec 64} {n o m : Nat} (h : s.canWrite a n = true)
    (hle : o + m ≤ n) : s.canWrite (a + BitVec.ofNat 64 o) m = true := by
  rw [canWrite_iff] at *
  intro i hi
  have := h (o + i) (by omega)
  rwa [BitVec.ofNat_add, ← BitVec.add_assoc] at this

theorem load64_congr {s t : State} (h : t.mem = s.mem) (a : BitVec 64) :
    t.load64 a = s.load64 a := by
  simp only [load64, load32, load16, load8, h]

theorem canRead_congr {s t : State} (h : t.perm = s.perm) (a : BitVec 64) (n : Nat) :
    t.canRead a n = s.canRead a n := by
  simp only [canRead, h]

theorem canWrite_congr {s t : State} (h : t.perm = s.perm) (a : BitVec 64) (n : Nat) :
    t.canWrite a n = s.canWrite a n := by
  simp only [canWrite, h]

theorem store64_regs (s : State) (a v : BitVec 64) : (s.store64 a v).regs = s.regs := by
  simp only [store64, store32, store16, regs_store8]

theorem store64_flags (s : State) (a v : BitVec 64) : (s.store64 a v).flags = s.flags := by
  simp only [store64, store32, store16, store8]

theorem store64_perm (s : State) (a v : BitVec 64) : (s.store64 a v).perm = s.perm :=
  State.perm_store s .w64 a v

theorem store64_rip (s : State) (a v : BitVec 64) : (s.store64 a v).rip = s.rip := by
  simp only [store64, store32, store16, store8]

theorem load64_store64_same (s : State) (a v : BitVec 64) : (s.store64 a v).load64 a = v :=
  load_store_same s .w64 a v

theorem load64_store64_disjoint (s : State) {a b : BitVec 64} (v : BitVec 64)
    (h : Disjoint a 8 b 8) : (s.store64 a v).load64 b = s.load64 b :=
  load_store_disjoint s .w64 .w64 a b v (h.1 (by decide)) (h.2 (by decide))

end State

/-- Within one region, a run of bytes does not overlap eight bytes that keep
clear of it. -/
theorem WellTyped.disjoint_bytes {a : BitVec 64} {lo cnt p N : Nat} (hc : 0 < cnt)
    (hout : p + 8 ≤ lo ∨ lo + cnt ≤ p) (hr : lo + cnt ≤ N) (hp : p + 8 ≤ N) (hN : N < 2 ^ 64) :
    Disjoint (a + BitVec.ofNat 64 lo) cnt (a + BitVec.ofNat 64 p) 8 := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega

/-- A range that some block is apart from keeps its permissions across a
change that touches permissions only inside that block. -/
theorem State.canWrite_apart {s s' : State} {a b : BitVec 64} {n m : Nat}
    (hd : Disjoint a n b m) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (hperm : ∀ x, s'.perm x = s.perm x ∨ (x - a).toNat < n)
    (hw : s.canWrite b m = true) : s'.canWrite b m = true := by
  rw [State.canWrite_iff] at hw ⊢
  intro i hi
  rcases hperm (b + BitVec.ofNat 64 i) with he | hin
  · rw [he]; exact hw i hi
  · have hd' := hd.of_pos (by omega) (by omega)
    exact absurd hin (by bv_omega)

theorem State.canRead_apart {s s' : State} {a b : BitVec 64} {n m : Nat}
    (hd : Disjoint a n b m) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (hperm : ∀ x, s'.perm x = s.perm x ∨ (x - a).toNat < n)
    (hr : s.canRead b m = true) : s'.canRead b m = true := by
  rw [State.canRead_iff] at hr ⊢
  intro i hi
  rcases hperm (b + BitVec.ofNat 64 i) with he | hin
  · rw [he]; exact hr i hi
  · have hd' := hd.of_pos (by omega) (by omega)
    exact absurd hin (by bv_omega)

/-- A range apart from each of two that lie end to end is apart from the two
taken as one. -/
theorem Disjoint.union_right {a b : BitVec 64} {n m₁ m₂ : Nat} (h₁ : Disjoint a n b m₁)
    (h₂ : Disjoint a n (b + BitVec.ofNat 64 m₁) m₂) (hm : m₁ + m₂ < 2 ^ 64) :
    Disjoint a n b (m₁ + m₂) := by
  refine ⟨fun _ => ?_, fun hn0 => ?_⟩
  · by_cases h10 : m₁ = 0
    · subst h10
      have := h₂.1 (by omega)
      bv_omega
    · exact h₁.1 h10
  · have a₁ := h₁.2 hn0
    have a₂ := h₂.2 hn0
    bv_omega

/-- A range apart from another is apart from any part of it. -/
theorem Disjoint.sub_right {a b : BitVec 64} {n m p m' : Nat} (h : Disjoint a n b m)
    (hp : p + m' ≤ m) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) :
    Disjoint a n (b + BitVec.ofNat 64 p) m' := by
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨fun _ => by bv_omega, fun h0 => absurd rfl h0⟩
  · by_cases hm0 : m' = 0
    · subst hm0
      exact ⟨fun h0 => absurd rfl h0, fun _ => by bv_omega⟩
    · have h' := h.of_pos hn0 (by omega)
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega

/-- A range apart from another has every beginning of it apart from that other. -/
theorem Disjoint.prefix_left {a b : BitVec 64} {n n' m : Nat} (h : Disjoint a n b m)
    (hle : n' ≤ n) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) : Disjoint a n' b m := by
  have := h.symm.sub_right (p := 0) (m' := n') (by omega) hm hn
  rw [show a + BitVec.ofNat 64 0 = a by simp] at this
  exact this.symm

/-- A part of a range that is apart from another is apart from it. -/
theorem Disjoint.part_left {a b : BitVec 64} {n m o n' : Nat} (h : Disjoint a n b m)
    (ho : o + n' ≤ n) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) :
    Disjoint (a + BitVec.ofNat 64 o) n' b m :=
  (h.symm.sub_right ho hm hn).symm

/-- Parts of two ranges that are apart are apart. -/
theorem Disjoint.parts {a b : BitVec 64} {n m o n' p m' : Nat} (h : Disjoint a n b m)
    (ho : o + n' ≤ n) (hp : p + m' ≤ m) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) :
    Disjoint (a + BitVec.ofNat 64 o) n' (b + BitVec.ofNat 64 p) m' :=
  (h.part_left ho hn hm).sub_right hp (by omega) hm

end TypedAsm
