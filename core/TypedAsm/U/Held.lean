import TypedAsm.U.Mem
import TypedAsm.Soundness

/-!
# Memory held alone

A change confined to a run of bytes of a region the context holds leaves the
state matching the context, with the region now holding whatever values are
there: nothing else can be looking at it.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat} {Γ : Ctx} {s : State}

namespace WellTyped

/-- Two different held regions do not overlap. -/
theorem held_apart {m k : Nat} (h : WellTyped fetch sys Ψ n Γ s) (hm : m < Γ.held.length)
    (hk : k < Γ.held.length) (hne : m ≠ k) :
    Disjoint Γ.held[k].1 Γ.held[k].2.size Γ.held[m].1 Γ.held[m].2.size := by
  have hp := List.pairwise_iff_getElem.mp h.held.apart
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact (hp m k hm hk hlt).symm
  · exact hp k m hk hm hgt

/-- **A change confined to a run of bytes of a held region keeps the state
matching**, the region described by any shape of the same size whose values
either were there before and keep clear of the run, or are there now. -/
theorem writeHeld {s' : State} {k : Nat} {a : BitVec 64} {S S' : Held} {lo cnt : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hk : Γ.held[k]? = some (a, S))
    (hle : lo + cnt ≤ S.size) (hS' : S'.size = S.size)
    (hfits : ∀ p ∈ S'.vals, p.1 + 8 ≤ S'.size)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 lo) cnt y 8 → s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤ x - (a + BitVec.ofNat 64 lo) → s'.mem x = s.mem x)
    (hvals : ∀ p ∈ S'.vals, (p ∈ S.vals ∧ (p.1 + 8 ≤ lo ∨ lo + cnt ≤ p.1)) ∨
      s'.load64 (a + BitVec.ofNat 64 p.1) = p.2) :
    WellTyped fetch sys Ψ n { Γ with held := Γ.held.set k (a, S') } s' := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (a, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hsz := h.held.size_lt _ hin
  simp only at hsz
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  -- an empty run touches nothing, so nothing need be shown apart from it
  have hF : ∀ y, (0 < cnt → Disjoint (a + BitVec.ofNat 64 lo) cnt y 8) →
      s'.load64 y = s.load64 y := fun y hy => by
    by_cases hc : 0 < cnt
    · exact hframe y (hy hc)
    · have e : cnt = 0 := by omega
      subst e
      exact hframe y ⟨fun _ => by bv_omega, fun h0 => absurd rfl h0⟩
  have hM : ∀ x, (0 < cnt → BitVec.ofNat 64 cnt ≤ x - (a + BitVec.ofNat 64 lo)) →
      s'.mem x = s.mem x := fun x hx => by
    by_cases hc : 0 < cnt
    · exact hmem x (hx hc)
    · have e : cnt = 0 := by omega
      subst e
      exact hmem x (by bv_omega)
  have hhp := h.held.heap _ hin
  simp only at hhp
  -- an entry of the new list is the old one at its place, but for the shape of this region
  have hlen : (Γ.held.set k (a, S')).length = Γ.held.length := List.length_set
  have hentry : ∀ m (hm : m < Γ.held.length),
      (Γ.held.set k (a, S'))[m]'(hlen ▸ hm) = if k = m then (a, S') else Γ.held[m] :=
    fun m hm => List.getElem_set _
  have hkey : ∀ m (hm : m < Γ.held.length),
      ((Γ.held.set k (a, S'))[m]'(hlen ▸ hm)).1 = Γ.held[m].1 ∧
      ((Γ.held.set k (a, S'))[m]'(hlen ▸ hm)).2.size = Γ.held[m].2.size := by
    intro m hm
    rw [hentry m hm]
    split
    · next e => subst e; rw [hkeq]; exact ⟨rfl, hS'⟩
    · exact ⟨rfl, rfl⟩
  exact {
    val := fun r => by rw [hg]; exact h.val r
    known := h.known
    flags := by rw [hflags]; exact h.flags
    heapPerm := fun b l hl => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l hl
    heap := fun b l hl p hp => by
      have hpf := hΨ.fits _ l hl p hp
      rw [hF _ (fun hc => (hhp b l hl).mono (o := lo) (p := p.1) (n' := cnt) (m' := 8)
        hsz (hΨ.size_lt b l hl) (by omega) (by simp only [Layout.size]; omega) (by omega)
        (by omega))]
      exact h.heap b l hl p hp
    text := fun b l hl ht => by
      have hpos := hΨ.nonempty b l hl
      rw [hM _ (fun hc => ((hhp b l hl).mono (o := lo) (p := l.size - 1) (n' := cnt) (m' := 1)
        hsz (hΨ.size_lt b l hl) (by omega) (by omega) (by omega) (by omega)).1 (by decide))]
      exact h.text b l hl ht
    said := fun b l bs hl hs j hj => by
      have hlen := (hΨ.said b l bs hl hs).2
      rw [hM _ (fun hc => ((hhp b l hl).mono (o := lo) (p := j) (n' := cnt) (m' := 1)
        hsz (hΨ.size_lt b l hl) (by omega) (by omega) (by omega) (by omega)).1 (by decide))]
      exact h.said b l bs hl hs j hj
    held := {
      perm := fun c hc' => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.held.length := hlen ▸ hm
        rw [(hkey m hm').1, (hkey m hm').2, State.canWrite_congr hperm]
        exact h.held.perm _ (List.getElem_mem hm')
      size_lt := fun c hc' => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.held.length := hlen ▸ hm
        rw [(hkey m hm').2]
        exact h.held.size_lt _ (List.getElem_mem hm')
      fits := fun c hc' p hp => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.held.length := hlen ▸ hm
        have he := hentry m hm'
        by_cases hmk : k = m
        · subst hmk
          simp only [↓reduceIte] at he
          rw [he] at hp ⊢
          exact hfits p hp
        · simp only [hmk, ↓reduceIte] at he
          rw [he] at hp ⊢
          exact h.held.fits _ (List.getElem_mem hm') p hp
      vals := fun c hc' p hp => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.held.length := hlen ▸ hm
        by_cases hmk : k = m
        · -- this region: values clear of the run are as before, the others are new
          subst hmk
          have he := hentry k hm'
          simp only [↓reduceIte] at he
          rw [he] at hp ⊢
          simp only at hp ⊢
          rcases hvals p hp with ⟨hold, hout⟩ | hnew
          · have hpf := h.held.fits _ hin p hold
            simp only at hpf
            rw [hF _ (fun hc => TypedAsm.WellTyped.disjoint_bytes hc hout hle hpf hsz)]
            exact h.held.vals _ hin p hold
          · exact hnew
        · -- another region: untouched
          have he := hentry m hm'
          simp only [hmk, ↓reduceIte] at he
          rw [he] at hp ⊢
          have hd := (h.held_apart hm' hklt (Ne.symm hmk))
          rw [hkeq] at hd
          simp only at hd
          have hpf := h.held.fits _ (List.getElem_mem hm') p hp
          rw [hF _ (fun hc => hd.mono (o := lo) (p := p.1) (n' := cnt) (m' := 8) hsz
            (h.held.size_lt _ (List.getElem_mem hm')) (by omega) hpf (by omega) (by omega))]
          exact h.held.vals _ (List.getElem_mem hm') p hp
      heap := fun c hc' b l hl => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.held.length := hlen ▸ hm
        rw [(hkey m hm').1, (hkey m hm').2]
        exact h.held.heap _ (List.getElem_mem hm') b l hl
      apart := by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        have hi' : i < Γ.held.length := hlen ▸ hi
        have hj' : j < Γ.held.length := hlen ▸ hj
        rw [(hkey i hi').1, (hkey i hi').2, (hkey j hj').1, (hkey j hj').2]
        exact List.pairwise_iff_getElem.mp h.held.apart i j hi' hj' hij } }

end WellTyped

/-! ## A store of any width -/

theorem storeN_regs (s : State) (n : Nat) (a v : BitVec 64) : (storeN s n a v).regs = s.regs := by
  unfold storeN
  split <;> rfl

theorem storeN_perm (s : State) (n : Nat) (a v : BitVec 64) : (storeN s n a v).perm = s.perm := by
  unfold storeN
  split <;> rfl

/-- A store changes no byte outside the bytes it is of. -/
theorem storeN_mem_out (s : State) (n : Nat) (a v x : BitVec 64) (hn : n ≤ 8)
    (h : BitVec.ofNat 64 n ≤ x - a) : (storeN s n a v).mem x = s.mem x := by
  unfold storeN
  split <;>
    simp only [State.store64, State.store32, State.store16, State.mem_store8] at * <;>
    (repeat' split) <;> first | rfl | bv_omega

/-- Nor any eight bytes apart from them. -/
theorem storeN_load64_out (s : State) (n : Nat) (a v y : BitVec 64) (hn : n ≤ 8)
    (h : Disjoint a n y 8) : (storeN s n a v).load64 y = s.load64 y := by
  by_cases h0 : n = 0
  · subst h0; rfl
  · have hd := h.of_pos h0 (by decide)
    refine State.load64_congr_bytes fun j hj => storeN_mem_out s n a v _ hn ?_
    bv_omega

/-! ## Access to bytes of a held region -/

/-- What a held region holds once `n` of its bytes, from `o`, are given the
value `v`: that value there if they are eight, and plain bytes otherwise;
whatever reached into them is gone. -/
def heldPut (S : Held) (o n : Nat) (v : BitVec 64) : Held :=
  if n = 8 then S.set o v else S.clear o n

/-- **A context provides the bytes of a region it holds.** They may be read
and written. Read, they are the value the region holds there, if it holds
one at those eight bytes; written, the region holds what was written. -/
theorem Access.held {Γ : Ctx} {k : Nat} {b : BitVec 64} {S : Held} {o n : Nat} (rd wr : Bool)
    (hk : Γ.held[k]? = some (b, S)) (hin : o + n ≤ S.size) (hn : n ≤ 8) :
    Access fetch sys Ψ Γ (b + BitVec.ofNat 64 o) n rd wr (fun _ => True)
      (fun x v Γ₁ => (n = 8 → ∀ w, (o, w) ∈ S.vals → x = w) ∧
        Γ₁ = if wr then { Γ with held := Γ.held.set k (b, heldPut S o n v) } else Γ) := by
  intro j Ψ' he hwf s hw
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hmem : (b, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hcw : s.canWrite (b + BitVec.ofNat 64 o) n = true :=
    State.canWrite_sub (hw.held.perm _ hmem) hin
  refine ⟨fun _ => State.canRead_of_canWrite hcw, fun _ => hcw, fun v _ => ?_⟩
  have hx : n = 8 → ∀ w, (o, w) ∈ S.vals → loadN s n (b + BitVec.ofNat 64 o) = w := by
    intro h8 w hwv
    subst h8
    exact hw.held.vals _ hmem (o, w) hwv
  cases wr with
  | false => exact ⟨Γ, ⟨hx, rfl⟩, rfl, rfl, hw⟩
  | true =>
    refine ⟨_, ⟨hx, rfl⟩, rfl, rfl, ?_⟩
    show WellTyped fetch sys Ψ' j { Γ with held := Γ.held.set k (b, heldPut S o n v) }
      (storeN s n (b + BitVec.ofNat 64 o) v)
    refine hw.writeHeld hwf hk hin ?_ ?_ (storeN_regs _ _ _ _) (storeN_flags _ _ _ _)
      (storeN_perm _ _ _ _) (fun y hy => storeN_load64_out _ _ _ _ _ hn hy)
      (fun x hx => storeN_mem_out _ _ _ _ _ hn hx) ?_
    · unfold heldPut; split <;> rfl
    · intro p hp
      have hsize : (heldPut S o n v).size = S.size := by unfold heldPut; split <;> rfl
      rw [hsize]
      unfold heldPut at hp
      split at hp
      · next h8 =>
        simp only [ShapeOf.set, ShapeOf.clear, List.mem_cons, List.mem_filter] at hp
        rcases hp with rfl | hp
        · show o + 8 ≤ S.size; omega
        · exact hw.held.fits _ hmem p hp.1
      · simp only [ShapeOf.clear, List.mem_filter] at hp
        exact hw.held.fits _ hmem p hp.1
    · intro p hp
      unfold heldPut at hp
      split at hp
      · next h8 =>
        subst h8
        simp only [ShapeOf.set, ShapeOf.clear, List.mem_cons, List.mem_filter] at hp
        rcases hp with rfl | hp
        · exact .inr (TypedAsm.State.load64_store64_same _ _ _)
        · exact .inl ⟨hp.1, by simpa [ShapeOf.clearOf] using hp.2⟩
      · simp only [ShapeOf.clear, List.mem_filter] at hp
        exact .inl ⟨hp.1, by simpa [ShapeOf.clearOf] using hp.2⟩

end TypedAsm.U
