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

end TypedAsm.U
