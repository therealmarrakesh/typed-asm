import TypedAsm.U.Mem
import TypedAsm.Ranges

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
    complete := fun x hx => by
      rcases h.complete x (by rw [← hperm]; exact hx) with ⟨c, hc, hlt⟩ | hr
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc
        refine .inl ⟨(Γ.held.set k (a, S'))[m]'(hlen ▸ hm), List.getElem_mem _, ?_⟩
        rw [(hkey m hm).1, (hkey m hm).2]
        exact hlt
      · exact .inr hr
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
  split <;> simp only [State.store64, State.store32, State.store16, State.regs_store8]

theorem storeN_perm (s : State) (n : Nat) (a v : BitVec 64) : (storeN s n a v).perm = s.perm := by
  unfold storeN
  split <;> simp only [State.store64, State.store32, State.store16, State.store8, State.perm]

theorem mem_store8_ne (s : State) {a x : BitVec 64} (v : BitVec 8) (h : x ≠ a) :
    (s.store8 a v).mem x = s.mem x := by
  rw [State.mem_store8]
  simp only [h, ↓reduceIte]

theorem mem_store16_out (s : State) (a x : BitVec 64) (v : BitVec 16) (h : 2 ≤ x - a) :
    (s.store16 a v).mem x = s.mem x := by
  unfold State.store16
  rw [mem_store8_ne _ _ (by bv_omega), mem_store8_ne _ _ (by bv_omega)]

theorem mem_store32_out (s : State) (a x : BitVec 64) (v : BitVec 32) (h : 4 ≤ x - a) :
    (s.store32 a v).mem x = s.mem x := by
  unfold State.store32
  rw [mem_store16_out _ _ _ _ (by bv_omega), mem_store16_out _ _ _ _ (by bv_omega)]

theorem mem_store64_out (s : State) (a x : BitVec 64) (v : BitVec 64) (h : 8 ≤ x - a) :
    (s.store64 a v).mem x = s.mem x := by
  unfold State.store64
  rw [mem_store32_out _ _ _ _ (by bv_omega), mem_store32_out _ _ _ _ (by bv_omega)]

/-- A store changes no byte outside the bytes it is of. -/
theorem storeN_mem_out (s : State) (n : Nat) (a v x : BitVec 64) (hn : n ≤ 8)
    (h : BitVec.ofNat 64 n ≤ x - a) : (storeN s n a v).mem x = s.mem x := by
  unfold storeN
  split
  · exact mem_store8_ne s _ (by bv_omega)
  · exact mem_store16_out s a x _ h
  · exact mem_store32_out s a x _ h
  · exact mem_store64_out s a x _ h
  · rfl

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

/-- **A context provides the bytes of a region it holds, to be read**: they
are the value the region holds there, if it holds one at those eight bytes. -/
theorem Reads.held {Γ : Ctx} {k : Nat} {b : BitVec 64} {S : Held} {o n : Nat}
    (hk : Γ.held[k]? = some (b, S)) (hin : o + n ≤ S.size) :
    Reads fetch sys Ψ Γ (b + BitVec.ofNat 64 o) n
      (fun x Γr => Γr = Γ ∧ (n = 8 → ∀ w, (o, w) ∈ S.vals → x = w)) := by
  intro j Ψ' he hwf s hw
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hmem : (b, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  refine ⟨State.canRead_of_canWrite (State.canWrite_sub (n := S.size) (hw.held.perm (b, S) hmem) hin),
    Γ, ⟨rfl, ?_⟩, rfl, rfl, hw⟩
  intro h8 w hwv
  subst h8
  exact hw.held.vals _ hmem (o, w) hwv

/-- **And to be written**: the region then holds what was written. -/
theorem Writes.held {Γ : Ctx} {k : Nat} {b : BitVec 64} {S : Held} {o n : Nat} (v : BitVec 64)
    (hk : Γ.held[k]? = some (b, S)) (hin : o + n ≤ S.size) (hn : n ≤ 8) :
    Writes fetch sys Ψ Γ (b + BitVec.ofNat 64 o) n v
      { Γ with held := Γ.held.set k (b, heldPut S o n v) } := by
  refine ⟨rfl, rfl, fun j Ψ' he hwf s hw => ?_⟩
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hmem : (b, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  refine ⟨State.canWrite_sub (n := S.size) (hw.held.perm (b, S) hmem) hin, ?_⟩
  refine hw.writeHeld (S' := heldPut S o n v) (lo := o) (cnt := n) hwf hk hin ?_ ?_
    (storeN_regs _ _ _ _) (storeN_flags _ _ _ _)
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

/-- **And to be written, the region then described anew**: by any values
that were there and keep clear of the bytes written, and the value written
where it is eight bytes. So of a region whose values are found to keep
clear by what is known, which may be fewer than those that do. -/
theorem Writes.heldTo {Γ : Ctx} {k : Nat} {b : BitVec 64} {S S' : Held} {o n : Nat} (v : BitVec 64)
    (hk : Γ.held[k]? = some (b, S)) (hin : o + n ≤ S.size) (hn : n ≤ 8) (hS' : S'.size = S.size)
    (hvals : ∀ p ∈ S'.vals, (p ∈ S.vals ∧ (p.1 + 8 ≤ o ∨ o + n ≤ p.1)) ∨ (n = 8 ∧ p = (o, v))) :
    Writes fetch sys Ψ Γ (b + BitVec.ofNat 64 o) n v
      { Γ with held := Γ.held.set k (b, S') } := by
  refine ⟨rfl, rfl, fun j Ψ' he hwf s hw => ?_⟩
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hmem : (b, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  refine ⟨State.canWrite_sub (n := S.size) (hw.held.perm (b, S) hmem) hin, ?_⟩
  refine hw.writeHeld (S' := S') (lo := o) (cnt := n) hwf hk hin hS' ?_
    (storeN_regs _ _ _ _) (storeN_flags _ _ _ _)
    (storeN_perm _ _ _ _) (fun y hy => storeN_load64_out _ _ _ _ _ hn hy)
    (fun x hx => storeN_mem_out _ _ _ _ _ hn hx) ?_
  · intro p hp
    rw [hS']
    rcases hvals p hp with ⟨hp', _⟩ | ⟨h8, rfl⟩
    · exact hw.held.fits _ hmem p hp'
    · show o + 8 ≤ S.size; omega
  · intro p hp
    rcases hvals p hp with hp' | ⟨h8, rfl⟩
    · exact .inl hp'
    · subst h8
      exact .inr (TypedAsm.State.load64_store64_same _ _ _)

/-- **And to be written somewhere within a stretch of the region**: the
region then holds no value the stretch reaches into. So of a write at an
address known only to lie so far in, give or take. -/
theorem Writes.heldIn {Γ : Ctx} {k : Nat} {b : BitVec 64} {S : Held} {o o' L n : Nat}
    (v : BitVec 64) (hk : Γ.held[k]? = some (b, S)) (ho : o ≤ o') (hfit : o' + n ≤ o + L)
    (hL : o + L ≤ S.size) (hn : n ≤ 8) :
    Writes fetch sys Ψ Γ (b + BitVec.ofNat 64 o') n v
      { Γ with held := Γ.held.set k (b, S.clear o L) } := by
  refine ⟨rfl, rfl, fun j Ψ' he hwf s hw => ?_⟩
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hmem : (b, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hin : o' + n ≤ S.size := by omega
  refine ⟨State.canWrite_sub (n := S.size) (hw.held.perm (b, S) hmem) hin, ?_⟩
  refine hw.writeHeld (S' := S.clear o L) (lo := o') (cnt := n) hwf hk hin rfl ?_
    (storeN_regs _ _ _ _) (storeN_flags _ _ _ _)
    (storeN_perm _ _ _ _) (fun y hy => storeN_load64_out _ _ _ _ _ hn hy)
    (fun x hx => storeN_mem_out _ _ _ _ _ hn hx) ?_
  · intro p hp
    simp only [ShapeOf.clear, List.mem_filter] at hp
    exact hw.held.fits _ hmem p hp.1
  · intro p hp
    simp only [ShapeOf.clear, List.mem_filter, ShapeOf.clearOf, Bool.or_eq_true,
      decide_eq_true_eq] at hp
    exact .inl ⟨hp.1, by omega⟩

end TypedAsm.U
