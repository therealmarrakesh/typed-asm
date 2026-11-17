import TypedAsm.U.Held

/-!
# Memory others may point into

A change confined to a run of bytes of a block of the memory typing leaves
the state matching, provided each typed value of the block keeps clear of
the run or is as its type says afterwards. And a context provides the bytes
of such a block where it knows a value to point into it.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat} {Γ : Ctx} {s : State}

/-- The last byte of a block's text lies outside any run of bytes of a
block's shape, its own block's or another's. -/
theorem MemTy.WF.text_outside_bytes (hΨ : Ψ.WF) {a b : BitVec 64} {l l' : Layout}
    {lo cnt : Nat} (hl : Ψ a = some l) (hle : lo + cnt ≤ l.shape.size) (hc : 0 < cnt)
    (hl' : Ψ b = some l') (ht : l'.text ≠ 0) :
    BitVec.ofNat 64 cnt ≤
      (b + BitVec.ofNat 64 (l'.size - 1)) - (a + BitVec.ofNat 64 lo) := by
  have hsz := hΨ.size_lt a l hl
  have hsz' := hΨ.size_lt b l' hl'
  by_cases hab : b = a
  · subst hab
    have e : l' = l := Option.some.inj (hl'.symm.trans hl)
    subst e
    simp only [Layout.size] at hsz ⊢
    bv_omega
  · have hpos := hΨ.nonempty b l' hl'
    have hd := (hΨ.disjoint a b l l' hl hl' (Ne.symm hab)).mono (o := lo) (p := l'.size - 1)
      (n' := cnt) (m' := 1) hsz hsz' (by simp only [Layout.size]; omega) (by omega)
      (by omega) (by omega)
    exact hd.1 (by decide)

/-- A block that may be written says nothing of its bytes. -/
theorem MemTy.WF.said_none (hΨ : Ψ.WF) {a : BitVec 64} {l : Layout} (hl : Ψ a = some l)
    (hw : l.writable = true) : l.said = none := by
  cases hs : l.said with
  | none => rfl
  | some bs => have := (hΨ.said a l bs hl hs).1; rw [hw] at this; cases this

/-- A byte of a block that says its bytes lies outside any run of bytes of
a block that says nothing of its own. -/
theorem MemTy.WF.said_outside_bytes (hΨ : Ψ.WF) {a b : BitVec 64} {l l' : Layout}
    {lo cnt : Nat} (hl : Ψ a = some l) (hn : l.said = none) (hle : lo + cnt ≤ l.shape.size)
    (hc : 0 < cnt) (hl' : Ψ b = some l') {bs : List (BitVec 8)} (hs : l'.said = some bs)
    {k : Nat} (hk : k < bs.length) :
    BitVec.ofNat 64 cnt ≤ (b + BitVec.ofNat 64 k) - (a + BitVec.ofNat 64 lo) := by
  have hsz := hΨ.size_lt a l hl
  have hsz' := hΨ.size_lt b l' hl'
  have hlen := (hΨ.said b l' bs hl' hs).2
  have hab : b ≠ a := by
    rintro rfl
    have e : l' = l := Option.some.inj (hl'.symm.trans hl)
    subst e
    rw [hn] at hs; cases hs
  have hd := (hΨ.disjoint a b l l' hl hl' (Ne.symm hab)).mono (o := lo) (p := k)
    (n' := cnt) (m' := 1) hsz hsz' (by simp only [Layout.size]; omega) (by omega)
    (by omega) (by omega)
  exact hd.1 (by decide)

namespace WellTyped

/-- **A change confined to a run of bytes of a block of the memory typing
keeps the state matching**, provided each typed value of the block either
keeps clear of the run or is as its type says afterwards. -/
theorem writeShared {a : BitVec 64} {l : Layout} {lo cnt : Nat} {s' : State}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hl : Ψ a = some l)
    (hwr : l.writable = true) (hle : lo + cnt ≤ l.shape.size)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 lo) cnt y 8 → s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤ x - (a + BitVec.ofNat 64 lo) → s'.mem x = s.mem x)
    (hvals : ∀ p ∈ l.shape.vals, (p.1 + 8 ≤ lo ∨ lo + cnt ≤ p.1) ∨
      HasTy fetch sys Ψ n p.2 (s'.load64 (a + BitVec.ofNat 64 p.1))) :
    WellTyped fetch sys Ψ n Γ s' := by
  have hsz := hΨ.size_lt a l hl
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
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
  exact {
    val := fun r => by rw [hg]; exact h.val r
    known := h.known
    flags := by rw [hflags]; exact h.flags
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' p hp => by
      have hpf := hΨ.fits b l' hl' p hp
      by_cases hab : b = a
      · subst hab
        have e : l' = l := Option.some.inj (hl'.symm.trans hl)
        subst e
        rcases hvals p hp with hout | hnew
        · rw [hF _ (fun hc => TypedAsm.WellTyped.disjoint_bytes (N := l'.size) hc hout
            (by simp only [Layout.size]; omega) (by simp only [Layout.size]; omega) hsz)]
          exact h.heap b l' hl' p hp
        · exact hnew
      · rw [hF _ (fun hc => (hΨ.disjoint a b l l' hl hl' (Ne.symm hab)).mono (o := lo)
          (p := p.1) (n' := cnt) (m' := 8) hsz (hΨ.size_lt b l' hl')
          (by simp only [Layout.size]; omega) (by simp only [Layout.size]; omega) hc (by omega))]
        exact h.heap b l' hl' p hp
    text := fun b l' hl' ht => by
      rw [hM _ (fun hc => hΨ.text_outside_bytes hl hle hc hl' ht)]
      exact h.text b l' hl' ht
    said := fun b l' bs hl' hs k hk => by
      rw [hM _ (fun hc => hΨ.said_outside_bytes hl (hΨ.said_none hl hwr) hle hc hl' hs hk)]
      exact h.said b l' bs hl' hs k hk
    held :=
      { perm := fun c hc => by rw [State.canWrite_congr hperm]; exact h.held.perm c hc
        size_lt := h.held.size_lt
        fits := h.held.fits
        vals := fun c hc p hp => by
          have hpf := h.held.fits c hc p hp
          rw [hF _ (fun hcnt => ((h.held.heap c hc a l hl).symm.mono (o := lo) (p := p.1)
            (n' := cnt) (m' := 8) hsz (h.held.size_lt c hc) (by simp only [Layout.size]; omega)
            hpf hcnt (by omega)))]
          exact h.held.vals c hc p hp
        heap := h.held.heap
        apart := h.held.apart } }

end WellTyped

end TypedAsm.U
