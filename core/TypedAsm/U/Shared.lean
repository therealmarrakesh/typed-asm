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
    complete := fun x hx => h.complete x (by rw [← hperm]; exact hx)
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

/-- Facts that are so may be added to what a context knows. -/
theorem addKnown (h : WellTyped fetch sys Ψ n Γ s) (fs : List Fact)
    (hfs : ∀ f ∈ fs, HasTy fetch sys Ψ n f.2 f.1) :
    WellTyped fetch sys Ψ n { Γ with known := fs ++ Γ.known } s :=
  { val := h.val
    known := fun f hf => by
      rcases List.mem_append.mp hf with hf | hf
      · exact hfs f hf
      · exact h.known f hf
    flags := h.flags
    heapPerm := h.heapPerm
    heap := h.heap
    text := h.text
    said := h.said
    complete := h.complete
    held :=
      { perm := h.held.perm
        size_lt := h.held.size_lt
        fits := h.held.fits
        vals := h.held.vals
        heap := h.held.heap
        apart := h.held.apart } }

end WellTyped

/-- What reading the `n` bytes at `o` of a block of a shape tells of the
value read: where they are eight bytes the shape gives a type, the value is
of it. -/
def readFacts (Sh : Shape) (o n : Nat) (x : BitVec 64) : List Fact :=
  if n = 8 then (Sh.vals.filter fun q => q.1 = o).map fun q => (x, q.2) else []

/-- **A context provides the bytes of a block a value is known to point
into, to be read**: what is read is known to be of the type the block gives
those bytes. -/
theorem Reads.shared {Γ : Ctx} {p a : BitVec 64} {τ : Ty} {Sh : Shape} {w : Bool} {off o n : Nat}
    (hf : (p, τ) ∈ Γ.known) (hτ : τ.pointee Ψ.kinds = some (Sh, w, off))
    (ha : a + BitVec.ofNat 64 off = p + BitVec.ofNat 64 o) (hin : o + n ≤ Sh.size) :
    Reads fetch sys Ψ Γ a n
      (fun x Γr => Γr = { Γ with known := readFacts Sh o n x ++ Γ.known }) := by
  intro j Ψ' he hwf s hw
  obtain ⟨base, l, hl, hsh, hlw, hp⟩ :=
    hasTy_pointee hwf (by rw [he.kinds]; exact hτ) (hw.known _ hf)
  subst hsh
  have hab : a = base + BitVec.ofNat 64 o := by bv_omega
  subst hab
  have hsub : o + n ≤ l.size := by simp only [Layout.size]; omega
  refine ⟨State.canRead_sub (hw.heapPerm base l hl).1 hsub, _, rfl, rfl, rfl, ?_⟩
  refine hw.addKnown _ (fun f hf' => ?_)
  unfold readFacts at hf'
  split at hf'
  · next h8 =>
    subst h8
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf'
    simp only [List.mem_filter, decide_eq_true_eq] at hq
    have := hw.heap base l hl q hq.1
    rw [hq.2] at this
    exact this
  · cases hf'

/-- The bytes may be read, with nothing said of what is read: so of a read
at an address known only to lie so far in, give or take. -/
theorem Reads.sharedAt {Γ : Ctx} {p a : BitVec 64} {τ : Ty} {Sh : Shape} {w : Bool} {off o n : Nat}
    (hf : (p, τ) ∈ Γ.known) (hτ : τ.pointee Ψ.kinds = some (Sh, w, off))
    (ha : a + BitVec.ofNat 64 off = p + BitVec.ofNat 64 o) (hin : o + n ≤ Sh.size) :
    Reads fetch sys Ψ Γ a n (fun _ Γr => Γr = Γ) := by
  intro j Ψ' he hwf s hw
  obtain ⟨base, l, hl, hsh, hlw, hp⟩ :=
    hasTy_pointee hwf (by rw [he.kinds]; exact hτ) (hw.known _ hf)
  subst hsh
  have hab : a = base + BitVec.ofNat 64 o := by bv_omega
  subst hab
  have hsub : o + n ≤ l.size := by simp only [Layout.size]; omega
  exact ⟨State.canRead_sub (hw.heapPerm base l hl).1 hsub, _, rfl, rfl, rfl, hw⟩

/-- **And to be written**, if the pointer may be written through and each
typed value of the block either keeps clear of the bytes or is the eight
bytes written, with a value that is of its type whenever what the context
knows is so. The context is as it was: the block still holds what its type
says. -/
theorem Writes.shared {Γ : Ctx} {p a : BitVec 64} {τ : Ty} {Sh : Shape} {off o n : Nat}
    (v : BitVec 64)
    (hf : (p, τ) ∈ Γ.known) (hτ : τ.pointee Ψ.kinds = some (Sh, true, off))
    (ha : a + BitVec.ofNat 64 off = p + BitVec.ofNat 64 o) (hin : o + n ≤ Sh.size) (hn : n ≤ 8)
    (hv : ∀ q ∈ Sh.vals, (q.1 + 8 ≤ o ∨ o + n ≤ q.1) ∨
      (n = 8 ∧ q.1 = o ∧ ∀ (Ψ' : MemTy) (k : Nat),
        (∀ g ∈ Γ.known, HasTy fetch sys Ψ' k g.2 g.1) → HasTy fetch sys Ψ' k q.2 v)) :
    Writes fetch sys Ψ Γ a n v Γ := by
  refine ⟨rfl, rfl, fun j Ψ' he hwf s hw => ?_⟩
  obtain ⟨base, l, hl, hsh, hlw, hp⟩ :=
    hasTy_pointee hwf (by rw [he.kinds]; exact hτ) (hw.known _ hf)
  subst hsh
  have hab : a = base + BitVec.ofNat 64 o := by bv_omega
  subst hab
  have hsub : o + n ≤ l.size := by simp only [Layout.size]; omega
  refine ⟨State.canWrite_sub ((hw.heapPerm base l hl).2 (hlw rfl)) hsub, ?_⟩
  refine hw.writeShared hwf hl (hlw rfl) hin (storeN_regs _ _ _ _)
    (storeN_flags _ _ _ _) (storeN_perm _ _ _ _)
    (fun y hy => storeN_load64_out _ _ _ _ _ hn hy)
    (fun x hx => storeN_mem_out _ _ _ _ _ hn hx) (fun q hq => ?_)
  rcases hv q hq with hout | ⟨h8, hqo, hcons⟩
  · exact .inl hout
  · subst h8
    rw [hqo]
    exact .inr (by
      rw [show storeN s 8 (base + BitVec.ofNat 64 o) v = s.store64 _ v from rfl,
        TypedAsm.State.load64_store64_same]
      exact hcons Ψ' j hw.known)

end TypedAsm.U
