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
      HasTy fetch sys Ψ n p.2 (s'.load64 (a + BitVec.ofNat 64 p.1)))
    (hrows : ∀ r ∈ Γ.rows, ∀ i, i < r.count.toNat →
      HasTy fetch sys Ψ n r.ty (cellAt s' r.byte (r.addr + BitVec.ofNat 64 (r.stride * i))))
    (hfed : ∀ r ∈ Γ.rows, ∀ off, r.fed = some off → FedRow s' r off) :
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
    rows := hrows
    fed := hfed
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

/-- What is said of rows may be anything that is so of memory as it is. -/
theorem setRows (h : WellTyped fetch sys Ψ n Γ s) (R : List (RowOf Ty))
    (hR : ∀ r ∈ R, ∀ i, i < r.count.toNat →
      HasTy fetch sys Ψ n r.ty (cellAt s r.byte (r.addr + BitVec.ofNat 64 (r.stride * i))))
    (hF : ∀ r ∈ R, ∀ off, r.fed = some off → FedRow s r off) :
    WellTyped fetch sys Ψ n { Γ with rows := R } s :=
  { val := h.val
    known := h.known
    flags := h.flags
    heapPerm := h.heapPerm
    heap := h.heap
    text := h.text
    said := h.said
    rows := hR
    fed := hF
    complete := h.complete
    held :=
      { perm := h.held.perm
        size_lt := h.held.size_lt
        fits := h.held.fits
        vals := h.held.vals
        heap := h.held.heap
        apart := h.held.apart } }

/-- What is said of rows may be let go. -/
theorem dropRows (h : WellTyped fetch sys Ψ n Γ s) :
    WellTyped fetch sys Ψ n { Γ with rows := [] } s :=
  h.setRows [] (fun _ hr => nomatch hr) (fun _ hr => nomatch hr)

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
    rows := h.rows
    fed := h.fed
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

/-- **A context provides a value of a row of values a pointer is known to
be the address of, to be read**: the one so many along, where that is fewer
than there are; and what is read is known to be of the type the row's
values are. -/
theorem Reads.arr {Γ : Ctx} {p a c : BitVec 64} {τ : Ty} {st i : Nat}
    (hf : (p, Ty.arr c τ st) ∈ Γ.known) (ha : a = p + BitVec.ofNat 64 (st * i)) (hi : i < c.toNat) :
    Reads fetch sys Ψ Γ a 8 (fun x Γr => Γr = { Γ with known := (x, τ) :: Γ.known }) := by
  intro j Ψ' he hwf s hw
  obtain ⟨base, l, off, hl, hp, hall⟩ := hasTy_arr.mp (hw.known _ hf)
  have hmem := hall i hi
  have hfit := hwf.fits base l hl _ hmem
  have hp' : p = base + BitVec.ofNat 64 off := hp
  have hab : a = base + BitVec.ofNat 64 (off + st * i) := by
    rw [ha, hp', BitVec.add_assoc, ← BitVec.ofNat_add]
  subst hab
  have hsub : off + st * i + 8 ≤ l.size := by
    simp only [Layout.size]
    omega
  refine ⟨State.canRead_sub (hw.heapPerm base l hl).1 hsub, _, rfl, rfl, rfl, ?_⟩
  refine hw.addKnown [(_, τ)] (fun f hf' => ?_)
  rw [List.mem_singleton.mp hf']
  exact hw.heap base l hl _ hmem

/-- **What is read where a row has a value is of the row's type**: the bytes
being provided to be read, whatever provides them. -/
theorem Reads.row {Γ : Ctx} {a : BitVec 64} {n : Nat} {P : BitVec 64 → Ctx → Prop}
    (h : Reads fetch sys Ψ Γ a n P) {r : RowOf Ty} (hr : r ∈ Γ.rows) {i : Nat}
    (hi : i < r.count.toNat) (ha : a = r.addr + BitVec.ofNat 64 (r.stride * i))
    (hn : n = if r.byte then 1 else 8) :
    Reads fetch sys Ψ Γ a n
      (fun x Γr => ∃ Γ0, P x Γ0 ∧ Γr = { Γ0 with known := (x, r.ty) :: Γ0.known }) := by
  intro k Ψ' he hwf s hw
  obtain ⟨hc, Γ0, hP, hv, hf, hw0⟩ := h k Ψ' he hwf s hw
  refine ⟨hc, _, ⟨Γ0, hP, rfl⟩, hv, hf, hw0.addKnown [(_, r.ty)] (fun f hf' => ?_)⟩
  rw [List.mem_singleton.mp hf']
  have hrow := hw.rows r hr i hi
  rw [← ha] at hrow
  subst hn
  cases hb : r.byte <;> rw [hb] at hrow <;> exact hrow

/-- **And to be written**, if the pointer may be written through and each
typed value of the block either keeps clear of the bytes or is the eight
bytes written, with a value that is of its type whenever what the context
knows is so. The context is as it was: the block still holds what its type
says. -/
theorem Writes.shared {Γ : Ctx} {p a : BitVec 64} {τ : Ty} {Sh : Shape} {off o n : Nat}
    (v : BitVec 64)
    (hf : (p, τ) ∈ Γ.known) (hτ : τ.pointee Ψ.kinds = some (Sh, true, off))
    (ha : a + BitVec.ofNat 64 off = p + BitVec.ofNat 64 o) (hin : o + n ≤ Sh.size) (hn : n ≤ 8)
    (hv : ∀ q ∈ Sh.vals, (q.1 + 8 ≤ o ∨ o + n ≤ q.1) ∨ q.2 = .any ∨
      (n = 8 ∧ q.1 = o ∧ ∀ (Ψ' : MemTy) (k : Nat),
        (∀ g ∈ Γ.known, HasTy fetch sys Ψ' k g.2 g.1) → HasTy fetch sys Ψ' k q.2 v))
    (hrows : Γ.rows = []) :
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
    (by rw [hrows]; exact fun r hr => nomatch hr)
    (by rw [hrows]; exact fun r hr => nomatch hr)
  rcases hv q hq with hout | hany | ⟨h8, hqo, hcons⟩
  · exact .inl hout
  · exact .inr (by rw [hany]; exact HasTy.any _)
  · subst h8
    rw [hqo]
    exact .inr (by
      rw [show storeN s 8 (base + BitVec.ofNat 64 o) v = s.store64 _ v from rfl,
        TypedAsm.State.load64_store64_same]
      exact hcons Ψ' j hw.known)

theorem storeN_world (s : State) (n : Nat) (a v : BitVec 64) : (storeN s n a v).world = s.world := by
  unfold storeN
  split <;> rfl

/-- **A row is as it says, in a state**: each of its values of its type,
and, where it is said to be bytes of the last `read`, those. -/
def RowHolds (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) (s : State) (r : RowOf Ty) :
    Prop :=
  (∀ i, i < r.count.toNat →
    HasTy fetch sys Ψ n r.ty (cellAt s r.byte (r.addr + BitVec.ofNat 64 (r.stride * i)))) ∧
  ∀ off, r.fed = some off → FedRow s r off

/-- **A store, with what is then so of rows**: the bytes written as a
context that says nothing of rows provides them, and of memory as the store
leaves it, each row said being as it says. -/
theorem Writes.rows {Γ Γw : Ctx} {a v : BitVec 64} {n : Nat} (R : List (RowOf Ty))
    (h : Writes fetch sys Ψ { Γ with rows := [] } a n v Γw)
    (hR : ∀ k, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' k Γ s →
      ∀ r ∈ R, RowHolds fetch sys Ψ' k (storeN s n a v) r) :
    Writes fetch sys Ψ Γ a n v { Γw with rows := R } :=
  ⟨h.1, h.2.1, fun k Ψ' he hwf s hw =>
    ⟨(h.2.2 k Ψ' he hwf s (WellTyped.dropRows hw)).1,
      (h.2.2 k Ψ' he hwf s (WellTyped.dropRows hw)).2.setRows R
        (fun r hr => (hR k Ψ' he hwf s hw r hr).1) (fun r hr => (hR k Ψ' he hwf s hw r hr).2)⟩⟩

/-- **A row's values are as they were after a store in the region the row
is in that keeps clear of it**: the store wholly below the row, or wholly
above. -/
theorem rowKept {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j : Nat} {base : BitVec 64} {S : Held}
    (hj : Γ.held[j]? = some (base, S)) {r : RowOf Ty} (hr : r ∈ Γ.rows) {ow orr n : Nat}
    (hn : n ≤ 8) (hwfit : ow + n ≤ S.size) (hrow : orr + r.stride * r.count.toNat ≤ S.size)
    (hra : r.addr = base + BitVec.ofNat 64 orr) (hwid : (if r.byte then 1 else 8) ≤ r.stride)
    (hclear : orr + r.stride * r.count.toNat ≤ ow ∨ ow + n ≤ orr) (v : BitVec 64) :
    ∀ i, i < r.count.toNat → HasTy fetch sys Ψ' k r.ty
      (cellAt (storeN s n (base + BitVec.ofNat 64 ow) v) r.byte
        (r.addr + BitVec.ofNat 64 (r.stride * i))) := by
  intro i hi
  have hsz : S.size < 2 ^ 64 := hw.held.size_lt (base, S) (List.mem_of_getElem? hj)
  have hstep : r.stride * i + r.stride ≤ r.stride * r.count.toNat := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have hd : Disjoint (base + BitVec.ofNat 64 ow) n (r.addr + BitVec.ofNat 64 (r.stride * i))
      (if r.byte then 1 else 8) := by
    rw [hra]
    have hw8 : (if r.byte then 1 else 8) ≤ 8 := by split <;> omega
    generalize r.stride * i = t at hstep ⊢
    generalize r.stride * r.count.toNat = T at hstep hrow hclear
    generalize (if r.byte = true then 1 else 8) = wd at hwid hw8 ⊢
    generalize r.stride = st at hstep hwid
    refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
  rw [cellAt_storeN_out s n _ v _ r.byte hn hd]
  exact hw.rows r hr i hi

/-- **A store in another region than the one a row is in keeps clear of
each of the row's values**: the regions held are apart. -/
theorem rowElsewhere_apart {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j j' : Nat} {base base' : BitVec 64} {S S' : Held}
    (hj : Γ.held[j]? = some (base, S)) (hj' : Γ.held[j']? = some (base', S')) (hne : j' ≠ j)
    {r : RowOf Ty} {ow orr n : Nat}
    (hwfit : ow + n ≤ S.size) (hrow : orr + r.stride * r.count.toNat ≤ S'.size)
    (hra : r.addr = base' + BitVec.ofNat 64 orr) (hwid : (if r.byte then 1 else 8) ≤ r.stride) :
    ∀ i, i < r.count.toNat →
      Disjoint (base + BitVec.ofNat 64 ow) n (r.addr + BitVec.ofNat 64 (r.stride * i))
        (if r.byte then 1 else 8) := by
  intro i hi
  have hsz : S.size < 2 ^ 64 := hw.held.size_lt (base, S) (List.mem_of_getElem? hj)
  have hsz' : S'.size < 2 ^ 64 := hw.held.size_lt (base', S') (List.mem_of_getElem? hj')
  obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hlt', e'⟩ := List.getElem?_eq_some_iff.mp hj'
  have hp := List.pairwise_iff_getElem.mp hw.held.apart
  have hap : Disjoint base S.size base' S'.size := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := (hp j' j hlt' hlt h).symm
      rw [e, e'] at this
      exact this
    · have := hp j j' hlt hlt' h
      rw [e, e'] at this
      exact this
  have hstep : r.stride * i + r.stride ≤ r.stride * r.count.toNat := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [hra, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hap.parts hwfit (by omega) hsz hsz'

/-- **A row's values are as they were after a store in another region than
the one the row is in.** -/
theorem rowElsewhere {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j j' : Nat} {base base' : BitVec 64} {S S' : Held}
    (hj : Γ.held[j]? = some (base, S)) (hj' : Γ.held[j']? = some (base', S')) (hne : j' ≠ j)
    {r : RowOf Ty} (hr : r ∈ Γ.rows) {ow orr n : Nat}
    (hn : n ≤ 8) (hwfit : ow + n ≤ S.size) (hrow : orr + r.stride * r.count.toNat ≤ S'.size)
    (hra : r.addr = base' + BitVec.ofNat 64 orr) (hwid : (if r.byte then 1 else 8) ≤ r.stride)
    (v : BitVec 64) :
    ∀ i, i < r.count.toNat → HasTy fetch sys Ψ' k r.ty
      (cellAt (storeN s n (base + BitVec.ofNat 64 ow) v) r.byte
        (r.addr + BitVec.ofNat 64 (r.stride * i))) := by
  intro i hi
  rw [cellAt_storeN_out s n _ v _ r.byte hn (rowElsewhere_apart hw hj hj' hne hwfit hrow hra hwid i hi)]
  exact hw.rows r hr i hi

/-- **A store in the region a row is in keeps clear of each of some of the
row's values, one after another**, where it is wholly below them or wholly
above. -/
theorem rowPiece_apart {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j : Nat} {base : BitVec 64} {S : Held}
    (hj : Γ.held[j]? = some (base, S)) {r : RowOf Ty} {ow orr n a m : Nat}
    (hwfit : ow + n ≤ S.size) (hrow : orr + r.stride * r.count.toNat ≤ S.size)
    (hra : r.addr = base + BitVec.ofNat 64 orr) (hwid : (if r.byte then 1 else 8) ≤ r.stride)
    (ham : a + m ≤ r.count.toNat)
    (hclear : orr + r.stride * (a + m) ≤ ow ∨ ow + n ≤ orr + r.stride * a) :
    ∀ i, i < m →
      Disjoint (base + BitVec.ofNat 64 ow) n (r.addr + BitVec.ofNat 64 (r.stride * (a + i)))
        (if r.byte then 1 else 8) := by
  intro i hi
  have hsz : S.size < 2 ^ 64 := hw.held.size_lt (base, S) (List.mem_of_getElem? hj)
  have h1 : r.stride * (a + i) + r.stride ≤ r.stride * (a + m) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have h2 : r.stride * (a + m) ≤ r.stride * r.count.toNat := Nat.mul_le_mul_left _ ham
  have h3 : r.stride * a ≤ r.stride * (a + i) := Nat.mul_le_mul_left _ (by omega)
  rw [hra]
  have hw8 : (if r.byte then 1 else 8) ≤ 8 := by split <;> omega
  generalize r.stride * (a + i) = t at h1 h3 ⊢
  generalize r.stride * (a + m) = T1 at h1 h2 hclear
  generalize r.stride * a = t0 at h3 hclear
  generalize r.stride * r.count.toNat = T at h2 hrow
  generalize (if r.byte = true then 1 else 8) = wd at hwid hw8 ⊢
  generalize r.stride = st at h1 hwid
  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega

/-- **Some of a row's values, one after another, are as they were after a
store in the region the row is in that keeps clear of them**: the store
wholly below them, or wholly above. -/
theorem rowPiece {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j : Nat} {base : BitVec 64} {S : Held}
    (hj : Γ.held[j]? = some (base, S)) {r : RowOf Ty} (hr : r ∈ Γ.rows) {ow orr n a m : Nat}
    (hn : n ≤ 8) (hwfit : ow + n ≤ S.size) (hrow : orr + r.stride * r.count.toNat ≤ S.size)
    (hra : r.addr = base + BitVec.ofNat 64 orr) (hwid : (if r.byte then 1 else 8) ≤ r.stride)
    (ham : a + m ≤ r.count.toNat)
    (hclear : orr + r.stride * (a + m) ≤ ow ∨ ow + n ≤ orr + r.stride * a) (v : BitVec 64) :
    ∀ i, i < m → HasTy fetch sys Ψ' k r.ty
      (cellAt (storeN s n (base + BitVec.ofNat 64 ow) v) r.byte
        (r.addr + BitVec.ofNat 64 (r.stride * (a + i)))) := by
  intro i hi
  rw [cellAt_storeN_out s n _ v _ r.byte hn (rowPiece_apart hw hj hwfit hrow hra hwid ham hclear i hi)]
  exact hw.rows r hr (a + i) (by omega)

/-- **Some of the bytes of a row that is bytes of the last `read`, one
after another, are bytes of it from that much further in after a store in
the region the row is in that keeps clear of them.** -/
theorem fedPiece {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j : Nat} {base : BitVec 64} {S : Held}
    (hj : Γ.held[j]? = some (base, S)) {r : RowOf Ty} (hr : r ∈ Γ.rows) {ow orr n a : Nat}
    (hn : n ≤ 8) (hwfit : ow + n ≤ S.size) (hrow : orr + r.stride * r.count.toNat ≤ S.size)
    (hra : r.addr = base + BitVec.ofNat 64 orr) {r' : RowOf Ty} (hb : r'.byte = r.byte)
    (hst : r'.stride = r.stride) (hA : r'.addr = r.addr + BitVec.ofNat 64 (r.stride * a))
    (ham : a + r'.count.toNat ≤ r.count.toNat)
    (hclear : orr + r.stride * (a + r'.count.toNat) ≤ ow ∨ ow + n ≤ orr + r.stride * a)
    (v : BitVec 64) {off : BitVec 64} (ho : r.fed = some off) :
    FedRow (storeN s n (base + BitVec.ofNat 64 ow) v) r' (off + BitVec.ofNat 64 a) := by
  have hf := hw.fed r hr off ho
  have hby : r.byte = true := hf.1
  have hs1 : r.stride = 1 := hf.2.1
  refine hf.part (congrArg World.reads (storeN_world s n _ v)) hb hst
    (by rw [hA, hs1, Nat.one_mul]) ham fun i hi => ?_
  have hd := rowPiece_apart hw hj hwfit hrow hra (by rw [hby, hs1]; decide) ham hclear i hi
  rw [hs1, Nat.one_mul, hby] at hd
  exact storeN_mem_out s n _ v _ hn (hd.1 (by decide))

/-- **A row that is bytes of the last `read` is so still after a store in
another region than the one the row is in.** -/
theorem fedElsewhere {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j j' : Nat} {base base' : BitVec 64} {S S' : Held}
    (hj : Γ.held[j]? = some (base, S)) (hj' : Γ.held[j']? = some (base', S')) (hne : j' ≠ j)
    {r : RowOf Ty} (hr : r ∈ Γ.rows) {ow orr n : Nat}
    (hn : n ≤ 8) (hwfit : ow + n ≤ S.size) (hrow : orr + r.stride * r.count.toNat ≤ S'.size)
    (hra : r.addr = base' + BitVec.ofNat 64 orr) (v : BitVec 64) {off : BitVec 64}
    (ho : r.fed = some off) :
    FedRow (storeN s n (base + BitVec.ofNat 64 ow) v) r off := by
  have hf := hw.fed r hr off ho
  have hby : r.byte = true := hf.1
  have hs1 : r.stride = 1 := hf.2.1
  have hm : ∀ i, i < r.count.toNat →
      (storeN s n (base + BitVec.ofNat 64 ow) v).mem (r.addr + BitVec.ofNat 64 (0 + i))
        = s.mem (r.addr + BitVec.ofNat 64 (0 + i)) := fun i hi => by
    have hd := rowElsewhere_apart hw hj hj' hne hwfit hrow hra (by rw [hby, hs1]; decide) i hi
    rw [hs1, Nat.one_mul, hby] at hd
    rw [Nat.zero_add]
    exact storeN_mem_out s n _ v _ hn (hd.1 (by decide))
  have := hf.part (r' := r) (a := 0) (congrArg World.reads (storeN_world s n _ v)) rfl rfl
    (by simp) (by omega) hm
  rwa [show off + BitVec.ofNat 64 0 = off by simp] at this

/-- **A row with one value more at its end**, where a store of a value of
its type puts one there. -/
theorem rowAppended {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j : Nat} {base : BitVec 64} {S : Held}
    (hj : Γ.held[j]? = some (base, S)) {r : RowOf Ty} (hr : r ∈ Γ.rows) {ow orr n : Nat}
    (hwfit : ow + n ≤ S.size) (hra : r.addr = base + BitVec.ofNat 64 orr)
    (hwid : (if r.byte then 1 else 8) ≤ r.stride)
    (hat : ow = orr + r.stride * r.count.toNat) (hnw : n = if r.byte then 1 else 8)
    {v : BitVec 64}
    (hv : HasTy fetch sys Ψ' k r.ty (if r.byte then (v.setWidth 8).setWidth 64 else v)) :
    ∀ i, i < (r.count + 1).toNat → HasTy fetch sys Ψ' k r.ty
      (cellAt (storeN s n (base + BitVec.ofNat 64 ow) v) r.byte
        (r.addr + BitVec.ofNat 64 (r.stride * i))) := by
  intro i hi
  have hsz : S.size < 2 ^ 64 := hw.held.size_lt (base, S) (List.mem_of_getElem? hj)
  have hn8 : n ≤ 8 := by rw [hnw]; split <;> omega
  have hpos : 0 < r.stride := by
    have : 0 < (if r.byte then 1 else 8) := by split <;> omega
    omega
  have hcle : r.count.toNat ≤ r.stride * r.count.toNat := Nat.le_mul_of_pos_left _ hpos
  have hc1 : (r.count + 1).toNat = r.count.toNat + 1 := by
    have : n ≠ 0 := by rw [hnw]; split <;> omega
    bv_omega
  rw [hc1] at hi
  by_cases hlt : i < r.count.toNat
  · exact rowKept hw hj hr hn8 hwfit (by omega) hra hwid (.inl (by omega)) v i hlt
  · have hi' : i = r.count.toNat := by omega
    subst hi'
    have ea : r.addr + BitVec.ofNat 64 (r.stride * r.count.toNat) = base + BitVec.ofNat 64 ow := by
      rw [hra, hat, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [ea, hnw, cellAt_storeN_same]
    exact hv

/-- **A row as it was, where a store puts a value of its type in the place
of one of its values.** -/
theorem rowOverwritten {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j : Nat} {base : BitVec 64} {S : Held}
    (hj : Γ.held[j]? = some (base, S)) {r : RowOf Ty} (hr : r ∈ Γ.rows) {ow orr n i0 : Nat}
    (hrow : orr + r.stride * r.count.toNat ≤ S.size)
    (hra : r.addr = base + BitVec.ofNat 64 orr) (hwid : (if r.byte then 1 else 8) ≤ r.stride)
    (hat : base + BitVec.ofNat 64 ow = r.addr + BitVec.ofNat 64 (r.stride * i0))
    (hi0 : i0 < r.count.toNat) (hnw : n = if r.byte then 1 else 8) {v : BitVec 64}
    (hv : HasTy fetch sys Ψ' k r.ty (if r.byte then (v.setWidth 8).setWidth 64 else v)) :
    ∀ i, i < r.count.toNat → HasTy fetch sys Ψ' k r.ty
      (cellAt (storeN s n (base + BitVec.ofNat 64 ow) v) r.byte
        (r.addr + BitVec.ofNat 64 (r.stride * i))) := by
  intro i hi
  have hsz : S.size < 2 ^ 64 := hw.held.size_lt (base, S) (List.mem_of_getElem? hj)
  by_cases he : i = i0
  · subst he
    rw [hat, hnw, cellAt_storeN_same]
    exact hv
  · have hn8 : n ≤ 8 := by rw [hnw]; split <;> omega
    have h1 : r.stride * i + r.stride ≤ r.stride * i0 ∨ r.stride * i0 + r.stride ≤ r.stride * i := by
      rcases Nat.lt_or_gt_of_ne he with h | h
      · exact .inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)
      · exact .inr (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)
    have h2 : r.stride * i + r.stride ≤ r.stride * r.count.toNat := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    have h3 : r.stride * i0 + r.stride ≤ r.stride * r.count.toNat := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi0
    have hd : Disjoint (base + BitVec.ofNat 64 ow) n (r.addr + BitVec.ofNat 64 (r.stride * i))
        (if r.byte then 1 else 8) := by
      rw [hat, hra, hnw, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add,
        ← BitVec.ofNat_add]
      have hw8 : (if r.byte then 1 else 8) ≤ 8 := by split <;> omega
      generalize r.stride * i = t at h1 h2 ⊢
      generalize r.stride * i0 = t0 at h1 h3 ⊢
      generalize r.stride * r.count.toNat = T at h2 h3 hrow
      generalize (if r.byte = true then 1 else 8) = wd at hwid hw8 ⊢
      generalize r.stride = st at h1 h2 h3 hwid
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
    rw [cellAt_storeN_out s n _ v _ r.byte hn8 hd]
    exact hw.rows r hr i hi

/-- **A row with one value more at its start**, where a store of a value of
its type puts one just before it. -/
theorem rowPrepended {Ψ' : MemTy} {k : Nat} {Γ : Ctx} {s : State}
    (hw : WellTyped fetch sys Ψ' k Γ s) {j : Nat} {base : BitVec 64} {S : Held}
    (hj : Γ.held[j]? = some (base, S)) {r : RowOf Ty} (hr : r ∈ Γ.rows) {ow orr n : Nat}
    (hwfit : ow + n ≤ S.size) (hrow : orr + r.stride * r.count.toNat ≤ S.size)
    (hra : r.addr = base + BitVec.ofNat 64 orr)
    (hwid : (if r.byte then 1 else 8) ≤ r.stride)
    (hat : ow + r.stride = orr) (hnw : n = if r.byte then 1 else 8)
    {v : BitVec 64}
    (hv : HasTy fetch sys Ψ' k r.ty (if r.byte then (v.setWidth 8).setWidth 64 else v)) :
    ∀ i, i < (r.count + 1).toNat → HasTy fetch sys Ψ' k r.ty
      (cellAt (storeN s n (base + BitVec.ofNat 64 ow) v) r.byte
        (base + BitVec.ofNat 64 ow + BitVec.ofNat 64 (r.stride * i))) := by
  intro i hi
  have hsz : S.size < 2 ^ 64 := hw.held.size_lt (base, S) (List.mem_of_getElem? hj)
  have hn8 : n ≤ 8 := by rw [hnw]; split <;> omega
  have hpos : 0 < r.stride := by
    have : 0 < (if r.byte then 1 else 8) := by split <;> omega
    omega
  have hcle : r.count.toNat ≤ r.stride * r.count.toNat := Nat.le_mul_of_pos_left _ hpos
  have hc1 : (r.count + 1).toNat = r.count.toNat + 1 := by bv_omega
  rw [hc1] at hi
  cases i with
  | zero =>
    have e0 : base + BitVec.ofNat 64 ow + BitVec.ofNat 64 (r.stride * 0)
        = base + BitVec.ofNat 64 ow := by
      rw [Nat.mul_zero]
      simp
    rw [e0, hnw, cellAt_storeN_same]
    exact hv
  | succ i' =>
    have ea : base + BitVec.ofNat 64 ow + BitVec.ofNat 64 (r.stride * (i' + 1))
        = r.addr + BitVec.ofNat 64 (r.stride * i') := by
      rw [hra, ← hat, Nat.mul_succ, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add,
        ← BitVec.ofNat_add]
      congr 2
      omega
    rw [ea]
    exact rowKept hw hj hr hn8 hwfit hrow hra hwid (.inr (by rw [hnw]; omega)) v i' (by omega)

end TypedAsm.U
