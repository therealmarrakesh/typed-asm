import TypedAsm.Program
import TypedAsm.Linux

/-!
# Memory a program owns

A block of memory the context owns is one nothing else knows of. So it may
be stored to freely, each field taking the type of what is stored; it may be
given back to the kernel; and when it holds what some layout asks, it may be
frozen: handed to the memory typing as an ordinary block, to be pointed at
and shared from then on. Freezing is how a block whose fields cannot start
as zero, such as one holding a pointer that is never null, comes to exist.
-/

namespace TypedAsm

variable {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- The memory typing with one more block. -/
def MemTy.add (Ψ : MemTy) (a : BitVec 64) (L : Layout) : MemTy :=
  ⟨fun x => if x = a then some L else Ψ x, Ψ.kinds⟩

namespace MemTy

variable {a : BitVec 64} {L : Layout}

theorem add_self : (Ψ.add a L) a = some L := by
  show (if a = a then some L else Ψ a) = some L
  simp only [↓reduceIte]

theorem add_cases {x : BitVec 64} {l : Layout} (h : (Ψ.add a L) x = some l) :
    (x = a ∧ l = L) ∨ (x ≠ a ∧ Ψ x = some l) := by
  change (if x = a then some L else Ψ x) = some l at h
  split at h
  · next hx => exact .inl ⟨hx, (Option.some.inj h).symm⟩
  · next hx => exact .inr ⟨hx, h⟩

theorem add_ext (hN : Ψ a = none) : Ψ.Ext (Ψ.add a L) :=
  ⟨fun x l hl => by
    have hx : x ≠ a := fun e => by rw [e, hN] at hl; cases hl
    show (if x = a then some L else Ψ x) = some l
    simp only [hx, ↓reduceIte]
    exact hl, rfl⟩

theorem add_wf (hΨ : Ψ.WF) (hpos : 0 < L.size) (hlt : L.size < 2 ^ 64)
    (hdis : ∀ b lb, Ψ b = some lb → Disjoint a L.size b lb.size)
    (hin : ∀ p ∈ L.shape.vals, p.1 + 8 ≤ L.shape.size)
    (hkind : ∀ t, L.tag = some t → Ψ.kinds t = some L.shape) : (Ψ.add a L).WF := by
  constructor
  · intro x l hl
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · exact hlt
    · exact hΨ.size_lt x l hl'
  · intro x y lx ly hx hy hxy
    rcases add_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx'⟩
    · rcases add_cases hy with ⟨rfl, -⟩ | ⟨-, hy'⟩
      · exact absurd rfl hxy
      · exact hdis y ly hy'
    · rcases add_cases hy with ⟨rfl, rfl⟩ | ⟨-, hy'⟩
      · exact (hdis x lx hx').symm
      · exact hΨ.disjoint x y lx ly hx' hy' hxy
  · intro x l hl
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · exact hpos
    · exact hΨ.nonempty x l hl'
  · intro x l hl p hp
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · exact hin p hp
    · exact hΨ.fits x l hl' p hp
  · intro x l hl t ht
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · exact hkind t ht
    · exact hΨ.kinds x l hl' t ht

end MemTy

variable {n : Nat} {Γ : Ctx} {s : State}

/-- A block that is there, holds what its layout says and overlaps nothing
the context describes may join the memory typing. -/
theorem WellTyped.addBlock {a : BitVec 64} {L : Layout} (h : WellTyped fetch sys Ψ n Γ s)
    (hN : Ψ a = none)
    (hperm : s.canRead a L.size = true ∧ (L.writable = true → s.canWrite a L.size = true))
    (hvals : ∀ p ∈ L.shape.vals,
      HasTy fetch sys Ψ n p.2 (s.load64 (a + BitVec.ofNat 64 p.1)))
    (hstack : Disjoint (stackBase Γ s) (stackSize Γ) a L.size) (htext : L.text = 0)
    (howned : ∀ c ∈ Γ.owned, Disjoint c.1 c.2.size a L.size) :
    WellTyped fetch sys (Ψ.add a L) n Γ s :=
  have he := MemTy.add_ext (L := L) hN
  { regs := fun r hr => (h.regs r hr).ext he
    flags := h.flags
    stackPerm := h.stackPerm
    stackSize_lt := h.stackSize_lt
    stackFits := h.stackFits
    stack := fun k S hk p hp => (h.stack k S hk p hp).ext he
    heapPerm := fun x l hl => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · exact hperm
      · exact h.heapPerm x l hl'
    heap := fun x l hl p hp => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · exact (hvals p hp).ext he
      · exact (h.heap x l hl' p hp).ext he
    stackHeap := fun x l hl => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · exact hstack
      · exact h.stackHeap x l hl'
    sp := h.sp.ext he
    text := fun x l hl ht => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · exact absurd htext ht
      · exact h.text x l hl' ht
    owned :=
      { perm := h.owned.perm
        size_lt := h.owned.size_lt
        fits := h.owned.fits
        vals := fun c hc p hp => (h.owned.vals c hc p hp).ext he
        stack := h.owned.stack
        heap := fun c hc x l hl => by
          rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
          · exact howned c hc
          · exact h.owned.heap c hc x l hl'
        apart := h.owned.apart } }

/-- **An owned block may be frozen.** It leaves the context and joins the
memory typing as a block of the shape it has, byte for byte, and the register
holding its address becomes a pointer to it. -/
theorem freeze_ok {r : Reg} {k : Nat} {base : BitVec 64} {S : Shape} {tag : Option Nat}
    {τ : Ty} (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hr : r ≠ .rsp)
    (hΓ : Γ.regs r = .eq base) (hk : Γ.owned[k]? = some (base, S)) (hne : 0 < S.size)
    (hkind : ∀ t, tag = some t → Ψ.kinds t = some S)
    (hτ : ∀ Ψ₂ : MemTy, Ψ₂ base = some ⟨S, true, tag, 0⟩ → HasTy fetch sys Ψ₂ n τ base) :
    ∃ Ψ₂ : MemTy, Ψ.Ext Ψ₂ ∧ Ψ₂.WF ∧
      WellTyped fetch sys Ψ₂ n (({ Γ with owned := Γ.owned.eraseIdx k } : Ctx).setReg r τ) s := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (base, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
  have hsz := h.owned.size_lt _ hin
  have hpm := h.owned.perm _ hin
  have hst := h.owned.stack _ hin
  have hhp := h.owned.heap _ hin
  simp only at hsz hpm hst hhp
  -- no block of the memory typing starts where this one does
  have hN : Ψ base = none := by
    cases hl : Ψ base with
    | none => rfl
    | some l =>
      have hd := (hhp base l hl).1 (by have := hΨ.nonempty base l hl; omega)
      exact absurd hd (by bv_omega)
  have hsize : (⟨S, true, tag, 0⟩ : Layout).size = S.size := by simp [Layout.size]
  have h₀ := h.eraseOwned hΨ hk (s' := s) rfl rfl rfl (fun _ => .inl rfl)
  have hB := h₀.addBlock (a := base) (L := ⟨S, true, tag, 0⟩) hN
    (by rw [hsize]; exact ⟨State.canRead_of_canWrite hpm, fun _ => hpm⟩)
    (fun p hp => h.owned.vals _ hin p hp)
    (by rw [hsize]; exact hst) rfl
    (fun c hc => by
      obtain ⟨m, hm, hmk, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hc
      have hd := h.owned_apart hm hklt hmk
      rw [hkeq] at hd
      rw [hsize]
      exact hd.symm)
  refine ⟨Ψ.add base ⟨S, true, tag, 0⟩, MemTy.add_ext hN,
    MemTy.add_wf hΨ (by rw [hsize]; omega) (by rw [hsize]; exact hsz)
      (fun b lb hl => by rw [hsize]; exact hhp b lb hl) (h.owned.fits _ hin) hkind, ?_⟩
  refine hB.retype hr ?_
  rw [h.eqReg hr hΓ]
  exact hτ _ MemTy.add_self

/-- Freezing between instructions: from here on the block is an ordinary
one of the same shape, and the register is a pointer to it. -/
theorem BlockOk.freeze {a : BitVec 64} {Γ : Ctx} {r : Reg} {k : Nat} {base : BitVec 64}
    {S : Shape} {w : Bool} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq base)
    (hk : Γ.owned[k]? = some (base, S)) (hne : 0 < S.size)
    (hrest : BlockOk Φ fetch sys Ψ a
      (({ Γ with owned := Γ.owned.eraseIdx k } : Ctx).setReg r (.ptr S w 0))) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .grow (ι := Unit) (fun _ _ hΨ₁ _ _ h =>
    let ⟨Ψ₂, he, hwf, hw⟩ := freeze_ok (tag := none) h hΨ₁ hr hΓ hk hne (fun _ ht => nomatch ht)
      (fun Ψ₂ hl => hasTy_ptr.mpr ⟨base, _, hl, rfl, fun _ => rfl, by
        show base = base + BitVec.ofNat 64 0
        simp⟩)
    ⟨Ψ₂, he, hwf, (), hw⟩) (fun _ => hrest)

/-- Freezing as a block of a declared kind: the register becomes a pointer
to a block of that kind, which other blocks of the kind may then point to. -/
theorem BlockOk.freezeKind {a : BitVec 64} {Γ : Ctx} {r : Reg} {k : Nat} {base : BitVec 64}
    {S : Shape} {tag : Nat} {w : Bool} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq base)
    (hk : Γ.owned[k]? = some (base, S)) (hne : 0 < S.size)
    (hkind : Ψ.kinds tag = some S)
    (hrest : BlockOk Φ fetch sys Ψ a
      (({ Γ with owned := Γ.owned.eraseIdx k } : Ctx).setReg r (.ref tag w 0))) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .grow (ι := Unit) (fun _ he₁ hΨ₁ _ _ h =>
    let ⟨Ψ₂, he, hwf, hw⟩ := freeze_ok (tag := some tag) h hΨ₁ hr hΓ hk hne
      (fun t ht => by cases ht; rw [he₁.kinds]; exact hkind)
      (fun Ψ₂ hl => hasTy_ref.mpr ⟨base, _, hl, rfl, fun _ => rfl, by
        show base = base + BitVec.ofNat 64 0
        simp⟩)
    ⟨Ψ₂, he, hwf, (), hw⟩) (fun _ => hrest)

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

/-- **An owned block may be split in two** at any byte. The first `m` bytes
stay a block where it was; the rest become a block of their own, `m` bytes
on. A typed value that lay across the split is forgotten. Each part may then
be stored to, frozen or given back on its own. -/
theorem WellTyped.splitOwned {k m : Nat} {base : BitVec 64} {S : Shape}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hk : Γ.owned[k]? = some (base, S))
    (hm : m ≤ S.size) :
    WellTyped fetch sys Ψ n
      { Γ with owned :=
          (base + BitVec.ofNat 64 m, S.drop m) :: (base, S.take m) :: Γ.owned.eraseIdx k } s := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (base, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
  have hsz := h.owned.size_lt _ hin
  have hpm := h.owned.perm _ hin
  have hst := h.owned.stack _ hin
  have hhp := h.owned.heap _ hin
  have hft := h.owned.fits _ hin
  have hvl := h.owned.vals _ hin
  simp only at hsz hpm hst hhp hft hvl
  -- the other blocks are apart from the whole of this one
  have hother : ∀ c ∈ Γ.owned.eraseIdx k, Disjoint base S.size c.1 c.2.size := by
    intro c hc
    obtain ⟨j, hj, hjk, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hc
    have hd := h.owned_apart hj hklt hjk
    rw [hkeq] at hd
    exact hd
  have hsub : ∀ c ∈ Γ.owned.eraseIdx k, c ∈ Γ.owned :=
    fun c hc => (List.eraseIdx_sublist _ _).subset hc
  have h₀ := h.eraseOwned hΨ hk (s' := s) rfl rfl rfl (fun _ => .inl rfl)
  have e0 : base + BitVec.ofNat 64 0 = base := by simp
  -- the first part
  have h₁ := h₀.addOwned (b := (base, S.take m))
    (Linux.canWrite_le hpm hm) (by show m < 2 ^ 64; omega)
    (fun p hp => by
      simp only [ShapeOf.take, List.mem_filter, decide_eq_true_eq] at hp
      exact hp.2)
    (fun p hp => by
      simp only [ShapeOf.take, List.mem_filter] at hp
      exact hvl p hp.1)
    (by
      have := hst.sub_right (p := 0) (m' := m) (by omega) h.stackSize_lt hsz
      rw [e0] at this
      exact this)
    (fun x l hl => by
      have := (hhp x l hl).symm.sub_right (p := 0) (m' := m) (by omega)
        (hΨ.size_lt x l hl) hsz
      rw [e0] at this
      exact this.symm)
    (fun c hc => by
      have := (hother c hc).symm.sub_right (p := 0) (m' := m) (by omega)
        (h.owned.size_lt c (hsub c hc)) hsz
      rw [e0] at this
      exact this.symm)
  -- the rest
  refine h₁.addOwned (b := (base + BitVec.ofNat 64 m, S.drop m)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact State.canWrite_sub hpm (by show m + (S.size - m) ≤ S.size; omega)
  · show S.size - m < 2 ^ 64; omega
  · intro p hp
    simp only [ShapeOf.drop, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
    obtain ⟨q, ⟨hq, hmq⟩, rfl⟩ := hp
    have := hft q hq
    show q.1 - m + 8 ≤ S.size - m
    omega
  · intro p hp
    simp only [ShapeOf.drop, List.mem_map, List.mem_filter, decide_eq_true_eq] at hp
    obtain ⟨q, ⟨hq, hmq⟩, rfl⟩ := hp
    have := hvl q hq
    have hq8 := hft q hq
    show HasTy fetch sys Ψ n q.2 (s.load64 (base + BitVec.ofNat 64 m + BitVec.ofNat 64 (q.1 - m)))
    rwa [show base + BitVec.ofNat 64 m + BitVec.ofNat 64 (q.1 - m)
        = base + BitVec.ofNat 64 q.1 by bv_omega]
  · exact hst.sub_right (by show m + (S.size - m) ≤ S.size; omega) h.stackSize_lt hsz
  · intro x l hl
    exact ((hhp x l hl).symm.sub_right (by show m + (S.size - m) ≤ S.size; omega)
      (hΨ.size_lt x l hl) hsz).symm
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · show Disjoint (base + BitVec.ofNat 64 m) (S.size - m) base m
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
    · exact ((hother c hc).symm.sub_right (by show m + (S.size - m) ≤ S.size; omega)
        (h.owned.size_lt c (hsub c hc)) hsz).symm

/-- Splitting between instructions. -/
theorem BlockOk.splitOwned {a : BitVec 64} {Γ : Ctx} {r : Reg} {k m : Nat} {base : BitVec 64}
    {S : Shape} (_hΓ : Γ.regs r = .eq base) (hk : Γ.owned[k]? = some (base, S))
    (hm : m ≤ S.size)
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with owned :=
          (base + BitVec.ofNat 64 m, S.drop m) :: (base, S.take m) :: Γ.owned.eraseIdx k }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ _ hΨ₁ _ _ h => h.splitOwned hΨ₁ hk hm) hrest

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

/-- What is left of a list after two places are taken out is at neither. -/
private theorem mem_eraseIdx_two {α : Type} {L : List α} {lo hi : Nat} {c : α} (hlt : lo < hi)
    (hc : c ∈ (L.eraseIdx hi).eraseIdx lo) :
    ∃ j, ∃ hj : j < L.length, j ≠ lo ∧ j ≠ hi ∧ L[j] = c := by
  obtain ⟨j, hj, hjlo, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hc
  rw [List.getElem_eraseIdx]
  have hlen := hj
  rw [List.length_eraseIdx] at hlen
  split at hlen
  · split
    · exact ⟨j, by omega, hjlo, by omega, rfl⟩
    · exact ⟨j + 1, by omega, by omega, by omega, rfl⟩
  · split
    · exact ⟨j, by omega, hjlo, by omega, rfl⟩
    · omega

/-- Two owned blocks may be replaced by one that is writable, holds what its
shape says, and is apart from whatever both of them were apart from. -/
private theorem WellTyped.mergeOwned {lo hi : Nat} {bl bh b : BitVec 64 × Shape}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hlt : lo < hi)
    (hlo : Γ.owned[lo]? = some bl) (hhi : Γ.owned[hi]? = some bh)
    (hperm : s.canWrite b.1 b.2.size = true) (hsz : b.2.size < 2 ^ 64)
    (hfits : ∀ p ∈ b.2.vals, p.1 + 8 ≤ b.2.size)
    (hvals : ∀ p ∈ b.2.vals, HasTy fetch sys Ψ n p.2 (s.load64 (b.1 + BitVec.ofNat 64 p.1)))
    (hcover : ∀ a m, Disjoint a m bl.1 bl.2.size → Disjoint a m bh.1 bh.2.size →
      Disjoint a m b.1 b.2.size) :
    WellTyped fetch sys Ψ n
      { Γ with owned := b :: (Γ.owned.eraseIdx hi).eraseIdx lo } s := by
  obtain ⟨hlolt, hloeq⟩ := List.getElem?_eq_some_iff.mp hlo
  obtain ⟨hhilt, hhieq⟩ := List.getElem?_eq_some_iff.mp hhi
  have hinl : bl ∈ Γ.owned := hloeq ▸ List.getElem_mem hlolt
  have hinh : bh ∈ Γ.owned := hhieq ▸ List.getElem_mem hhilt
  have h₁ := h.eraseOwned (a := bh.1) (S := bh.2) hΨ hhi (s' := s) rfl rfl rfl (fun _ => .inl rfl)
  have hlo' : (Γ.owned.eraseIdx hi)[lo]? = some bl := by
    rw [List.getElem?_eraseIdx_of_lt hlt]
    exact hlo
  have h₂ := h₁.eraseOwned (a := bl.1) (S := bl.2) hΨ hlo' (s' := s) rfl rfl rfl
    (fun _ => .inl rfl)
  refine h₂.addOwned hperm hsz hfits hvals ?_ ?_ ?_
  · exact hcover _ _ (h.owned.stack _ hinl) (h.owned.stack _ hinh)
  · intro x l hl
    exact (hcover _ _ (h.owned.heap _ hinl x l hl).symm (h.owned.heap _ hinh x l hl).symm).symm
  · intro c hc
    obtain ⟨j, hj, hjlo, hjhi, rfl⟩ := mem_eraseIdx_two hlt hc
    have d₁ := h.owned_apart hj hlolt hjlo
    have d₂ := h.owned_apart hj hhilt hjhi
    rw [hloeq] at d₁
    rw [hhieq] at d₂
    exact (hcover _ _ d₁.symm d₂.symm).symm

/-- **Two owned blocks that lie end to end may be joined into one**, the
bytes of the first followed by those of the second. -/
theorem WellTyped.joinOwned {k₁ k₂ : Nat} {base : BitVec 64} {S₁ S₂ : Shape}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hk₁ : Γ.owned[k₁]? = some (base, S₁))
    (hk₂ : Γ.owned[k₂]? = some (base + BitVec.ofNat 64 S₁.size, S₂)) (hne : k₁ ≠ k₂)
    (hsz : S₁.size + S₂.size < 2 ^ 64) :
    WellTyped fetch sys Ψ n
      { Γ with owned :=
          (base, S₁.append S₂) :: (Γ.owned.eraseIdx (max k₁ k₂)).eraseIdx (min k₁ k₂) } s := by
  have hin₁ : (base, S₁) ∈ Γ.owned := List.mem_of_getElem? hk₁
  have hin₂ : (base + BitVec.ofNat 64 S₁.size, S₂) ∈ Γ.owned := List.mem_of_getElem? hk₂
  have hperm : s.canWrite base (S₁.append S₂).size = true := by
    have p₁ := State.canWrite_iff.mp (h.owned.perm _ hin₁)
    have p₂ := State.canWrite_iff.mp (h.owned.perm _ hin₂)
    simp only at p₁ p₂
    rw [State.canWrite_iff]
    show ∀ i, i < S₁.size + S₂.size → _
    intro i hi
    by_cases hi₁ : i < S₁.size
    · exact p₁ i hi₁
    · have := p₂ (i - S₁.size) (by omega)
      rwa [show base + BitVec.ofNat 64 S₁.size + BitVec.ofNat 64 (i - S₁.size)
          = base + BitVec.ofNat 64 i by bv_omega] at this
  have hfits : ∀ p ∈ (S₁.append S₂).vals, p.1 + 8 ≤ (S₁.append S₂).size := by
    intro p hp
    simp only [ShapeOf.append, List.mem_append, List.mem_map] at hp
    show p.1 + 8 ≤ S₁.size + S₂.size
    rcases hp with hp | ⟨q, hq, rfl⟩
    · have := h.owned.fits _ hin₁ p hp; simp only at this; omega
    · have := h.owned.fits _ hin₂ q hq; simp only at this ⊢; omega
  have hvals : ∀ p ∈ (S₁.append S₂).vals,
      HasTy fetch sys Ψ n p.2 (s.load64 (base + BitVec.ofNat 64 p.1)) := by
    intro p hp
    simp only [ShapeOf.append, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact h.owned.vals _ hin₁ p hp
    · have := h.owned.vals _ hin₂ q hq
      simp only at this ⊢
      rwa [show base + BitVec.ofNat 64 S₁.size + BitVec.ofNat 64 q.1
          = base + BitVec.ofNat 64 (S₁.size + q.1) by bv_omega] at this
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · rw [Nat.max_eq_right (by omega), Nat.min_eq_left (by omega)]
    exact h.mergeOwned (b := (base, S₁.append S₂)) hΨ hlt hk₁ hk₂ hperm hsz hfits hvals
      (fun a m d₁ d₂ => Disjoint.union_right (m₁ := S₁.size) (m₂ := S₂.size) d₁ d₂ hsz)
  · rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
    exact h.mergeOwned (b := (base, S₁.append S₂)) hΨ hgt hk₂ hk₁ hperm hsz hfits hvals
      (fun a m d₂ d₁ => Disjoint.union_right (m₁ := S₁.size) (m₂ := S₂.size) d₁ d₂ hsz)

/-- Joining between instructions. -/
theorem BlockOk.joinOwned {a : BitVec 64} {Γ : Ctx} {r : Reg} {k₁ k₂ : Nat} {base : BitVec 64}
    {S₁ S₂ : Shape} (_hΓ : Γ.regs r = .eq base) (hk₁ : Γ.owned[k₁]? = some (base, S₁))
    (hk₂ : Γ.owned[k₂]? = some (base + BitVec.ofNat 64 S₁.size, S₂)) (hne : k₁ ≠ k₂)
    (hsz : S₁.size + S₂.size < 2 ^ 64)
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with owned :=
          (base, S₁.append S₂) :: (Γ.owned.eraseIdx (max k₁ k₂)).eraseIdx (min k₁ k₂) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ _ hΨ₁ _ _ h => h.joinOwned hΨ₁ hk₁ hk₂ hne hsz) hrest

/-- A list is its element at one place followed by the rest, in some order. -/
private theorem perm_cons_eraseIdx {α : Type} {l : List α} {k : Nat} {b : α}
    (h : l[k]? = some b) : (b :: l.eraseIdx k).Perm l := by
  induction l generalizing k with
  | nil => cases h
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact .refl _
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.eraseIdx_cons_succ]
      exact (List.Perm.swap x b _).trans ((ih h).cons x)

/-- **The order in which a context lists the blocks it owns means nothing.** -/
theorem WellTyped.permOwned {L : List (BitVec 64 × Shape)}
    (h : WellTyped fetch sys Ψ n Γ s) (hp : L.Perm Γ.owned) :
    WellTyped fetch sys Ψ n { Γ with owned := L } s :=
  { regs := h.regs, flags := h.flags, stackPerm := h.stackPerm, stackSize_lt := h.stackSize_lt,
    stackFits := h.stackFits, stack := h.stack, heapPerm := h.heapPerm, heap := h.heap, stackHeap := h.stackHeap,
    sp := h.sp, text := h.text,
    owned :=
      { perm := fun b hb => h.owned.perm b (hp.subset hb)
        size_lt := fun b hb => h.owned.size_lt b (hp.subset hb)
        fits := fun b hb => h.owned.fits b (hp.subset hb)
        vals := fun b hb => h.owned.vals b (hp.subset hb)
        stack := fun b hb => h.owned.stack b (hp.subset hb)
        heap := fun b hb => h.owned.heap b (hp.subset hb)
        apart := (hp.pairwise_iff (fun hd => hd.symm)).mpr h.owned.apart } }

/-- Listing one owned block first, between instructions: a call hands over
the blocks its signature takes from the front of the list. -/
theorem BlockOk.frontOwned {a : BitVec 64} {Γ : Ctx} {r : Reg} {k : Nat} {base : BitVec 64}
    {S : Shape} (_hΓ : Γ.regs r = .eq base) (hk : Γ.owned[k]? = some (base, S))
    (hrest : BlockOk Φ fetch sys Ψ a { Γ with owned := (base, S) :: Γ.owned.eraseIdx k }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ _ _ _ _ h => h.permOwned (perm_cons_eraseIdx hk)) hrest

/-- An `mmap` whose memory the program is to own, in a block: what follows is
typed twice, for an error number in `rax` and for the address of whole pages
of plain bytes that the context then owns. -/
theorem BlockOk.mmapOwn {a : BitVec 64} {Γ : Ctx} {len : BitVec 64} {l : BitVec 64} {size : Nat}
    (hf : fetch a = some (.syscall, l)) (hΓ : Γ.regs .rax = .eq 9)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22) (hsize : size = (len.toNat + 4095) / 4096 * 4096)
    (herr : ∀ e, SysErr e →
      BlockOk Φ fetch linux Ψ (a + l) (Γ.afterSyscall.setReg .rax (.eq e)))
    (hok : ∀ p : BitVec 64, p.toNat % 4096 = 0 → p < 0x800000000000 →
      BlockOk Φ fetch linux Ψ (a + l)
        { Γ.afterSyscall.setReg .rax (.eq p) with
          owned := (p, ShapeOf.raw size) :: Γ.owned }) :
    BlockOk Φ fetch linux Ψ a Γ := by
  subst hsize
  exact .sem hf (linux_mmap_own hΓ hlen hprot hflags) (fun x =>
    match x with
    | .inl e => herr e.1 e.2
    | .inr p => hok p.1 p.2.1 p.2.2)

/-! ## Pieces of the stack

How the stack is cut into pieces is a matter of description: a run of pieces
may be described by any other run that comes to as many bytes and says
nothing of them that the first did not. -/

/-- **A run of pieces of the stack may be described another way**, by pieces
that come to as many bytes, whose typed values each lie inside their piece
and each are a typed value of the run as it was, at the same place. -/
theorem WellTyped.repiece {pre mid mid' post : List Shape}
    (h : WellTyped fetch sys Ψ n Γ s) (hst : Γ.stack = pre ++ mid ++ post)
    (hlen : stackLen mid' = stackLen mid)
    (hfits : ∀ T ∈ mid', ∀ q ∈ T.vals, q.1 + 8 ≤ T.size)
    (hvals : ∀ j T, mid'[j]? = some T → ∀ q ∈ T.vals, ∃ i S p, mid[i]? = some S ∧ p ∈ S.vals ∧
      p.2 = q.2 ∧ stackOff mid i + p.1 = stackOff mid' j + q.1) :
    WellTyped fetch sys Ψ n { Γ with stack := pre ++ mid' ++ post } s := by
  have hz : stackSize { Γ with stack := pre ++ mid' ++ post } = stackSize Γ := by
    simp only [stackSize, hst, stackLen_append, hlen]
  have hb : stackBase { Γ with stack := pre ++ mid' ++ post } s = stackBase Γ s := rfl
  exact {
    regs := h.regs
    flags := h.flags
    stackPerm := by rw [hb, hz]; exact h.stackPerm
    stackSize_lt := by rw [hz]; exact h.stackSize_lt
    stackFits := fun T hT q hq => by
      rcases List.mem_append.mp hT with hT | hT
      · rcases List.mem_append.mp hT with hT | hT
        · exact h.stackFits T (by rw [hst]; simp [hT]) q hq
        · exact hfits T hT q hq
      · exact h.stackFits T (by rw [hst]; simp [hT]) q hq
    stack := fun k T hk q hq => by
      show HasTy fetch sys Ψ n q.2
        (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff (pre ++ mid' ++ post) k + q.1)))
      have hk' : (pre ++ mid' ++ post)[k]? = some T := hk
      by_cases h1 : k < pre.length
      · -- a piece before the run: as it was
        have e1 : (pre ++ mid' ++ post)[k]? = pre[k]? := by
          rw [List.append_assoc, List.getElem?_append_left h1]
        have e2 : Γ.stack[k]? = pre[k]? := by
          rw [hst, List.append_assoc, List.getElem?_append_left h1]
        have o1 : stackOff (pre ++ mid' ++ post) k = stackOff pre k := by
          rw [List.append_assoc, stackOff_append_le _ _ (by omega)]
        have o2 : stackOff Γ.stack k = stackOff pre k := by
          rw [hst, List.append_assoc, stackOff_append_le _ _ (by omega)]
        rw [o1, ← o2]
        exact h.stack k T (by rw [e2, ← e1]; exact hk') q hq
      · by_cases h2 : k < pre.length + mid'.length
        · -- a piece of the run: each typed value was one of the run's
          obtain ⟨j, rfl⟩ : ∃ j, k = pre.length + j := ⟨k - pre.length, by omega⟩
          have hj : mid'[j]? = some T := by
            rw [List.getElem?_append_left (by simp; omega),
              List.getElem?_append_right (by omega)] at hk'
            simpa using hk'
          obtain ⟨i, S, p, hi, hp, hty, hoff⟩ := hvals j T hj q hq
          have hilt : i < mid.length := (List.getElem?_eq_some_iff.mp hi).1
          have hS : Γ.stack[pre.length + i]? = some S := by
            rw [hst, List.getElem?_append_left (by simp; omega),
              List.getElem?_append_right (by omega)]
            simpa using hi
          have o1 : stackOff (pre ++ mid' ++ post) (pre.length + j)
              = stackLen pre + stackOff mid' j := by
            rw [List.append_assoc, stackOff_append]
            rw [stackOff_append_le _ _ (by omega)]
          have o2 : stackOff Γ.stack (pre.length + i) = stackLen pre + stackOff mid i := by
            rw [hst, List.append_assoc, stackOff_append]
            rw [stackOff_append_le _ _ (by omega)]
          have := h.stack (pre.length + i) S hS p hp
          rw [o2, hty] at this
          rw [o1]
          rwa [show stackLen pre + stackOff mid' j + q.1 = stackLen pre + stackOff mid i + p.1
            by omega]
        · -- a piece after the run: as it was, the same distance up
          obtain ⟨j, rfl⟩ : ∃ j, k = (pre ++ mid').length + j :=
            ⟨k - (pre ++ mid').length, by simp; omega⟩
          have hj : post[j]? = some T := by
            rw [List.getElem?_append_right (by omega)] at hk'
            simpa using hk'
          have hS : Γ.stack[(pre ++ mid).length + j]? = some T := by
            rw [hst, List.getElem?_append_right (by omega)]
            simpa using hj
          have o1 : stackOff (pre ++ mid' ++ post) ((pre ++ mid').length + j)
              = stackLen pre + stackLen mid' + stackOff post j := by
            rw [stackOff_append, stackLen_append]
          have o2 : stackOff Γ.stack ((pre ++ mid).length + j)
              = stackLen pre + stackLen mid + stackOff post j := by
            rw [hst, stackOff_append, stackLen_append]
          have := h.stack ((pre ++ mid).length + j) T hS q hq
          rw [o2] at this
          rw [o1, hlen]
          exact this
    heapPerm := h.heapPerm
    heap := h.heap
    stackHeap := fun a l hl => by rw [hb, hz]; exact h.stackHeap a l hl
    owned := h.owned.frame rfl rfl hb hz (fun _ _ _ _ => rfl)
    text := h.text
    sp := h.sp }

theorem eq_take_cons_drop {α : Type} {l : List α} {k : Nat} {x : α} (h : l[k]? = some x) :
    l = l.take k ++ [x] ++ l.drop (k + 1) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hk,
    List.take_append_drop]

theorem eq_take_two_drop {α : Type} {l : List α} {k : Nat} {x y : α} (h : l[k]? = some x)
    (h' : l[k + 1]? = some y) : l = l.take k ++ [x, y] ++ l.drop (k + 2) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.mp h'
  rw [List.append_assoc]
  show l = List.take k l ++ (l[k] :: l[k + 1] :: List.drop (k + 2) l)
  rw [← List.drop_eq_getElem_cons hk', ← List.drop_eq_getElem_cons hk, List.take_append_drop]

/-- **A piece of the stack may be regarded as two**: its first `m` bytes and
the rest. An access then has to keep to one of them, which is how a local of
so many bytes is kept to exactly that many. -/
theorem BlockOk.splitStack {a : BitVec 64} {Γ : Ctx} {k m : Nat} {S : Shape}
    (hk : Γ.stack[k]? = some S) (hm : m ≤ S.size)
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.take k ++ [S.take m, S.drop m] ++ Γ.stack.drop (k + 1) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ _ _ _ _ h =>
    h.repiece (mid := [S]) (eq_take_cons_drop hk)
      (by simp only [stackLen_cons, stackLen_nil, ShapeOf.take, ShapeOf.drop]; omega)
      (fun T hT q hq => by
        have hS := h.stackFits S (List.mem_of_getElem? hk)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
        rcases hT with rfl | rfl
        · simp only [ShapeOf.take, List.mem_filter, decide_eq_true_eq] at hq ⊢
          exact hq.2
        · simp only [ShapeOf.drop, List.mem_map, List.mem_filter, decide_eq_true_eq] at hq ⊢
          obtain ⟨p, ⟨hp, hmp⟩, rfl⟩ := hq
          have := hS p hp
          simp only
          omega)
      (fun j T hj q hq => by
        match j, hj with
        | 0, hj =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          simp only [ShapeOf.take, List.mem_filter] at hq
          exact ⟨0, S, q, rfl, hq.1, rfl, by simp⟩
        | 1, hj =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          simp only [ShapeOf.drop, List.mem_map, List.mem_filter, decide_eq_true_eq] at hq
          obtain ⟨p, ⟨hp, hmp⟩, rfl⟩ := hq
          refine ⟨0, S, p, rfl, hp, rfl, ?_⟩
          simp only [stackOff_zero, stackOff_cons_succ, ShapeOf.take]
          omega
        | j + 2, hj => simp at hj)) hrest

/-- **Two pieces of the stack that lie end to end may be regarded as one.** -/
theorem BlockOk.joinStack {a : BitVec 64} {Γ : Ctx} {k : Nat} {S₁ S₂ : Shape}
    (hk : Γ.stack[k]? = some S₁) (hk' : Γ.stack[k + 1]? = some S₂)
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.take k ++ [S₁.append S₂] ++ Γ.stack.drop (k + 2) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ _ _ _ _ h =>
    h.repiece (mid := [S₁, S₂]) (eq_take_two_drop hk hk')
      (by simp only [stackLen_cons, stackLen_nil, ShapeOf.append]; omega)
      (fun T hT q hq => by
        have h1 := h.stackFits S₁ (List.mem_of_getElem? hk)
        have h2 := h.stackFits S₂ (List.mem_of_getElem? hk')
        simp only [List.mem_singleton] at hT
        subst hT
        simp only [ShapeOf.append, List.mem_append, List.mem_map] at hq ⊢
        rcases hq with hq | ⟨p, hp, rfl⟩
        · have := h1 q hq; omega
        · have := h2 p hp
          simp only
          omega)
      (fun j T hj q hq => by
        match j, hj with
        | 0, hj =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          simp only [ShapeOf.append, List.mem_append, List.mem_map] at hq
          rcases hq with hq | ⟨p, hp, rfl⟩
          · exact ⟨0, S₁, q, rfl, hq, rfl, by simp⟩
          · exact ⟨1, S₂, p, rfl, hp, rfl, by simp⟩
        | j + 1, hj => simp at hj)) hrest

end TypedAsm
