import TypedAsm.Typing

/-!
# Soundness

A well-typed program started in a well-typed state is safe.
-/

namespace TypedAsm

variable {Φ : CodeTy} {Ψ : MemTy} {fetch : Fetch} {sys : Syscall} {ix : Nat}

/-! ## Subtyping -/

theorem HasTy.sub {τ υ : Ty} {v : BitVec 64} (h : Sub τ υ) (hv : HasTy fetch sys Ψ ix τ v) :
    HasTy fetch sys Ψ ix υ v := by
  induction h generalizing v with
  | refl => exact hv
  | int => exact HasTy.int v
  | readOnly fields w index =>
    obtain ⟨a, l, hl, hf, hw, hva⟩ := hasTy_ptr.mp hv
    exact hasTy_ptr.mpr ⟨a, l, hl, hf, fun _ => hw rfl, hva⟩
  | refReadOnly tag w index =>
    obtain ⟨a, l, hl, ht, hw, hva⟩ := hasTy_ref.mp hv
    exact hasTy_ref.mpr ⟨a, l, hl, ht, fun _ => hw rfl, hva⟩
  | nullable _ ih => exact hasTy_nullable.mpr (.inr (ih hv))
  | null τ => exact hasTy_nullable.mpr (.inl (hasTy_eq.mp hv))
  | nullableMono _ ih => exact hasTy_nullable.mpr ((hasTy_nullable.mp hv).imp id ih)
  | strLess more =>
    obtain ⟨a, l, off, hl, hoff, hva⟩ := hasTy_str.mp hv
    exact hasTy_str.mpr ⟨a, l, off, hl, by
      simp only [↓reduceIte] at hoff
      cases more <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega, hva⟩
  | codeAll pre x => exact hasTy_codeAll.mp hv x
  | codeAllMap pre f => exact hasTy_codeAll.mpr fun x => hasTy_codeAll.mp hv (f x)
  | orErr _ ih => exact hasTy_orErr.mpr (.inr (ih hv))
  | orErrMono _ ih => exact hasTy_orErr.mpr ((hasTy_orErr.mp hv).imp id ih)

theorem SubList.stackLen_eq {σ ρ : List (ShapeOf Ty)} (h : SubList σ ρ) :
    stackLen σ = stackLen ρ := by
  induction h with
  | nil => rfl
  | cons hs _ ih => simp only [stackLen, hs.size, ih]

theorem SubList.stackOff_eq {σ ρ : List (ShapeOf Ty)} (h : SubList σ ρ) (k : Nat) :
    stackOff σ k = stackOff ρ k := by
  induction h generalizing k with
  | nil => rfl
  | cons hs _ ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [stackOff, hs.size, ih]

theorem SubList.get {σ ρ : List (ShapeOf Ty)} (h : SubList σ ρ) :
    ∀ (k : Nat) (T : ShapeOf Ty), ρ[k]? = some T → ∃ S, σ[k]? = some S ∧ SubShape S T := by
  induction h with
  | nil => intro k T h; simp at h
  | cons hs _ ih =>
    intro k T h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨_, by simp, h ▸ hs⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      simpa using ih k T h
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

/-! ## The stack region -/

/-- The address `j` bytes above the stack pointer, measured from the bottom
of the stack region. -/
theorem slot_addr (Γ : Ctx) (s : State) (j : Nat) :
    stackBase Γ s + BitVec.ofNat 64 (Γ.room + j) = s.getReg .rsp + BitVec.ofNat 64 j := by
  simp only [stackBase]
  bv_omega

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

/-- Owned blocks stay as the context says across a change that leaves their
permissions, their fields and the stack region as they were. -/
theorem OwnedOk.frame {H : Ty → BitVec 64 → Prop} {Γ Γ' : Ctx} {s s' : State}
    (h : OwnedOk H Ψ Γ s) (ho : Γ'.owned = Γ.owned) (hp : s'.perm = s.perm)
    (hb : stackBase Γ' s' = stackBase Γ s) (hz : stackSize Γ' = stackSize Γ)
    (hload : ∀ b ∈ Γ.owned, ∀ o, o + 8 ≤ b.2.size →
      s'.load64 (b.1 + BitVec.ofNat 64 o) = s.load64 (b.1 + BitVec.ofNat 64 o)) :
    OwnedOk H Ψ Γ' s' :=
  { perm := fun b hb' => by
      rw [ho] at hb'; rw [State.canWrite_congr hp]; exact h.perm b hb'
    size_lt := fun b hb' => h.size_lt b (ho ▸ hb')
    fits := fun b hb' => h.fits b (ho ▸ hb')
    vals := fun b hb' p hp' => by
      rw [ho] at hb'
      rw [hload b hb' p.1 (h.fits b hb' p hp')]
      exact h.vals b hb' p hp'
    stack := fun b hb' => by rw [ho] at hb'; rw [hb, hz]; exact h.stack b hb'
    heap := fun b hb' => h.heap b (ho ▸ hb')
    apart := ho ▸ h.apart }

/-- A context that owns nothing asks nothing. -/
theorem OwnedOk.nil {H : Ty → BitVec 64 → Prop} {Γ : Ctx} {s : State} (h : Γ.owned = []) :
    OwnedOk H Ψ Γ s :=
  { perm := fun b hb => by rw [h] at hb; cases hb
    size_lt := fun b hb => by rw [h] at hb; cases hb
    fits := fun b hb => by rw [h] at hb; cases hb
    vals := fun b hb => by rw [h] at hb; cases hb
    stack := fun b hb => by rw [h] at hb; cases hb
    heap := fun b hb => by rw [h] at hb; cases hb
    apart := by rw [h]; exact .nil }

/-! ## Keeping a state well typed -/

namespace WellTyped

variable {Γ : Ctx} {s : State}

/-- A typed value of a piece of the stack lies inside the stack. -/
theorem stack_in {k : Nat} {S : Shape} {p : Nat × Ty} (h : WellTyped fetch sys Ψ ix Γ s)
    (hk : Γ.stack[k]? = some S) (hp : p ∈ S.vals) :
    stackOff Γ.stack k + p.1 + 8 ≤ stackLen Γ.stack := by
  have h1 := h.stackFits S (List.mem_of_getElem? hk) p hp
  have h2 := stackOff_add_le hk
  omega

/-- Well-typedness looks only at the registers, flags, memory and permissions. -/
theorem congr {t : State} (h : WellTyped fetch sys Ψ ix Γ s) (hr : t.regs = s.regs)
    (hf : t.flags = s.flags) (hm : t.mem = s.mem) (hp : t.perm = s.perm) :
    WellTyped fetch sys Ψ ix Γ t := by
  have hg : ∀ r, t.getReg r = s.getReg r := fun r => by simp only [State.getReg, hr]
  have hb : stackBase Γ t = stackBase Γ s := by simp only [stackBase, hg]
  exact {
    regs := fun r hr' => by rw [hg]; exact h.regs r hr'
    flags := by rw [hf]; exact h.flags
    stackPerm := by rw [hb, State.canWrite_congr hp]; exact h.stackPerm
    stackBound := h.stackBound
    stackFits := h.stackFits
    stack := fun k S hk p hp => by rw [hg, State.load64_congr hm]; exact h.stack k S hk p hp
    heapPerm := fun a l hl => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm a l hl
    heap := fun a l hl p hp => by rw [State.load64_congr hm]; exact h.heap a l hl p hp
    stackHeap := fun a l hl => by rw [hb]; exact h.stackHeap a l hl
    owned := h.owned.frame rfl hp hb rfl (fun b _ i _ => State.load64_congr hm _)
    text := fun a l hl ht => by rw [hm]; exact h.text a l hl ht
    sp := by rw [hg]; exact h.sp }

/-- A state matching a context matches every weaker context. -/
theorem sub {Δ : Ctx} (h : WellTyped fetch sys Ψ ix Γ s) (hs : CtxSub Γ Δ) : WellTyped fetch sys Ψ ix Δ s := by
  have hl := hs.stack.stackLen_eq
  have hb : stackBase Δ s = stackBase Γ s := by simp only [stackBase, hs.room]
  have hz : stackSize Δ = stackSize Γ := by simp only [stackSize, hs.room, hl]
  exact {
    regs := fun r hr => (h.regs r hr).sub (hs.regs r hr)
    flags := hs.flags _ h.flags
    stackPerm := by rw [hb, hz]; exact h.stackPerm
    stackBound := by rw [hz, ← hs.above]; exact h.stackBound
    stackFits := fun T hT q hq => by
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hT
      obtain ⟨S, hS, hsub⟩ := hs.stack.get k T hk
      obtain ⟨p, hp, hpq, -⟩ := hsub.vals q hq
      have := h.stackFits S (List.mem_of_getElem? hS) p hp
      rw [← hsub.size, ← hpq]
      exact this
    stack := fun k T hk q hq => by
      obtain ⟨S, hS, hsub⟩ := hs.stack.get k T hk
      obtain ⟨p, hp, hpq, hty⟩ := hsub.vals q hq
      rw [← hs.stack.stackOff_eq k, ← hpq]
      exact (h.stack k S hS p hp).sub hty
    heapPerm := h.heapPerm
    heap := h.heap
    stackHeap := fun a l hl => by rw [hb, hz]; exact h.stackHeap a l hl
    owned := h.owned.frame hs.owned.symm rfl hb hz (fun _ _ _ _ => rfl)
    text := h.text
    sp := h.sp.sub hs.sp }

/-- Writing a value of type `τ` to a register other than `rsp`. -/
theorem setReg {r : Reg} {τ : Ty} {v : BitVec 64} (h : WellTyped fetch sys Ψ ix Γ s) (hr : r ≠ .rsp)
    (hv : HasTy fetch sys Ψ ix τ v) : WellTyped fetch sys Ψ ix (Γ.setReg r τ) (s.setReg r v) := by
  have hsp : (s.setReg r v).getReg .rsp = s.getReg .rsp :=
    State.getReg_setReg_other s r .rsp v (Ne.symm hr)
  have hb : stackBase (Γ.setReg r τ) (s.setReg r v) = stackBase Γ s := by
    simp only [stackBase, hsp, CtxOf.setReg]
  have hm : (s.setReg r v).mem = s.mem := rfl
  have hp : (s.setReg r v).perm = s.perm := rfl
  exact {
    regs := fun r' hr' => by
      by_cases h' : r' = r
      · subst h'
        simp only [CtxOf.setReg, State.getReg_setReg_same, ite_true]
        exact hv
      · rw [State.getReg_setReg_other s r r' v h']
        simp only [CtxOf.setReg, h', ite_false]
        exact h.regs r' hr'
    flags := h.flags
    stackPerm := by rw [hb, State.canWrite_congr hp]; exact h.stackPerm
    stackBound := h.stackBound
    stackFits := h.stackFits
    stack := fun k S hk p hp => by rw [hsp, State.load64_congr hm]; exact h.stack k S hk p hp
    heapPerm := fun a l hl => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm a l hl
    heap := fun a l hl p hp => by rw [State.load64_congr hm]; exact h.heap a l hl p hp
    stackHeap := fun a l hl => by rw [hb]; exact h.stackHeap a l hl
    owned := h.owned.frame rfl hp hb rfl (fun b _ i _ => State.load64_congr hm _)
    text := fun a l hl ht => by rw [hm]; exact h.text a l hl ht
    sp := by
      rw [hsp]
      simp only [CtxOf.setReg, Ne.symm hr, ↓reduceIte]
      exact h.sp }

/-- Replacing the flags with ones that satisfy the new context's flags predicate. -/
theorem setFlags {f : Flags} {P : Flags → Prop} (h : WellTyped fetch sys Ψ ix Γ s) (hf : P f) :
    WellTyped fetch sys Ψ ix { Γ with flags := P } { s with flags := f } :=
  { regs := h.regs, flags := hf, stackPerm := h.stackPerm, stackBound := h.stackBound,
    stackFits := h.stackFits, stack := h.stack, heapPerm := h.heapPerm, heap := h.heap, stackHeap := h.stackHeap,
    owned := h.owned.frame rfl rfl rfl rfl (fun _ _ _ _ => rfl),
    text := h.text,
    sp := h.sp }

/-- The last byte of a block's text lies outside any run of bytes of the
stack region. -/
theorem text_outside_stack {lo cnt : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hle : lo + cnt ≤ stackSize Γ) (hc : 0 < cnt) {b : BitVec 64} {l' : Layout}
    (hl' : Ψ b = some l') :
    BitVec.ofNat 64 cnt ≤
      (b + BitVec.ofNat 64 (l'.size - 1)) - (stackBase Γ s + BitVec.ofNat 64 lo) := by
  have hpos := hΨ.nonempty b l' hl'
  have hd := (h.stackHeap b l' hl').mono (o := lo) (p := l'.size - 1) (n' := cnt)
    (m' := 1) h.stackSize_lt (hΨ.size_lt b l' hl') hle (by omega) hc (by omega)
  exact hd.1 (by decide)

/-- Eight bytes of an owned block lie apart from any run of bytes of a block
of the memory typing. -/
theorem owned_bytes_apart {a : BitVec 64} {l : Layout} {lo cnt : Nat}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hl : Ψ a = some l)
    (hle : lo + cnt ≤ l.shape.size) (hc : 0 < cnt) {b : BitVec 64 × Shape}
    (hb : b ∈ Γ.owned) {j : Nat} (hj : j + 8 ≤ b.2.size) :
    Disjoint (a + BitVec.ofNat 64 lo) cnt (b.1 + BitVec.ofNat 64 j) 8 :=
  (h.owned.heap b hb a l hl).symm.mono (o := lo) (p := j) (n' := cnt) (m' := 8)
    (hΨ.size_lt a l hl) (h.owned.size_lt b hb) (by simp only [Layout.size]; omega) (by omega)
    (by omega) (by omega)

/-- Eight bytes of an owned block lie apart from any run of bytes of the
stack region. -/
theorem owned_stack_apart {lo cnt : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hle : lo + cnt ≤ stackSize Γ) (hc : 0 < cnt) {b : BitVec 64 × Shape}
    (hb : b ∈ Γ.owned) {j : Nat} (hj : j + 8 ≤ b.2.size) :
    Disjoint (stackBase Γ s + BitVec.ofNat 64 lo) cnt (b.1 + BitVec.ofNat 64 j) 8 :=
  (h.owned.stack b hb).mono (o := lo) (p := j) (n' := cnt) (m' := 8)
    h.stackSize_lt (h.owned.size_lt b hb) hle (by omega) hc (by omega)

/-- The byte of text a register points at is readable. -/
theorem canRead_text {b : Reg} {more : Bool} (h : WellTyped fetch sys Ψ ix Γ s) (hb : b ≠ .rsp)
    (hΓ : Γ.regs b = .str more) : s.canRead (s.ea (.sib (some b) none 0)) 1 = true := by
  have hp := h.regs b hb
  rw [hΓ] at hp
  obtain ⟨a, l, off, hl, hoff, hva⟩ := hasTy_str.mp hp
  have hea : s.ea (.sib (some b) none 0) = a + BitVec.ofNat 64 (l.shape.size + off) := by
    simp [State.ea, hva]
  rw [hea]
  exact State.canRead_sub (h.heapPerm a l hl).1 (by simp only [Layout.size]; omega)

/-- Bytes inside a block's shape are readable. -/
theorem canRead_bytes {a : BitVec 64} {l : Layout} {lo m : Nat}
    (h : WellTyped fetch sys Ψ ix Γ s) (hl : Ψ a = some l) (hi : lo + m ≤ l.shape.size) :
    s.canRead (a + BitVec.ofNat 64 lo) m = true :=
  State.canRead_sub (h.heapPerm a l hl).1 (by simp only [Layout.size]; omega)

/-- Bytes inside a writable block's shape are writable. -/
theorem canWrite_bytes {a : BitVec 64} {l : Layout} {lo m : Nat}
    (h : WellTyped fetch sys Ψ ix Γ s) (hl : Ψ a = some l) (hw : l.writable = true)
    (hi : lo + m ≤ l.shape.size) : s.canWrite (a + BitVec.ofNat 64 lo) m = true :=
  State.canWrite_sub ((h.heapPerm a l hl).2 hw) (by simp only [Layout.size]; omega)

/-- Bytes of the described stack, at and above the stack pointer, are writable. -/
theorem canWrite_stack {lo m : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hle : lo + m ≤ stackLen Γ.stack) :
    s.canWrite (s.getReg .rsp + BitVec.ofNat 64 lo) m = true := by
  have := State.canWrite_sub h.stackPerm (o := Γ.room + lo) (m := m)
    (by simp only [stackSize]; omega)
  rwa [slot_addr] at this

/-- Bytes of a piece of the stack are writable. -/
theorem canWrite_piece {k i m : Nat} {S : Shape} (h : WellTyped fetch sys Ψ ix Γ s)
    (hk : Γ.stack[k]? = some S) (hi : i + m ≤ S.size) :
    s.canWrite (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) m = true :=
  h.canWrite_stack (by have := stackOff_add_le hk; omega)

/-- When there is room, the bytes below `rsp` are writable. -/
theorem canWrite_below {m n : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hroom : Γ.room = m + n) :
    s.canWrite (s.getReg .rsp - BitVec.ofNat 64 n) n = true := by
  have := State.canWrite_sub h.stackPerm (o := m) (m := n)
    (by simp only [stackSize, hroom]; omega)
  have e : stackBase Γ s + BitVec.ofNat 64 m = s.getReg .rsp - BitVec.ofNat 64 n := by
    simp only [stackBase, hroom]; bv_omega
  rwa [e] at this

theorem canWrite_push {n : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hroom : Γ.room = n + 8) :
    s.canWrite (s.getReg .rsp - 8) 8 = true :=
  h.canWrite_below hroom

/-- A value shifted by a known amount has the shifted type. -/
theorem _root_.TypedAsm.HasTy.shift {τ : Ty} {v : BitVec 64} (hv : HasTy fetch sys Ψ ix τ v)
    (d : BitVec 64) : HasTy fetch sys Ψ ix (τ.shift d) (v + d) := by
  cases τ with
  | eq x => exact hasTy_eq.mpr (by rw [hasTy_eq.mp hv])
  | _ => exact HasTy.int _

/-- A context that differs only in the stack pointer's type is matched as
soon as the stack pointer has that type. -/
theorem setSp {Γ' : Ctx} (h : WellTyped fetch sys Ψ ix Γ s)
    (hregs : ∀ r, r ≠ .rsp → Γ'.regs r = Γ.regs r) (hstack : Γ'.stack = Γ.stack)
    (hroom : Γ'.room = Γ.room) (hflags : Γ'.flags = Γ.flags)
    (hv : HasTy fetch sys Ψ ix (Γ'.regs .rsp) (s.getReg .rsp))
    (howned : Γ'.owned = Γ.owned := by rfl) (habove : Γ'.above = Γ.above := by rfl) :
    WellTyped fetch sys Ψ ix Γ' s :=
  { regs := fun r hr => by rw [hregs r hr]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by
      have := h.stackPerm
      simpa only [stackBase, stackSize, hstack, hroom] using this
    stackBound := by
      have := h.stackBound
      simpa only [stackSize, hstack, hroom, habove] using this
    stackFits := by rw [hstack]; exact h.stackFits
    stack := by rw [hstack]; exact h.stack
    heapPerm := h.heapPerm
    heap := h.heap
    stackHeap := fun a l hl => by
      have := h.stackHeap a l hl
      simpa only [stackBase, stackSize, hstack, hroom] using this
    owned := h.owned.frame howned rfl (by simp only [stackBase, hroom])
      (by simp only [stackSize, hstack, hroom]) (fun _ _ _ _ => rfl)
    text := h.text
    sp := hv }

/-- **The stack grows by a piece.** The stack pointer moves down by the
piece's size, into the free room, and nothing outside those bytes changes;
what the piece says of them must hold afterwards. A `push`, a `call` and
making room for locals are each this. -/
theorem growStack {s' : State} {X : Shape} {m : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hΨ : Ψ.WF) (hroom : Γ.room = m + X.size) (hX : ∀ p ∈ X.vals, p.1 + 8 ≤ X.size)
    (hsp : s'.getReg .rsp = s.getReg .rsp - BitVec.ofNat 64 X.size)
    (hregs : ∀ r, r ≠ .rsp → s'.getReg r = s.getReg r) (hflags : s'.flags = s.flags)
    (hperm : s'.perm = s.perm)
    (hframe : ∀ y, (0 < X.size →
      Disjoint (s.getReg .rsp - BitVec.ofNat 64 X.size) X.size y 8) → s'.load64 y = s.load64 y)
    (hmem : ∀ x, (0 < X.size →
      BitVec.ofNat 64 X.size ≤ x - (s.getReg .rsp - BitVec.ofNat 64 X.size)) →
      s'.mem x = s.mem x)
    (hvals : ∀ p ∈ X.vals,
      HasTy fetch sys Ψ ix p.2 (s'.load64 (s'.getReg .rsp + BitVec.ofNat 64 p.1))) :
    WellTyped fetch sys Ψ ix
      { Γ.moveSp (-BitVec.ofNat 64 X.size) with stack := X :: Γ.stack, room := m } s' := by
  have hz : stackSize { Γ.moveSp (-BitVec.ofNat 64 X.size) with stack := X :: Γ.stack, room := m }
      = stackSize Γ := by
    simp only [stackSize, stackLen, hroom]; omega
  have hlt := h.stackSize_lt
  simp only [stackSize, hroom] at hlt
  have hb : stackBase { Γ.moveSp (-BitVec.ofNat 64 X.size) with stack := X :: Γ.stack, room := m }
      s' = stackBase Γ s := by
    simp only [stackBase, hsp, hroom]; bv_omega
  have htop : stackBase Γ s + BitVec.ofNat 64 m = s.getReg .rsp - BitVec.ofNat 64 X.size := by
    simp only [stackBase, hroom]; bv_omega
  exact {
    regs := fun r hr => by
      rw [hregs r hr]
      show HasTy fetch sys Ψ ix ((Γ.moveSp _).regs r) _
      rw [CtxOf.moveSp_regs hr]
      exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by rw [hb, hz, State.canWrite_congr hperm]; exact h.stackPerm
    stackBound := by rw [hz]; exact h.stackBound
    stackFits := fun S hS p hp => by
      rcases List.mem_cons.mp hS with rfl | hS
      · exact hX p hp
      · exact h.stackFits S hS p hp
    stack := fun k S hk p hp => by
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [stackOff, Nat.zero_add]
        exact hvals p hp
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        have hin := h.stack_in hk hp
        have e : s'.getReg .rsp + BitVec.ofNat 64 (stackOff (X :: Γ.stack) (k + 1) + p.1)
            = s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + p.1) := by
          simp only [stackOff, hsp]; bv_omega
        rw [e, hframe _ (fun hc => by
          refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega)]
        exact h.stack k S hk p hp
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' p hp => by
      have hpf := hΨ.fits b l' hl' p hp
      rw [hframe _ (fun hc => by
        have hd := (h.stackHeap b l' hl').mono (o := m) (p := p.1) (n' := X.size) (m' := 8)
          h.stackSize_lt (hΨ.size_lt b l' hl') (by simp only [stackSize, hroom]; omega)
          (by simp only [Layout.size]; omega) hc (by omega)
        rwa [htop] at hd)]
      exact h.heap b l' hl' p hp
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl'
    owned := h.owned.frame rfl hperm hb hz (fun b hb' j hj =>
      hframe _ (fun hc => by
        have hd := h.owned_stack_apart (lo := m) (cnt := X.size)
          (by simp only [stackSize, hroom]; omega) hc hb' hj
        rwa [htop] at hd))
    text := fun b l' hl' ht => by
      rw [hmem _ (fun hc => by
        have hout := h.text_outside_stack hΨ (lo := m) (cnt := X.size)
          (by simp only [stackSize, hroom]; omega) hc hl'
        rwa [htop] at hout)]
      exact h.text b l' hl' ht
    sp := by
      show HasTy fetch sys Ψ ix ((Γ.moveSp _).regs .rsp) _
      rw [CtxOf.moveSp_sp, hsp, BitVec.sub_eq_add_neg]
      exact h.sp.shift _ }

/-- **The stack shrinks by the pieces at its top.** The stack pointer moves
up past them and they become free room; nothing changes in memory. A `pop`,
a `ret` and giving up locals are each this. -/
theorem shrinkStack {top rest : List Shape} {k : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hst : Γ.stack = top ++ rest) (hk : stackLen top = k) :
    WellTyped fetch sys Ψ ix
      { Γ.moveSp (BitVec.ofNat 64 k) with stack := rest, room := Γ.room + k }
      (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 k)) := by
  have hm : (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 k)).mem = s.mem := rfl
  have hp : (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 k)).perm = s.perm := rfl
  have hsp : (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 k)).getReg .rsp
      = s.getReg .rsp + BitVec.ofNat 64 k := State.getReg_setReg_same _ _ _
  have hz : stackSize { Γ.moveSp (BitVec.ofNat 64 k) with stack := rest, room := Γ.room + k }
      = stackSize Γ := by
    simp only [stackSize, hst, stackLen_append, hk]; omega
  have hlt := h.stackSize_lt
  simp only [stackSize, hst, stackLen_append, hk] at hlt
  have hb : stackBase { Γ.moveSp (BitVec.ofNat 64 k) with stack := rest, room := Γ.room + k }
      (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 k)) = stackBase Γ s := by
    simp only [stackBase, hsp]; bv_omega
  exact {
    regs := fun r hr => by
      rw [State.getReg_setReg_other s .rsp r _ hr]
      show HasTy fetch sys Ψ ix ((Γ.moveSp _).regs r) _
      rw [CtxOf.moveSp_regs hr]
      exact h.regs r hr
    flags := h.flags
    stackPerm := by rw [hb, hz, State.canWrite_congr hp]; exact h.stackPerm
    stackBound := by rw [hz]; exact h.stackBound
    stackFits := fun S hS p hp' =>
      h.stackFits S (by rw [hst]; exact List.mem_append_right _ hS) p hp'
    stack := fun j S hj p hp' => by
      have hj' : Γ.stack[top.length + j]? = some S := by
        rw [hst, List.getElem?_append_right (by omega)]
        simpa using hj
      have ho : stackOff Γ.stack (top.length + j) = k + stackOff rest j := by
        rw [hst, stackOff_append, hk]
      have e : s.getReg .rsp + BitVec.ofNat 64 k + BitVec.ofNat 64 (stackOff rest j + p.1)
          = s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack (top.length + j) + p.1) := by
        rw [ho]; bv_omega
      rw [hsp, State.load64_congr hm, e]
      exact h.stack (top.length + j) S hj' p hp'
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' p hp' => by
      rw [State.load64_congr hm]; exact h.heap b l' hl' p hp'
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl'
    owned := h.owned.frame rfl hp hb hz (fun b _ i _ => State.load64_congr hm _)
    text := fun a l hl ht => by rw [hm]; exact h.text a l hl ht
    sp := by
      show HasTy fetch sys Ψ ix ((Γ.moveSp _).regs .rsp) _
      rw [CtxOf.moveSp_sp, hsp]
      exact h.sp.shift _ }

/-- After a push: the pushed value is on top, and the stack pointer is 8 lower. -/
theorem push {n : Nat} {τ : Ty} {v : BitVec 64} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hroom : Γ.room = n + 8) (hv : HasTy fetch sys Ψ ix τ v) :
    WellTyped fetch sys Ψ ix { Γ.moveSp (-8) with stack := .slot τ :: Γ.stack, room := n }
      ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v) := by
  have hm : (s.setReg .rsp (s.getReg .rsp - 8)).mem = s.mem := rfl
  have hg : ∀ r, ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v).getReg r
      = (s.setReg .rsp (s.getReg .rsp - 8)).getReg r :=
    fun r => by simp only [State.getReg, State.store64_regs]
  refine h.growStack hΨ (X := .slot τ) hroom (fun p hp => ?_) ?_ (fun r hr => ?_)
    (State.store64_flags _ _ _) (State.store64_perm _ _ _) (fun y hy => ?_) (fun x hx => ?_)
    (fun p hp => ?_)
  · simp only [ShapeOf.slot, List.mem_singleton] at hp
    subst hp
    exact Nat.le_refl _
  · rw [hg, State.getReg_setReg_same]; rfl
  · rw [hg, State.getReg_setReg_other s .rsp r _ hr]
  · exact (State.load64_store64_disjoint _ v (hy (Nat.succ_pos 7))).trans (State.load64_congr hm _)
  · exact State.mem_store_of_disjoint (s.setReg .rsp (s.getReg .rsp - 8)) .w64 _ _ v
      (hx (Nat.succ_pos 7))
  · simp only [ShapeOf.slot, List.mem_singleton] at hp
    subst hp
    rw [hg, State.getReg_setReg_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [State.load64_store64_same]
    exact hv

/-- After a pop of eight bytes, whatever they hold: the stack pointer is 8 higher. -/
theorem popAny {S : Shape} {σ : List Shape} (h : WellTyped fetch sys Ψ ix Γ s)
    (hst : Γ.stack = S :: σ) (h8 : S.size = 8) :
    WellTyped fetch sys Ψ ix { Γ.moveSp 8 with stack := σ, room := Γ.room + 8 }
      (s.setReg .rsp (s.getReg .rsp + 8)) :=
  h.shrinkStack (top := [S]) (rest := σ) (k := 8) hst (by simp [stackLen, h8])

/-- After a pop: the popped value had the type of the typed value on top,
and the stack pointer is 8 higher. -/
theorem pop {τ : Ty} {σ : List Shape} (h : WellTyped fetch sys Ψ ix Γ s)
    (hst : Γ.stack = .slot τ :: σ) :
    HasTy fetch sys Ψ ix τ (s.load64 (s.getReg .rsp)) ∧
    WellTyped fetch sys Ψ ix { Γ.moveSp 8 with stack := σ, room := Γ.room + 8 }
      (s.setReg .rsp (s.getReg .rsp + 8)) := by
  refine ⟨?_, h.popAny hst rfl⟩
  have := h.stack 0 (.slot τ) (by simp [hst]) (0, τ) (by simp [ShapeOf.slot])
  simpa [stackOff] using this

/-- Eight bytes at the top of the stack are readable and writable. -/
theorem canWrite_top {S : Shape} {σ : List Shape} (h : WellTyped fetch sys Ψ ix Γ s)
    (hst : Γ.stack = S :: σ) (h8 : S.size = 8) : s.canWrite (s.getReg .rsp) 8 = true := by
  have := h.canWrite_stack (lo := 0) (m := 8) (by simp only [hst, stackLen, h8]; omega)
  simpa using this

theorem allocFrame {k m : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hroom : Γ.room = m + k) :
    WellTyped fetch sys Ψ ix
      { Γ.moveSp (-BitVec.ofNat 64 k) with stack := .raw k :: Γ.stack, room := m }
      (s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 k)) :=
  h.growStack hΨ (X := .raw k) hroom (fun p hp => by cases hp)
    (State.getReg_setReg_same _ _ _) (fun r hr => State.getReg_setReg_other s .rsp r _ hr) rfl
    rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun p hp => by cases hp)

theorem freeFrame {k : Nat} {top rest : List Shape} (h : WellTyped fetch sys Ψ ix Γ s)
    (hst : Γ.stack = top ++ rest) (hk : stackLen top = k) :
    WellTyped fetch sys Ψ ix
      { Γ.moveSp (BitVec.ofNat 64 k) with stack := rest, room := Γ.room + k }
      (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 k)) :=
  h.shrinkStack hst hk

/-- Two different owned blocks do not overlap. -/
theorem owned_apart {m k : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hm : m < Γ.owned.length)
    (hk : k < Γ.owned.length) (hne : m ≠ k) :
    Disjoint Γ.owned[k].1 Γ.owned[k].2.size Γ.owned[m].1 Γ.owned[m].2.size := by
  have hp := List.pairwise_iff_getElem.mp h.owned.apart
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact (hp m k hm hk hlt).symm
  · exact hp k m hk hm hgt

/-- Within one region, a run of bytes does not overlap eight bytes that keep
clear of it. -/
theorem disjoint_bytes {a : BitVec 64} {lo cnt p N : Nat} (hc : 0 < cnt)
    (hout : p + 8 ≤ lo ∨ lo + cnt ≤ p) (hr : lo + cnt ≤ N) (hp : p + 8 ≤ N) (hN : N < 2 ^ 64) :
    Disjoint (a + BitVec.ofNat 64 lo) cnt (a + BitVec.ofNat 64 p) 8 := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega

/-- **A change confined to a run of bytes of a block of the memory typing
keeps the state well typed**, provided each typed value of the block either
keeps clear of the run or is of its type afterwards. -/
theorem writeHeap {a : BitVec 64} {l : Layout} {lo cnt : Nat} {s' : State}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hl : Ψ a = some l)
    (hle : lo + cnt ≤ l.shape.size)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 lo) cnt y 8 → s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤ x - (a + BitVec.ofNat 64 lo) → s'.mem x = s.mem x)
    (hvals : ∀ p ∈ l.shape.vals, (p.1 + 8 ≤ lo ∨ lo + cnt ≤ p.1) ∨
      HasTy fetch sys Ψ ix p.2 (s'.load64 (a + BitVec.ofNat 64 p.1))) :
    WellTyped fetch sys Ψ ix Γ s' := by
  have hsz := hΨ.size_lt a l hl
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hb : stackBase Γ s' = stackBase Γ s := by simp only [stackBase, hg]
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
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by rw [hb, State.canWrite_congr hperm]; exact h.stackPerm
    stackBound := h.stackBound
    stackFits := h.stackFits
    stack := fun k S hk p hp => by
      have hpf := h.stack_in hk hp
      rw [hg, hF _ (fun hc => by
        have hd := (h.stackHeap a l hl).symm.mono (o := lo) (p := Γ.room + (stackOff Γ.stack k + p.1))
          (n' := cnt) (m' := 8) hsz h.stackSize_lt (by simp only [Layout.size]; omega)
          (by simp only [stackSize]; omega) (by omega) (by omega)
        rw [slot_addr] at hd
        exact hd)]
      exact h.stack k S hk p hp
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' p hp => by
      have hpf := hΨ.fits b l' hl' p hp
      by_cases hab : b = a
      · subst hab
        have e : l' = l := Option.some.inj (hl'.symm.trans hl)
        subst e
        rcases hvals p hp with hout | hnew
        · rw [hF _ (fun hc => disjoint_bytes (N := l'.size) hc hout
            (by simp only [Layout.size]; omega) (by simp only [Layout.size]; omega) hsz)]
          exact h.heap b l' hl' p hp
        · exact hnew
      · rw [hF _ (fun hc => (hΨ.disjoint a b l l' hl hl' (Ne.symm hab)).mono (o := lo)
          (p := p.1) (n' := cnt) (m' := 8) hsz (hΨ.size_lt b l' hl')
          (by simp only [Layout.size]; omega) (by simp only [Layout.size]; omega) hc (by omega))]
        exact h.heap b l' hl' p hp
    stackHeap := fun b l' hl' => by rw [hb]; exact h.stackHeap b l' hl'
    owned := h.owned.frame rfl hperm hb rfl (fun b hb' j hj =>
      hF _ (fun hc => h.owned_bytes_apart hΨ hl hle hc hb' hj))
    text := fun b l' hl' ht => by
      rw [hM _ (fun hc => hΨ.text_outside_bytes hl hle hc hl' ht)]
      exact h.text b l' hl' ht
    sp := by rw [hg]; exact h.sp }

/-- A change confined to plain bytes of a block keeps the state well typed. -/
theorem writeHeapFree {a : BitVec 64} {l : Layout} {lo cnt : Nat} {s' : State}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hl : Ψ a = some l)
    (hle : lo + cnt ≤ l.shape.size) (hfree : l.shape.free lo cnt = true)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 lo) cnt y 8 → s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤ x - (a + BitVec.ofNat 64 lo) → s'.mem x = s.mem x) :
    WellTyped fetch sys Ψ ix Γ s' :=
  h.writeHeap hΨ hl hle hregs hflags hperm hframe hmem
    (fun p hp => .inl (ShapeOf.clearOf_of_free hfree p hp))

/-- Storing a value of its type over a typed value of a block, where no
other typed value reaches into those eight bytes. -/
theorem storeHeap {a : BitVec 64} {l : Layout} {o : Nat} {τ : Ty} {v : BitVec 64}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hl : Ψ a = some l)
    (hi : l.shape.valAt o = some τ) (hso : l.shape.sole o = true)
    (hv : HasTy fetch sys Ψ ix τ v) :
    WellTyped fetch sys Ψ ix Γ (s.store64 (a + BitVec.ofNat 64 o) v) := by
  have hm := ShapeOf.mem_of_valAt hi
  have hof := hΨ.fits a l hl _ hm
  refine h.writeHeap hΨ hl (lo := o) (cnt := 8) hof (State.store64_regs _ _ _)
    (State.store64_flags _ _ _) (State.store64_perm _ _ _)
    (fun y hd => State.load64_store64_disjoint s v hd)
    (fun x hx => State.mem_store_of_disjoint s .w64 _ _ v hx) (fun p hp => ?_)
  by_cases hc : p.1 + 8 ≤ o ∨ o + 8 ≤ p.1
  · exact .inl hc
  · have e : p = (o, τ) := ShapeOf.eq_of_sole hso hp hm hc (by omega)
    subst e
    right
    rw [State.load64_store64_same]
    exact hv

/-- **A change confined to a run of bytes of an owned block keeps the state
well typed**, with the block described by any shape of the same size whose
typed values either were there before and keep clear of the run, or are of
their type now. Nothing else can be looking at the block: this is what owning
it buys. -/
theorem writeOwned {s' : State} {k : Nat} {a : BitVec 64} {S S' : Shape} {lo cnt : Nat}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hk : Γ.owned[k]? = some (a, S))
    (hle : lo + cnt ≤ S.size) (hS' : S'.size = S.size)
    (hfits : ∀ p ∈ S'.vals, p.1 + 8 ≤ S'.size)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 lo) cnt y 8 → s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤ x - (a + BitVec.ofNat 64 lo) → s'.mem x = s.mem x)
    (hvals : ∀ p ∈ S'.vals, (p ∈ S.vals ∧ (p.1 + 8 ≤ lo ∨ lo + cnt ≤ p.1)) ∨
      HasTy fetch sys Ψ ix p.2 (s'.load64 (a + BitVec.ofNat 64 p.1))) :
    WellTyped fetch sys Ψ ix { Γ with owned := Γ.owned.set k (a, S') } s' := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
  have hsz := h.owned.size_lt _ hin
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
  have hb : stackBase { Γ with owned := Γ.owned.set k (a, S') } s' = stackBase Γ s := by
    simp only [stackBase, hg]
  -- the block is apart from the stack and from the memory typing's blocks
  have hst := h.owned.stack _ hin
  have hhp := h.owned.heap _ hin
  simp only at hst hhp
  -- an entry of the new list is the old one at its place, but for the shape of this block
  have hlen : (Γ.owned.set k (a, S')).length = Γ.owned.length := List.length_set
  have hentry : ∀ m (hm : m < Γ.owned.length),
      (Γ.owned.set k (a, S'))[m]'(hlen ▸ hm) = if k = m then (a, S') else Γ.owned[m] :=
    fun m hm => List.getElem_set _
  have hkey : ∀ m (hm : m < Γ.owned.length),
      ((Γ.owned.set k (a, S'))[m]'(hlen ▸ hm)).1 = Γ.owned[m].1 ∧
      ((Γ.owned.set k (a, S'))[m]'(hlen ▸ hm)).2.size = Γ.owned[m].2.size := by
    intro m hm
    rw [hentry m hm]
    split
    · next e => subst e; rw [hkeq]; exact ⟨rfl, hS'⟩
    · exact ⟨rfl, rfl⟩
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by rw [hb, State.canWrite_congr hperm]; exact h.stackPerm
    stackBound := h.stackBound
    stackFits := h.stackFits
    stack := fun k S hk p hp => by
      have hpf := h.stack_in hk hp
      rw [hg, hF _ (fun hc => by
        have hd := hst.symm.mono (o := lo) (p := Γ.room + (stackOff Γ.stack k + p.1)) (n' := cnt) (m' := 8)
          hsz h.stackSize_lt (by omega) (by simp only [stackSize]; omega) (by omega) (by omega)
        rw [slot_addr] at hd
        exact hd)]
      exact h.stack k S hk p hp
    heapPerm := fun b l hl => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l hl
    heap := fun b l hl p hp => by
      have hpf := hΨ.fits _ l (by assumption) p hp
      rw [hF _ (fun hc => (hhp b l hl).mono (o := lo) (p := p.1) (n' := cnt) (m' := 8)
        hsz (hΨ.size_lt b l hl) (by omega) (by simp only [Layout.size]; omega) (by omega)
        (by omega))]
      exact h.heap b l hl p hp
    stackHeap := fun b l hl => by rw [hb]; exact h.stackHeap b l hl
    sp := by rw [hg]; exact h.sp
    text := fun b l hl ht => by
      have hpos := hΨ.nonempty b l hl
      rw [hM _ (fun hc => ((hhp b l hl).mono (o := lo) (p := l.size - 1) (n' := cnt) (m' := 1)
        hsz (hΨ.size_lt b l hl) (by omega) (by omega) (by omega) (by omega)).1 (by decide))]
      exact h.text b l hl ht
    owned := {
      perm := fun c hc' => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.owned.length := hlen ▸ hm
        rw [(hkey m hm').1, (hkey m hm').2, State.canWrite_congr hperm]
        exact h.owned.perm _ (List.getElem_mem hm')
      size_lt := fun c hc' => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.owned.length := hlen ▸ hm
        rw [(hkey m hm').2]
        exact h.owned.size_lt _ (List.getElem_mem hm')
      fits := fun c hc' p hp => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.owned.length := hlen ▸ hm
        have he := hentry m hm'
        by_cases hmk : k = m
        · subst hmk
          simp only [↓reduceIte] at he
          rw [he] at hp ⊢
          exact hfits p hp
        · simp only [hmk, ↓reduceIte] at he
          rw [he] at hp ⊢
          exact h.owned.fits _ (List.getElem_mem hm') p hp
      vals := fun c hc' p hp => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.owned.length := hlen ▸ hm
        by_cases hmk : k = m
        · -- this block: values clear of the run are as before, the others are new
          subst hmk
          have he := hentry k hm'
          simp only [↓reduceIte] at he
          rw [he] at hp ⊢
          simp only at hp ⊢
          rcases hvals p hp with ⟨hold, hout⟩ | hnew
          · have hpf := h.owned.fits _ hin p hold
            simp only at hpf
            rw [hF _ (fun hc => disjoint_bytes hc hout hle hpf hsz)]
            exact h.owned.vals _ hin p hold
          · exact hnew
        · -- another block: untouched
          have he := hentry m hm'
          simp only [hmk, ↓reduceIte] at he
          rw [he] at hp ⊢
          have hd := (h.owned_apart hm' hklt (Ne.symm hmk))
          rw [hkeq] at hd
          simp only at hd
          have hpf := h.owned.fits _ (List.getElem_mem hm') p hp
          rw [hF _ (fun hc => hd.mono (o := lo) (p := p.1) (n' := cnt) (m' := 8) hsz
            (h.owned.size_lt _ (List.getElem_mem hm')) (by omega) hpf (by omega) (by omega))]
          exact h.owned.vals _ (List.getElem_mem hm') p hp
      stack := fun c hc' => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.owned.length := hlen ▸ hm
        rw [(hkey m hm').1, (hkey m hm').2, hb]
        exact h.owned.stack _ (List.getElem_mem hm')
      heap := fun c hc' b l hl => by
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc'
        have hm' : m < Γ.owned.length := hlen ▸ hm
        rw [(hkey m hm').1, (hkey m hm').2]
        exact h.owned.heap _ (List.getElem_mem hm') b l hl
      apart := by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        have hi' : i < Γ.owned.length := hlen ▸ hi
        have hj' : j < Γ.owned.length := hlen ▸ hj
        rw [(hkey i hi').1, (hkey i hi').2, (hkey j hj').1, (hkey j hj').2]
        exact List.pairwise_iff_getElem.mp h.owned.apart i j hi' hj' hij } }

/-- A block that is writable, holds what its field types say, and overlaps
nothing the context or the memory typing describes may be added to the
blocks the context owns. -/
theorem addOwned {b : BitVec 64 × Shape} (h : WellTyped fetch sys Ψ ix Γ s)
    (hperm : s.canWrite b.1 b.2.size = true) (hlt : b.2.size < 2 ^ 64)
    (hfits : ∀ p ∈ b.2.vals, p.1 + 8 ≤ b.2.size)
    (hvals : ∀ p ∈ b.2.vals, HasTy fetch sys Ψ ix p.2 (s.load64 (b.1 + BitVec.ofNat 64 p.1)))
    (hstack : Disjoint (stackBase Γ s) (stackSize Γ) b.1 b.2.size)
    (hheap : ∀ a l, Ψ a = some l → Disjoint b.1 b.2.size a l.size)
    (hapart : ∀ c ∈ Γ.owned, Disjoint b.1 b.2.size c.1 c.2.size) :
    WellTyped fetch sys Ψ ix { Γ with owned := b :: Γ.owned } s :=
  { regs := h.regs, flags := h.flags, stackPerm := h.stackPerm, stackBound := h.stackBound,
    stackFits := h.stackFits, stack := h.stack, heapPerm := h.heapPerm, heap := h.heap, stackHeap := h.stackHeap,
    sp := h.sp, text := h.text,
    owned :=
      { perm := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hperm
          · exact h.owned.perm c hc
        size_lt := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hlt
          · exact h.owned.size_lt c hc
        fits := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hfits
          · exact h.owned.fits c hc
        vals := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hvals
          · exact h.owned.vals c hc
        stack := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hstack
          · exact h.owned.stack c hc
        heap := fun c hc a l hl => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hheap a l hl
          · exact h.owned.heap c hc a l hl
        apart := List.pairwise_cons.mpr ⟨hapart, h.owned.apart⟩ } }

/-- A range that some block is apart from keeps its permissions across a
change that touches permissions only inside that block. -/
theorem _root_.TypedAsm.State.canWrite_apart {s s' : State} {a b : BitVec 64} {n m : Nat}
    (hd : Disjoint a n b m) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (hperm : ∀ x, s'.perm x = s.perm x ∨ (x - a).toNat < n)
    (hw : s.canWrite b m = true) : s'.canWrite b m = true := by
  rw [State.canWrite_iff] at hw ⊢
  intro i hi
  rcases hperm (b + BitVec.ofNat 64 i) with he | hin
  · rw [he]; exact hw i hi
  · have hd' := hd.of_pos (by omega) (by omega)
    exact absurd hin (by bv_omega)

theorem _root_.TypedAsm.State.canRead_apart {s s' : State} {a b : BitVec 64} {n m : Nat}
    (hd : Disjoint a n b m) (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (hperm : ∀ x, s'.perm x = s.perm x ∨ (x - a).toNat < n)
    (hr : s.canRead b m = true) : s'.canRead b m = true := by
  rw [State.canRead_iff] at hr ⊢
  intro i hi
  rcases hperm (b + BitVec.ofNat 64 i) with he | hin
  · rw [he]; exact hr i hi
  · have hd' := hd.of_pos (by omega) (by omega)
    exact absurd hin (by bv_omega)

/-- **An owned block may be given up.** The context without it still
describes the state, even if the block's memory has meanwhile become
inaccessible: nothing else the context describes overlaps it. -/
theorem eraseOwned {s' : State} {k : Nat} {a : BitVec 64} {S : Shape}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hk : Γ.owned[k]? = some (a, S))
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hmem : s'.mem = s.mem)
    (hperm : ∀ x, s'.perm x = s.perm x ∨ (x - a).toNat < S.size) :
    WellTyped fetch sys Ψ ix { Γ with owned := Γ.owned.eraseIdx k } s' := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
  have hsz := h.owned.size_lt _ hin
  have hst := h.owned.stack _ hin
  have hhp := h.owned.heap _ hin
  simp only at hsz hst hhp
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hb : stackBase { Γ with owned := Γ.owned.eraseIdx k } s' = stackBase Γ s := by
    simp only [stackBase, hg]
  have hsub : ∀ c ∈ Γ.owned.eraseIdx k, c ∈ Γ.owned :=
    fun c hc => (List.eraseIdx_sublist _ _).subset hc
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by
      rw [hb]
      exact State.canWrite_apart hst.symm hsz h.stackSize_lt hperm h.stackPerm
    stackBound := h.stackBound
    stackFits := h.stackFits
    stack := fun k S hk p hp => by rw [hg, State.load64_congr hmem]; exact h.stack k S hk p hp
    heapPerm := fun b l hl =>
      ⟨State.canRead_apart (hhp b l hl) hsz (hΨ.size_lt b l hl) hperm (h.heapPerm b l hl).1,
        fun hw => State.canWrite_apart (hhp b l hl) hsz (hΨ.size_lt b l hl) hperm
          ((h.heapPerm b l hl).2 hw)⟩
    heap := fun b l hl p hp => by rw [State.load64_congr hmem]; exact h.heap b l hl p hp
    stackHeap := fun b l hl => by rw [hb]; exact h.stackHeap b l hl
    sp := by rw [hg]; exact h.sp
    text := fun b l hl ht => by rw [hmem]; exact h.text b l hl ht
    owned := {
      perm := fun c hc => by
        obtain ⟨m, hm, hmk, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hc
        have hd := h.owned_apart hm hklt hmk
        rw [hkeq] at hd
        simp only at hd
        exact State.canWrite_apart hd hsz (h.owned.size_lt _ (List.getElem_mem hm)) hperm
          (h.owned.perm _ (List.getElem_mem hm))
      size_lt := fun c hc => h.owned.size_lt c (hsub c hc)
      fits := fun c hc => h.owned.fits c (hsub c hc)
      vals := fun c hc p hp => by
        rw [State.load64_congr hmem]; exact h.owned.vals c (hsub c hc) p hp
      stack := fun c hc => by rw [hb]; exact h.owned.stack c (hsub c hc)
      heap := fun c hc => h.owned.heap c (hsub c hc)
      apart := h.owned.apart.sublist (List.eraseIdx_sublist _ _) } }

/-- A register may be given any type its current value has. -/
theorem retype {r : Reg} {τ : Ty} (h : WellTyped fetch sys Ψ ix Γ s) (hr : r ≠ .rsp)
    (hv : HasTy fetch sys Ψ ix τ (s.getReg r)) : WellTyped fetch sys Ψ ix (Γ.setReg r τ) s := by
  refine (h.setReg hr hv).congr ?_ rfl rfl rfl
  funext r'
  simp only [State.regs_setReg, State.getReg]
  split
  · next h' => rw [h']
  · rfl

/-- **A change confined to a run of bytes of one piece of the stack keeps the
state well typed**, with the piece described by any shape of the same size
whose typed values either were there before and keep clear of the run, or
are of their type now. -/
theorem writeStack {s' : State} {k : Nat} {S S' : Shape} {i cnt : Nat}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hk : Γ.stack[k]? = some S)
    (hle : i + cnt ≤ S.size) (hS' : S'.size = S.size)
    (hfits : ∀ p ∈ S'.vals, p.1 + 8 ≤ S'.size)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) cnt y 8 →
      s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤
      x - (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) → s'.mem x = s.mem x)
    (hvals : ∀ p ∈ S'.vals, (p ∈ S.vals ∧ (p.1 + 8 ≤ i ∨ i + cnt ≤ p.1)) ∨
      HasTy fetch sys Ψ ix p.2
        (s'.load64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + p.1)))) :
    WellTyped fetch sys Ψ ix { Γ with stack := Γ.stack.set k S' } s' := by
  have hklt : k < Γ.stack.length := (List.getElem?_eq_some_iff.mp hk).1
  have hkend := stackOff_add_le hk
  have hlt := h.stackSize_lt
  simp only [stackSize] at hlt
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hoff : ∀ j, stackOff (Γ.stack.set k S') j = stackOff Γ.stack j :=
    fun j => stackOff_set hk hS' j
  have hlen : stackLen (Γ.stack.set k S') = stackLen Γ.stack := stackLen_set hk hS'
  have hz : stackSize { Γ with stack := Γ.stack.set k S' } = stackSize Γ := by
    simp only [stackSize, hlen]
  have hb : stackBase { Γ with stack := Γ.stack.set k S' } s' = stackBase Γ s := by
    simp only [stackBase, hg]
  -- an empty run touches nothing, so nothing need be shown apart from it
  have hF : ∀ y, (0 < cnt →
      Disjoint (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) cnt y 8) →
      s'.load64 y = s.load64 y := fun y hy => by
    by_cases hc : 0 < cnt
    · exact hframe y (hy hc)
    · have e : cnt = 0 := by omega
      subst e
      exact hframe y ⟨fun _ => by bv_omega, fun h0 => absurd rfl h0⟩
  have hM : ∀ x, (0 < cnt → BitVec.ofNat 64 cnt ≤
      x - (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i))) →
      s'.mem x = s.mem x := fun x hx => by
    by_cases hc : 0 < cnt
    · exact hmem x (hx hc)
    · have e : cnt = 0 := by omega
      subst e
      exact hmem x (by bv_omega)
  have haddr : stackBase Γ s + BitVec.ofNat 64 (Γ.room + (stackOff Γ.stack k + i))
      = s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i) := slot_addr Γ s _
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by rw [hb, hz, State.canWrite_congr hperm]; exact h.stackPerm
    stackBound := by rw [hz]; exact h.stackBound
    stackFits := fun T hT p hp => by
      rcases List.mem_or_eq_of_mem_set hT with hT | rfl
      · exact h.stackFits T hT p hp
      · exact hfits p hp
    stack := fun j T hj p hp => by
      rw [hg, hoff]
      by_cases hjk : j = k
      · subst hjk
        have e : T = S' := by
          rw [List.getElem?_set_self hklt] at hj
          exact (Option.some.inj hj).symm
        subst e
        rcases hvals p hp with ⟨hold, hout⟩ | hnew
        · have hpf := h.stackFits S (List.mem_of_getElem? hk) p hold
          rw [hF _ (fun hc => by
            have := disjoint_bytes (a := s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack j))
              (N := S.size) hc hout hle hpf (by omega)
            rwa [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
              at this)]
          exact h.stack j S hk p hold
        · exact hnew
      · rw [List.getElem?_set_ne (Ne.symm hjk)] at hj
        have hpf := h.stackFits T (List.mem_of_getElem? hj) p hp
        have hjend := stackOff_add_le hj
        rw [hF _ (fun hc => by
          have hsep : stackOff Γ.stack j + p.1 + 8 ≤ stackOff Γ.stack k + i ∨
              stackOff Γ.stack k + i + cnt ≤ stackOff Γ.stack j + p.1 := by
            rcases Nat.lt_or_gt_of_ne hjk with hlt' | hgt
            · have := stackOff_le hlt' hj; omega
            · have := stackOff_le hgt hk; omega
          exact disjoint_bytes (N := stackLen Γ.stack) hc hsep (by omega) (by omega) (by omega))]
        exact h.stack j T hj p hp
    heapPerm := fun b l hl => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l hl
    heap := fun b l hl p hp => by
      have hpf := hΨ.fits b l hl p hp
      rw [hF _ (fun hc => by
        have hd := (h.stackHeap b l hl).mono (o := Γ.room + (stackOff Γ.stack k + i)) (p := p.1)
          (n' := cnt) (m' := 8) h.stackSize_lt (hΨ.size_lt b l hl)
          (by simp only [stackSize]; omega) (by simp only [Layout.size]; omega) hc (by omega)
        rwa [haddr] at hd)]
      exact h.heap b l hl p hp
    stackHeap := fun b l hl => by rw [hb, hz]; exact h.stackHeap b l hl
    owned := h.owned.frame rfl hperm hb hz (fun b hb' j hj =>
      hF _ (fun hc => by
        have hd := h.owned_stack_apart (lo := Γ.room + (stackOff Γ.stack k + i)) (cnt := cnt)
          (by simp only [stackSize]; omega) hc hb' hj
        rwa [haddr] at hd))
    text := fun b l hl ht => by
      rw [hM _ (fun hc => by
        have hout := h.text_outside_stack hΨ (lo := Γ.room + (stackOff Γ.stack k + i))
          (cnt := cnt) (by simp only [stackSize]; omega) hc hl
        rwa [haddr] at hout)]
      exact h.text b l hl ht
    sp := by rw [hg]; exact h.sp }

/-- A change confined to a run of bytes of a piece of the stack keeps the
state well typed, with whatever typed values reached into the run forgotten. -/
theorem writeStackClear {s' : State} {k : Nat} {S : Shape} {i cnt : Nat}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hk : Γ.stack[k]? = some S)
    (hle : i + cnt ≤ S.size)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) cnt y 8 →
      s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤
      x - (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) → s'.mem x = s.mem x) :
    WellTyped fetch sys Ψ ix { Γ with stack := Γ.stack.set k (S.clear i cnt) } s' :=
  h.writeStack hΨ hk (S' := S.clear i cnt) hle rfl
    (fun p hp => h.stackFits S (List.mem_of_getElem? hk) p (ShapeOf.mem_clear hp).1)
    hregs hflags hperm hframe hmem (fun _ hp => .inl (ShapeOf.mem_clear hp))

/-- Storing eight bytes into a piece of the stack: they take the stored
value's type. -/
theorem storeStack {k i : Nat} {S : Shape} {τ : Ty} {v : BitVec 64}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hk : Γ.stack[k]? = some S)
    (hle : i + 8 ≤ S.size) (hv : HasTy fetch sys Ψ ix τ v) :
    WellTyped fetch sys Ψ ix { Γ with stack := Γ.stack.set k (S.set i τ) }
      (s.store64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) v) := by
  refine h.writeStack hΨ hk (S' := S.set i τ) (cnt := 8) hle rfl (fun p hp => ?_)
    (State.store64_regs _ _ _) (State.store64_flags _ _ _) (State.store64_perm _ _ _)
    (fun y hd => State.load64_store64_disjoint s v hd)
    (fun x hx => State.mem_store_of_disjoint s .w64 _ _ v hx) (fun p hp => ?_)
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact hle
    · exact h.stackFits S (List.mem_of_getElem? hk) p (ShapeOf.mem_clear hp).1
  · rcases List.mem_cons.mp hp with rfl | hp
    · right
      rw [State.load64_store64_same]
      exact hv
    · exact .inl (ShapeOf.mem_clear hp)

/-- After a two-operand operation on register `d` that left known flags. -/
theorem afterAlu {op : AluOp} {d : Reg} {fl : Flags} (h : WellTyped fetch sys Ψ ix Γ s) (hd : d ≠ .rsp)
    (hdef : fl.defined = true) (v : BitVec 64) :
    WellTyped fetch sys Ψ ix (Γ.afterAlu op d)
      { (if op.writesDst then s.setReg d v else s) with flags := fl } := by
  cases hwd : op.writesDst
  · simp only [CtxOf.afterAlu, hwd, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
    exact h.setFlags (P := Flags.Known) hdef
  · simp only [CtxOf.afterAlu, hwd, Bool.cond_true, ↓reduceIte]
    exact (h.setReg hd (HasTy.int v)).setFlags (P := Flags.Known) hdef

end WellTyped

/-! ## What the typed instructions compute -/

theorem sext_small {m : Nat} (h : m < 2 ^ 31) :
    (BitVec.ofNat 32 m).signExtend 64 = BitVec.ofNat 64 m := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_ofNat]
    omega

namespace State

theorem read_w32 {s : State} {a : BitVec 64} (h : s.canRead a 4 = true) :
    s.read .w32 a = .next (s.load32 a) := by
  have h' : s.canRead a Width.w32.bytes.toNat = true := h
  simp only [read, h', ite_true]
  rfl

/-- The address `d` bytes on from a base register. -/
theorem ea_byte (s : State) (b : Reg) {d : Nat} {disp : BitVec 32} (h : byteDisp d disp) :
    s.ea (.sib (some b) none disp) = s.getReg b + BitVec.ofNat 64 d := by
  obtain ⟨rfl, hlt⟩ := h
  simp [ea, sext_small hlt]

theorem readReg_w64 (s : State) (r : Reg) : s.readReg .w64 r = s.getReg r := by
  simp [readReg, Width.bits]

theorem read_w64 {s : State} {a : BitVec 64} (h : s.canRead a 8 = true) :
    s.read .w64 a = .next (s.load64 a) := by
  have h' : s.canRead a Width.w64.bytes.toNat = true := h
  simp only [read, h', ite_true]
  rfl

theorem write_w64 {s : State} {a : BitVec 64} (v : BitVec 64) (h : s.canWrite a 8 = true) :
    s.write .w64 a v = .next (s.store64 a v) := by
  have h' : s.canWrite a Width.w64.bytes.toNat = true := h
  simp only [write, h', ite_true]
  rfl

end State

/-- When the flags are known, every condition has an answer. -/
theorem Cond.eval_some {f : Flags} (h : f.defined = true) (c : Cond) : ∃ b, c.eval f = some b := by
  obtain ⟨cf, zf, sf, of⟩ := f
  simp only [Flags.defined, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨⟨cf, rfl⟩, ⟨zf, rfl⟩⟩, ⟨sf, rfl⟩⟩, ⟨of, rfl⟩⟩ := h
  cases c <;> simp [Cond.eval]

/-- When the flags a condition reads are defined, it has an answer. -/
theorem Cond.decided_of_defined {cf zf sf of : Bool} (c : Cond)
    (hc : c.within cf zf sf of = true) :
    ∀ f, Flags.Defined cf zf sf of f → ∃ b, c.eval f = some b := by
  rintro ⟨fc, fz, fs, fo⟩ ⟨h1, h2, h3, h4⟩
  cases c <;> simp only [Cond.within, Bool.and_eq_true] at hc <;>
    simp only [Option.isSome_iff_exists] at h1 h2 h3 h4
  all_goals
    first
    | (obtain ⟨x, rfl⟩ := h1 hc; exact ⟨_, rfl⟩)
    | (obtain ⟨x, rfl⟩ := h2 hc; exact ⟨_, rfl⟩)
    | (obtain ⟨x, rfl⟩ := h3 hc; exact ⟨_, rfl⟩)
    | (obtain ⟨x, rfl⟩ := h4 hc; exact ⟨_, rfl⟩)
    | (obtain ⟨x, rfl⟩ := h1 hc.1; obtain ⟨y, rfl⟩ := h2 hc.2; exact ⟨_, rfl⟩)
    | (obtain ⟨x, rfl⟩ := h3 hc.1; obtain ⟨y, rfl⟩ := h4 hc.2; exact ⟨_, rfl⟩)
    | (obtain ⟨x, rfl⟩ := h2 hc.1.1; obtain ⟨y, rfl⟩ := h3 hc.1.2; obtain ⟨z, rfl⟩ := h4 hc.2
       exact ⟨_, rfl⟩)

theorem Flags.ofMul_defined (b : Bool) : Flags.AfterMul (Flags.ofMul b) := by
  simp [Flags.AfterMul, Flags.Defined, Flags.ofMul]

/-- The flags a shift or rotate leaves are the ones the rule promises. -/
theorem ShiftOp.eval_flagsAfter {n : Nat} (op : ShiftOp) {P : Flags → Prop} {old : Flags}
    (hP : P old) (a : BitVec n) (c : Nat) : op.flagsAfter c P (op.eval old a c).2 := by
  simp only [ShiftOp.flagsAfter, ShiftOp.eval]
  by_cases hc : c = 0
  · simp only [hc, ↓reduceIte]; exact hP
  · simp only [hc, ↓reduceIte]
    cases op <;> by_cases h1 : c = 1 <;> simp [Flags.Defined, h1]

theorem Flags.ofResult_defined {n : Nat} (r : BitVec n) (cf of : Bool) :
    (Flags.ofResult r cf of).defined = true := by
  simp [Flags.ofResult, Flags.defined]

/-- A two-operand operation produces a result and known flags, provided the
carry is known when the operation reads it. -/
theorem AluOp.eval_some {n : Nat} (op : AluOp) {cf : Option Bool} (a b : BitVec n)
    (h : op.readsCarry = true → cf.isSome = true) :
    ∃ r fl, op.eval cf a b = some (r, fl) ∧ fl.defined = true := by
  cases op <;>
    first
    | exact ⟨_, _, rfl, Flags.ofResult_defined _ _ _⟩
    | (obtain ⟨c, rfl⟩ := Option.isSome_iff_exists.mp (h rfl)
       exact ⟨_, _, rfl, Flags.ofResult_defined _ _ _⟩)

/-- An operation that does not read the carry flag evaluates to `apply`,
whatever the carry flag is. -/
theorem AluOp.eval_eq_apply {n : Nat} {op : AluOp} (h : op.readsCarry = false) (a b : BitVec n)
    (cf : Option Bool) : op.eval cf a b = some (op.apply a b) := by
  cases op <;> first | rfl | exact absurd h (by decide)

theorem addCarry_fst (a b : BitVec 64) : (addCarry a b false).1 = a + b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt
  simp [addCarry, BitVec.toNat_add, BitVec.toNat_setWidth]

theorem subBorrow_fst (a b : BitVec 64) : (subBorrow a b false).1 = a - b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt
  simp [subBorrow, BitVec.toNat_sub, BitVec.toNat_setWidth]
  omega

/-- The zero flag after a subtraction says whether the result is zero. -/
theorem subBorrow_zf {n : Nat} (a b : BitVec n) (c : Bool) :
    (subBorrow a b c).2.zf = some ((subBorrow a b c).1 == 0) := rfl

/-- A store leaves every eight bytes clear of the bytes it writes unchanged. -/
theorem State.load64_store_range (s : State) (w : Width) {q y : BitVec 64} (v : BitVec w.bits)
    (hd : Disjoint q w.bytes.toNat y 8) : (s.store w q v).load64 y = s.load64 y := by
  cases w
  · have hd := hd.of_pos (by decide) (by decide)
    exact State.load_store_disjoint s .w32 .w64 _ _ v
      (by simp only [Width.bytes] at *; bv_omega) (by simp only [Width.bytes] at *; bv_omega)
  · have hd := hd.of_pos (by decide) (by decide)
    exact State.load_store_disjoint s .w64 .w64 _ _ v
      (by simp only [Width.bytes] at *; bv_omega) (by simp only [Width.bytes] at *; bv_omega)

theorem State.mem_store_range (s : State) (w : Width) {q x : BitVec 64} (v : BitVec w.bits)
    (hx : BitVec.ofNat 64 w.bytes.toNat ≤ x - q) : (s.store w q v).mem x = s.mem x := by
  refine State.mem_store_of_disjoint s w _ x v ?_
  cases w <;> simp only [Width.bytes] at * <;> bv_omega

theorem State.load64_store8_range (s : State) {q y : BitVec 64} (v : BitVec 8)
    (hd : Disjoint q 1 y 8) : (s.store8 q v).load64 y = s.load64 y := by
  have hd := hd.of_pos (by decide) (by decide)
  exact State.load64_store8_disjoint s v (by bv_omega)

theorem State.mem_store8_range (s : State) {q x : BitVec 64} (v : BitVec 8)
    (hx : BitVec.ofNat 64 1 ≤ x - q) : (s.store8 q v).mem x = s.mem x := by
  rw [State.mem_store8]
  split
  · next he => exact absurd hx (by subst he; bv_omega)
  · rfl

theorem State.load64_store16_range (s : State) {q y : BitVec 64} (v : BitVec 16)
    (hd : Disjoint q 2 y 8) : (s.store16 q v).load64 y = s.load64 y := by
  have hd := hd.of_pos (by decide) (by decide)
  rw [State.store16, State.load64_store8_disjoint _ _ (by bv_omega),
    State.load64_store8_disjoint _ _ (by bv_omega)]

theorem State.mem_store16_range (s : State) {q x : BitVec 64} (v : BitVec 16)
    (hx : BitVec.ofNat 64 2 ≤ x - q) : (s.store16 q v).mem x = s.mem x := by
  rw [State.store16, State.mem_store8, State.mem_store8]
  split
  · next he => exact absurd hx (by subst he; bv_omega)
  · split
    · next he => exact absurd hx (by subst he; bv_omega)
    · rfl

/-- An offset into a block, written as a number and back. -/
theorem owned_off (a off : BitVec 64) : a + BitVec.ofNat 64 off.toNat = a + off := by simp

theorem AluOp.apply_defined {n : Nat} (op : AluOp) (a b : BitVec n) :
    (op.apply a b).2.defined = true := by
  cases op <;> exact Flags.ofResult_defined _ _ _

/-- Stepping `d` bytes on from byte `off`. -/
theorem byte_add (a : BitVec 64) (off d : Nat) :
    a + BitVec.ofNat 64 off + BitVec.ofNat 64 d = a + BitVec.ofNat 64 (off + d) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Instructions that continue to the next one -/

/-! ## Operands -/

/-- A register typed as exactly `a` holds `a`. -/
theorem WellTyped.eqReg {Γ : Ctx} {s : State} {r : Reg} {a : BitVec 64}
    (h : WellTyped fetch sys Ψ ix Γ s) (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq a) :
    s.getReg r = a := by
  have := h.regs r hr
  rwa [hΓ, hasTy_eq] at this

theorem State.readReg_of {s : State} {r : Reg} {a : BitVec 64} (hp : s.getReg r = a) (w : Width) :
    s.readReg w r = a.setWidth w.bits := by
  rw [State.readReg, hp]

theorem IndexReg.toReg_ne_rsp (x : IndexReg) : x.toReg ≠ .rsp := by
  cases x <;> decide

/-- The address an indexed operand refers to, when the index is known. -/
theorem State.ea_indexed (s : State) {b : Reg} {x : IndexReg} {sc : Scale} {disp : BitVec 32}
    {c D : BitVec 64} (hx : s.getReg x.toReg = c) (hD : (c <<< sc.shift) + disp.signExtend 64 = D) :
    s.ea (.sib (some b) (some (x, sc)) disp) = s.getReg b + D := by
  simp only [State.ea, hx]
  rw [BitVec.add_assoc, hD]

section Operands

variable {Γ : Ctx} {s : State} {next : BitVec 64}

theorem subBorrow_defined {n : Nat} (a b : BitVec n) (c : Bool) :
    (subBorrow a b c).2.defined = true :=
  Flags.ofResult_defined _ _ _

theorem State.ea_base (s : State) (b : Reg) (disp : BitVec 32) :
    s.ea (.sib (some b) none disp) = s.getReg b + disp.signExtend 64 := by
  simp [State.ea]

/-- An operand whose address is exactly known has that address. -/
theorem EaIs.sound {m : Mem} {p : BitVec 64} (he : EaIs Γ m p)
    (h : WellTyped fetch sys Ψ ix Γ s) : s.ea m = p := by
  cases he with
  | base hb hΓ => rw [State.ea_base, h.eqReg hb hΓ]
  | @indexed b x sc v c disp hb hΓ hΓx =>
    simp only [State.ea, h.eqReg hb hΓ, h.eqReg x.toReg_ne_rsp hΓx]

/-- Bytes inside an owned block may be written. -/
theorem WellTyped.canWrite_owned {k : Nat} {a off : BitVec 64} {S : Shape} {m : Nat}
    (h : WellTyped fetch sys Ψ ix Γ s) (hk : Γ.owned[k]? = some (a, S))
    (hm : off.toNat + m ≤ S.size) : s.canWrite (a + off) m = true := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
  have := State.canWrite_sub (h.owned.perm _ hin) (o := off.toNat) (m := m) hm
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

/-- A change confined to plain bytes of an owned block keeps the state well
typed as it was. -/
theorem WellTyped.writeOwnedFree {s' : State} {k : Nat} {a : BitVec 64} {S : Shape}
    {lo cnt : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hk : Γ.owned[k]? = some (a, S)) (hle : lo + cnt ≤ S.size)
    (hfree : S.free lo cnt = true)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 lo) cnt y 8 → s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤ x - (a + BitVec.ofNat 64 lo) → s'.mem x = s.mem x) :
    WellTyped fetch sys Ψ ix Γ s' := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
  have hw := h.writeOwned hΨ hk (S' := S) hle rfl (h.owned.fits _ hin) hregs hflags hperm
    hframe hmem (fun p hp => .inl ⟨hp, ShapeOf.clearOf_of_free hfree p hp⟩)
  have hset : Γ.owned.set k (a, S) = Γ.owned := by
    rw [← hkeq]; exact List.set_getElem_self hklt
  rw [hset] at hw
  exact hw

/-- A change confined to a run of bytes of an owned block keeps the state
well typed, with whatever typed values reached into the run forgotten. -/
theorem WellTyped.writeOwnedClear {s' : State} {k : Nat} {a : BitVec 64} {S : Shape}
    {lo cnt : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hk : Γ.owned[k]? = some (a, S)) (hle : lo + cnt ≤ S.size)
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 lo) cnt y 8 → s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 cnt ≤ x - (a + BitVec.ofNat 64 lo) → s'.mem x = s.mem x) :
    WellTyped fetch sys Ψ ix { Γ with owned := Γ.owned.set k (a, S.clear lo cnt) } s' := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
  exact h.writeOwned hΨ hk (S' := S.clear lo cnt) hle rfl
    (fun p hp => h.owned.fits _ hin p (ShapeOf.mem_clear hp).1) hregs hflags hperm hframe hmem
    (fun p hp => .inl (ShapeOf.mem_clear hp))

/-- A readable memory operand's bytes are readable. -/
theorem ReadOk.canRead {n : Nat} {m : Mem} (hr : ReadOk Ψ next Γ n (.mem m))
    (h : WellTyped fetch sys Ψ ix Γ s) (hrip : s.rip = next) : s.canRead (s.ea m) n = true := by
  cases hr with
  | @global base l d disp hl haddr hin =>
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 d := by
      simp only [State.ea, hrip, haddr]
    rw [hea]
    exact h.canRead_bytes hl hin
  | @indexed b x sc S writable off d disp c hb hΓ hΓx hD hin =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    rw [State.ea_indexed s hx hD, hva, byte_add]
    exact h.canRead_bytes hl hin
  | @field b S writable off d disp hb hΓ hdisp hin =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    rw [State.ea_byte s b hdisp, hva, byte_add]
    exact h.canRead_bytes hl hin
  | @slot d k i S disp hdisp hat hin =>
    obtain ⟨hk, rfl⟩ := hat
    rw [State.ea_byte s .rsp hdisp]
    exact State.canRead_of_canWrite (h.canWrite_piece hk hin)
  | @slotIndexed x sc d k i S disp c hΓx hD hat hin =>
    obtain ⟨hk, rfl⟩ := hat
    rw [State.ea_indexed s (h.eqReg x.toReg_ne_rsp hΓx) hD]
    exact State.canRead_of_canWrite (h.canWrite_piece hk hin)
  | @text b more hb hΓ hn =>
    subst hn
    exact h.canRead_text hb hΓ
  | @owned m k a p off F hm hat hn =>
    obtain ⟨hk, hoff⟩ := hat
    rw [hm.sound h, hoff]
    exact State.canRead_of_canWrite (h.canWrite_owned hk hn)

/-- Reading a readable operand succeeds. -/
theorem ReadOk.readRM {w : Width} {rm : RM} (hr : ReadOk Ψ next Γ w.bytes.toNat rm)
    (h : WellTyped fetch sys Ψ ix Γ s) (hrip : s.rip = next) : ∃ v, s.readRM w rm = .next v := by
  cases rm with
  | reg r => exact ⟨_, rfl⟩
  | mem m =>
    refine ⟨s.load w (s.ea m), ?_⟩
    simp only [State.readRM, State.read, hr.canRead h hrip, ite_true]

/-- Reading a readable narrow operand succeeds. -/
theorem ReadOk.readNarrow {sw : NarrowW} {rm : RM} (hr : ReadOk Ψ next Γ sw.bytes rm)
    (h : WellTyped fetch sys Ψ ix Γ s) (hrip : s.rip = next) :
    ∃ v, s.readNarrow sw rm = .next v := by
  cases rm with
  | reg r => exact ⟨_, rfl⟩
  | mem m =>
    cases sw with
    | w8 =>
      have hc : s.canRead (s.ea m) 1 = true := hr.canRead h hrip
      refine ⟨s.load8 (s.ea m), ?_⟩
      simp only [State.readNarrow, State.read8, hc, ite_true]
    | w16 =>
      have hc : s.canRead (s.ea m) 2 = true := hr.canRead h hrip
      refine ⟨s.load16 (s.ea m), ?_⟩
      simp only [State.readNarrow, State.read16, hc, ite_true]

/-- Writing any value to a writable operand succeeds and leaves a state
matching the judgment's result context. -/
theorem WriteIntOk.writeRM {w : Width} {rm : RM} {Γ' : Ctx}
    (hw : WriteIntOk Ψ next Γ w.bytes.toNat rm Γ') (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hrip : s.rip = next) (v : BitVec w.bits) :
    ∃ s', s.writeRM w rm v = .next s' ∧ s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases hw with
  | @indexed b x sc S off d disp c hb hΓ hΓx hD hin hfree =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (off + d) := by
      rw [State.ea_indexed s hx hD, hva, byte_add]
    have hc := h.canWrite_bytes (m := w.bytes.toNat) hl (hwr rfl) hin
    refine ⟨s.store w (a + BitVec.ofNat 64 (off + d)) v, ?_, State.rip_store _ _ _ _,
      h.writeHeapFree hΨ hl hin hfree (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _)
        (fun y hd => State.load64_store_range s w v hd)
        (fun x hx => State.mem_store_range s w v hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @global base l d disp hl hwr haddr hin hfree =>
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 d := by
      simp only [State.ea, hrip, haddr]
    have hc := h.canWrite_bytes (m := w.bytes.toNat) hl hwr hin
    refine ⟨s.store w (base + BitVec.ofNat 64 d) v, ?_, State.rip_store _ _ _ _,
      h.writeHeapFree hΨ hl hin hfree (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _)
        (fun y hd => State.load64_store_range s w v hd)
        (fun x hx => State.mem_store_range s w v hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @owned m k a p off S hm hat hin hfree =>
    obtain ⟨hk, hoff⟩ := hat
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hoa := owned_off a off
    have hc : s.canWrite (a + off) w.bytes.toNat = true := h.canWrite_owned hk hin
    refine ⟨s.store w (a + off) v, ?_, State.rip_store _ _ _ _,
      h.writeOwnedFree hΨ hk (lo := off.toNat) (cnt := w.bytes.toNat) hin hfree
        (State.regs_store _ _ _ _) (State.flags_store _ _ _ _) (State.perm_store _ _ _ _)
        (fun y hd => by rw [hoa] at hd; exact State.load64_store_range s w v hd)
        (fun x hx => by rw [hoa] at hx; exact State.mem_store_range s w v hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @ownedClear m k a p off S hm hat hin =>
    obtain ⟨hk, hoff⟩ := hat
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hoa := owned_off a off
    have hc : s.canWrite (a + off) w.bytes.toNat = true := h.canWrite_owned hk hin
    refine ⟨s.store w (a + off) v, ?_, State.rip_store _ _ _ _,
      h.writeOwnedClear hΨ hk (lo := off.toNat) (cnt := w.bytes.toNat) hin
        (State.regs_store _ _ _ _) (State.flags_store _ _ _ _) (State.perm_store _ _ _ _)
        (fun y hd => by rw [hoa] at hd; exact State.load64_store_range s w v hd)
        (fun x hx => by rw [hoa] at hx; exact State.mem_store_range s w v hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @reg d hd => exact ⟨s.writeReg w d v, rfl, rfl, h.setReg hd (HasTy.int _)⟩
  | @field b S off d disp hb hΓ hdisp hin hfree =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (off + d) := by
      rw [State.ea_byte s b hdisp, hva, byte_add]
    have hc := h.canWrite_bytes (m := w.bytes.toNat) hl (hwr rfl) hin
    refine ⟨s.store w (a + BitVec.ofNat 64 (off + d)) v, ?_, State.rip_store _ _ _ _,
      h.writeHeapFree hΨ hl hin hfree (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _)
        (fun y hd => State.load64_store_range s w v hd)
        (fun x hx => State.mem_store_range s w v hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @slot d k i S disp hdisp hat hin =>
    obtain ⟨hk, rfl⟩ := hat
    have hea := State.ea_byte s .rsp hdisp
    have hc := h.canWrite_piece (m := w.bytes.toNat) hk hin
    refine ⟨s.store w (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) v, ?_, State.rip_store _ _ _ _,
      h.writeStackClear hΨ hk hin (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _)
        (fun y hd => State.load64_store_range s w v hd)
        (fun x hx => State.mem_store_range s w v hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @slotIndexed x sc d k i S disp c hΓx hD hat hin =>
    obtain ⟨hk, rfl⟩ := hat
    have hea : s.ea (.sib (some .rsp) (some (x, sc)) disp)
        = s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i) :=
      State.ea_indexed s (h.eqReg x.toReg_ne_rsp hΓx) hD
    have hc := h.canWrite_piece (m := w.bytes.toNat) hk hin
    refine ⟨s.store w (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) v, ?_, State.rip_store _ _ _ _,
      h.writeStackClear hΨ hk hin (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _)
        (fun y hd => State.load64_store_range s w v hd)
        (fun x hx => State.mem_store_range s w v hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
/-- Writing any byte to a writable operand succeeds likewise. -/
theorem WriteIntOk.writeRM8 {rm : RM} {Γ' : Ctx} (hw : WriteIntOk Ψ next Γ 1 rm Γ')
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hrip : s.rip = next) (v : BitVec 8) :
    ∃ s', s.writeRM8 rm v = .next s' ∧ s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases hw with
  | @indexed b x sc S off d disp c hb hΓ hΓx hD hin hfree =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (off + d) := by
      rw [State.ea_indexed s hx hD, hva, byte_add]
    have hc := h.canWrite_bytes (m := 1) hl (hwr rfl) hin
    refine ⟨s.store8 (a + BitVec.ofNat 64 (off + d)) v, ?_, rfl,
      h.writeHeapFree hΨ hl hin hfree rfl rfl rfl
        (fun y hd => State.load64_store8_range s v hd)
        (fun x hx => State.mem_store8_range s v hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @global base l d disp hl hwr haddr hin hfree =>
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 d := by
      simp only [State.ea, hrip, haddr]
    have hc := h.canWrite_bytes (m := 1) hl hwr hin
    refine ⟨s.store8 (base + BitVec.ofNat 64 d) v, ?_, rfl,
      h.writeHeapFree hΨ hl hin hfree rfl rfl rfl
        (fun y hd => State.load64_store8_range s v hd)
        (fun x hx => State.mem_store8_range s v hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @owned m k a p off S hm hat hin hfree =>
    obtain ⟨hk, hoff⟩ := hat
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hoa := owned_off a off
    have hc : s.canWrite (a + off) 1 = true := h.canWrite_owned hk hin
    refine ⟨s.store8 (a + off) v, ?_, rfl,
      h.writeOwnedFree hΨ hk (lo := off.toNat) (cnt := 1) hin hfree
        rfl rfl rfl
        (fun y hd => by rw [hoa] at hd; exact State.load64_store8_range s v hd)
        (fun x hx => by rw [hoa] at hx; exact State.mem_store8_range s v hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @ownedClear m k a p off S hm hat hin =>
    obtain ⟨hk, hoff⟩ := hat
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hoa := owned_off a off
    have hc : s.canWrite (a + off) 1 = true := h.canWrite_owned hk hin
    refine ⟨s.store8 (a + off) v, ?_, rfl,
      h.writeOwnedClear hΨ hk (lo := off.toNat) (cnt := 1) hin
        rfl rfl rfl
        (fun y hd => by rw [hoa] at hd; exact State.load64_store8_range s v hd)
        (fun x hx => by rw [hoa] at hx; exact State.mem_store8_range s v hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @reg d hd => exact ⟨_, rfl, rfl, h.setReg hd (HasTy.int _)⟩
  | @field b S off d disp hb hΓ hdisp hin hfree =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (off + d) := by
      rw [State.ea_byte s b hdisp, hva, byte_add]
    have hc := h.canWrite_bytes (m := 1) hl (hwr rfl) hin
    refine ⟨s.store8 (a + BitVec.ofNat 64 (off + d)) v, ?_, rfl,
      h.writeHeapFree hΨ hl hin hfree rfl rfl rfl
        (fun y hd => State.load64_store8_range s v hd)
        (fun x hx => State.mem_store8_range s v hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @slot d k i S disp hdisp hat hin =>
    obtain ⟨hk, rfl⟩ := hat
    have hea := State.ea_byte s .rsp hdisp
    have hc := h.canWrite_piece (m := 1) hk hin
    refine ⟨s.store8 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) v, ?_, rfl,
      h.writeStackClear hΨ hk hin rfl rfl rfl
        (fun y hd => State.load64_store8_range s v hd)
        (fun x hx => State.mem_store8_range s v hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @slotIndexed x sc d k i S disp c hΓx hD hat hin =>
    obtain ⟨hk, rfl⟩ := hat
    have hea : s.ea (.sib (some .rsp) (some (x, sc)) disp)
        = s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i) :=
      State.ea_indexed s (h.eqReg x.toReg_ne_rsp hΓx) hD
    have hc := h.canWrite_piece (m := 1) hk hin
    refine ⟨s.store8 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) v, ?_, rfl,
      h.writeStackClear hΨ hk hin rfl rfl rfl
        (fun y hd => State.load64_store8_range s v hd)
        (fun x hx => State.mem_store8_range s v hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
theorem WriteIntOk.write16 {m : Mem} {Γ' : Ctx} (hw : WriteIntOk Ψ next Γ 2 (.mem m) Γ')
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hrip : s.rip = next) (v : BitVec 16) :
    ∃ s', s.write16 (s.ea m) v = .next s' ∧ s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases hw with
  | @indexed b x sc S off d disp c hb hΓ hΓx hD hin hfree =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (off + d) := by
      rw [State.ea_indexed s hx hD, hva, byte_add]
    have hc := h.canWrite_bytes (m := 2) hl (hwr rfl) hin
    refine ⟨s.store16 (a + BitVec.ofNat 64 (off + d)) v, ?_, rfl,
      h.writeHeapFree hΨ hl hin hfree rfl rfl rfl
        (fun y hd => State.load64_store16_range s v hd)
        (fun x hx => State.mem_store16_range s v hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @global base l d disp hl hwr haddr hin hfree =>
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 d := by
      simp only [State.ea, hrip, haddr]
    have hc := h.canWrite_bytes (m := 2) hl hwr hin
    refine ⟨s.store16 (base + BitVec.ofNat 64 d) v, ?_, rfl,
      h.writeHeapFree hΨ hl hin hfree rfl rfl rfl
        (fun y hd => State.load64_store16_range s v hd)
        (fun x hx => State.mem_store16_range s v hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @owned m k a p off S hm hat hin hfree =>
    obtain ⟨hk, hoff⟩ := hat
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hoa := owned_off a off
    have hc : s.canWrite (a + off) 2 = true := h.canWrite_owned hk hin
    refine ⟨s.store16 (a + off) v, ?_, rfl,
      h.writeOwnedFree hΨ hk (lo := off.toNat) (cnt := 2) hin hfree
        rfl rfl rfl
        (fun y hd => by rw [hoa] at hd; exact State.load64_store16_range s v hd)
        (fun x hx => by rw [hoa] at hx; exact State.mem_store16_range s v hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @ownedClear m k a p off S hm hat hin =>
    obtain ⟨hk, hoff⟩ := hat
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hoa := owned_off a off
    have hc : s.canWrite (a + off) 2 = true := h.canWrite_owned hk hin
    refine ⟨s.store16 (a + off) v, ?_, rfl,
      h.writeOwnedClear hΨ hk (lo := off.toNat) (cnt := 2) hin
        rfl rfl rfl
        (fun y hd => by rw [hoa] at hd; exact State.load64_store16_range s v hd)
        (fun x hx => by rw [hoa] at hx; exact State.mem_store16_range s v hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @field b S off d disp hb hΓ hdisp hin hfree =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (off + d) := by
      rw [State.ea_byte s b hdisp, hva, byte_add]
    have hc := h.canWrite_bytes (m := 2) hl (hwr rfl) hin
    refine ⟨s.store16 (a + BitVec.ofNat 64 (off + d)) v, ?_, rfl,
      h.writeHeapFree hΨ hl hin hfree rfl rfl rfl
        (fun y hd => State.load64_store16_range s v hd)
        (fun x hx => State.mem_store16_range s v hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @slot d k i S disp hdisp hat hin =>
    obtain ⟨hk, rfl⟩ := hat
    have hea := State.ea_byte s .rsp hdisp
    have hc := h.canWrite_piece (m := 2) hk hin
    refine ⟨s.store16 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) v, ?_, rfl,
      h.writeStackClear hΨ hk hin rfl rfl rfl
        (fun y hd => State.load64_store16_range s v hd)
        (fun x hx => State.mem_store16_range s v hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @slotIndexed x sc d k i S disp c hΓx hD hat hin =>
    obtain ⟨hk, rfl⟩ := hat
    have hea : s.ea (.sib (some .rsp) (some (x, sc)) disp)
        = s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i) :=
      State.ea_indexed s (h.eqReg x.toReg_ne_rsp hΓx) hD
    have hc := h.canWrite_piece (m := 2) hk hin
    refine ⟨s.store16 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) v, ?_, rfl,
      h.writeStackClear hΨ hk hin rfl rfl rfl
        (fun y hd => State.load64_store16_range s v hd)
        (fun x hx => State.mem_store16_range s v hx)⟩
    simp only [hea, State.write16, hc, ite_true]
/-- An operand holding a code pointer can be read, and what is read is a code pointer. -/
theorem Holds.sound {rm : RM} {τ : Ty} (hc : Holds Ψ next Γ rm τ)
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hrip : s.rip = next) :
    ∃ v, s.readRM .w64 rm = .next v ∧ HasTy fetch sys Ψ ix τ v := by
  cases hc with
  | @indexed b x sc S writable off d disp c Δ hb hΓ hΓx hD hi =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hm := ShapeOf.mem_of_valAt hi
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (off + d) := by
      rw [State.ea_indexed s hx hD, hva, byte_add]
    refine ⟨s.load64 (a + BitVec.ofNat 64 (off + d)), ?_, h.heap _ l hl _ hm⟩
    simp [State.readRM, hea, State.read_w64 (h.canRead_bytes hl (hΨ.fits _ l hl _ hm))]
  | @global base l d disp Δ hl haddr hi =>
    have hm := ShapeOf.mem_of_valAt hi
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 d := by
      simp only [State.ea, hrip, haddr]
    refine ⟨s.load64 (base + BitVec.ofNat 64 d), ?_, h.heap _ l hl _ hm⟩
    simp [State.readRM, hea, State.read_w64 (h.canRead_bytes hl (hΨ.fits _ l hl _ hm))]
  | @reg r Δ hr hΓ =>
    refine ⟨s.getReg r, ?_, by have := h.regs r hr; rwa [hΓ] at this⟩
    simp [State.readRM, State.readReg_w64]
  | @field b S writable off d disp Δ hb hΓ hdisp hi =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hm := ShapeOf.mem_of_valAt hi
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (off + d) := by
      rw [State.ea_byte s b hdisp, hva, byte_add]
    refine ⟨s.load64 (a + BitVec.ofNat 64 (off + d)), ?_, h.heap _ l hl _ hm⟩
    simp [State.readRM, hea, State.read_w64 (h.canRead_bytes hl (hΨ.fits _ l hl _ hm))]
  | @slot d k i S disp Δ hdisp hat hi =>
    obtain ⟨hk, rfl⟩ := hat
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := h.stackFits S (List.mem_of_getElem? hk) _ hm
    refine ⟨s.load64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)), ?_,
      h.stack k S hk _ hm⟩
    simp [State.readRM, State.ea_byte s .rsp hdisp,
      State.read_w64 (State.canRead_of_canWrite (h.canWrite_piece hk hfit))]

end Operands

/-! ## Exactly known values -/

/-- The value a shift or rotate produces does not depend on the flags. -/
theorem ShiftOp.eval_fst {n : Nat} (op : ShiftOp) (old : Flags) (a : BitVec n) (c : Nat) :
    (op.eval old a c).1 = op.apply a c := by
  simp only [ShiftOp.eval, ShiftOp.apply]
  by_cases hc : c = 0
  · subst hc
    cases op <;> simp only [↓reduceIte, BitVec.shiftLeft_zero, BitVec.ushiftRight_zero,
      BitVec.sshiftRight_zero]
    · ext i hi; simp [BitVec.getElem_rotateLeft]
    · ext i hi; simp [BitVec.getElem_rotateRight, hi]
  · simp only [hc, ↓reduceIte]
    cases op <;> rfl

/-- An unsigned divide of a dividend whose upper half is zero, by a divisor
that is not zero, raises no divide error. -/
theorem MulDivOp.eval_div {n : Nat} (a b : BitVec n) (hb : b ≠ 0) :
    MulDivOp.eval .div 0 a b = .next (a / b, a % b, .unknown) := by
  have hbn : b.toNat ≠ 0 := fun h0 => hb (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hbpos : 0 < b.toNat := Nat.pos_of_ne_zero hbn
  have ha := a.isLt
  have hb' := b.isLt
  have hpow : 2 ^ n ≤ 2 ^ (n + n) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right n n)
  have hdiv : a.toNat / b.toNat < 2 ^ n := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  have hmod : a.toNat % b.toNat < 2 ^ n := Nat.lt_of_lt_of_le (Nat.mod_lt _ hbpos) (Nat.le_of_lt hb')
  have hdvd : ((0 : BitVec n) ++ a).toNat = a.toNat := by
    simp [BitVec.toNat_append]
  have hbw : (b.setWidth (n + n)).toNat = b.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hq : (((0 : BitVec n) ++ a) / b.setWidth (n + n)).toNat = a.toNat / b.toNat := by
    rw [BitVec.toNat_udiv, hdvd, hbw]
  have hr : (((0 : BitVec n) ++ a) % b.setWidth (n + n)).toNat = a.toNat % b.toNat := by
    rw [BitVec.toNat_umod, hdvd, hbw]
  have hb0 : (b == 0) = false := by simpa using hb
  have hfit : ((((0 : BitVec n) ++ a) / b.setWidth (n + n)).setWidth n).setWidth (n + n)
      = ((0 : BitVec n) ++ a) / b.setWidth (n + n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hq]
    rw [Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt (by omega)]
  have hlo : (((0 : BitVec n) ++ a) / b.setWidth (n + n)).setWidth n = a / b := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hq, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt hdiv
  have hhi : (((0 : BitVec n) ++ a) % b.setWidth (n + n)).setWidth n = a % b := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hr, BitVec.toNat_umod]
    exact Nat.mod_eq_of_lt hmod
  rw [hlo] at hfit
  simp only [MulDivOp.eval, hb0, hlo, hhi, hfit, bne_self_eq_false, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]

/-- A value with its sign bit copied across the upper half is its sign extension. -/
theorem signFill_append {n : Nat} (a : BitVec n) : signFill a ++ a = a.signExtend (n + n) := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_signExtend, signFill]
  by_cases h : i < n
  · simp [h]
  · simp only [h, ↓reduceDIte]
    by_cases hm : a.msb = true <;> simp [hm]

/-- A signed divide of a sign-extended dividend, by a divisor that is not
zero, raises no divide error unless it is the one quotient that does not
fit: the most negative number divided by minus one. -/
theorem MulDivOp.eval_idiv {n : Nat} (a b : BitVec n) (hb : b ≠ 0)
    (hov : a ≠ BitVec.intMin n ∨ b ≠ -1#n) :
    MulDivOp.eval .idiv (signFill a) a b = .next (a.sdiv b, a.srem b, .unknown) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim b 0) hb
    · exact h
  have hle : n ≤ n + n := Nat.le_add_right n n
  have hAi : (a.signExtend (n + n)).toInt = a.toInt := BitVec.toInt_signExtend_of_le hle
  have hDi : (b.signExtend (n + n)).toInt = b.toInt := BitVec.toInt_signExtend_of_le hle
  have hne : a.signExtend (n + n) ≠ BitVec.intMin (n + n) := by
    intro h
    have ht := congrArg BitVec.toInt h
    rw [hAi, BitVec.toInt_intMin] at ht
    have hlow := BitVec.le_toInt a
    have hpow : (2 : Nat) ^ (n - 1) < 2 ^ (n + n - 1) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hmod : (2 : Nat) ^ (n + n - 1) % 2 ^ (n + n) = 2 ^ (n + n - 1) :=
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    rw [hmod] at ht
    have hcast : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by norm_cast
    rw [hcast] at hlow
    omega
  have hq : (a.signExtend (n + n)).sdiv (b.signExtend (n + n)) = (a.sdiv b).signExtend (n + n) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (.inl hne), hAi, hDi,
      BitVec.toInt_signExtend_of_le hle, BitVec.toInt_sdiv_of_ne_or_ne _ _ hov]
  have hr : (a.signExtend (n + n)).srem (b.signExtend (n + n)) = (a.srem b).signExtend (n + n) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_srem, hAi, hDi, BitVec.toInt_signExtend_of_le hle, BitVec.toInt_srem]
  have htr : ∀ x : BitVec n, (x.signExtend (n + n)).setWidth n = x := by
    intro x
    ext i hi
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, hi, ↓reduceIte,
      BitVec.getLsbD_eq_getElem hi]
    have hi' : i < n + n := by omega
    simp [hi']
  have hb0 : (b == 0) = false := by simpa using hb
  simp only [MulDivOp.eval, signFill_append, hq, hr, htr, hb0, bne_self_eq_false, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]

/-! ## Multiply and divide -/

/-- A multiply or divide that produces a result continues, with `rax` and
`rdx` integers. -/
theorem mulDiv_next {Γ : Ctx} {s : State} {op : MulDivOp} {w : Width} {src : RM}
    (hr : ReadOk Ψ next Γ w.bytes.toNat src) (h : WellTyped fetch sys Ψ ix Γ s)
    (hrip : s.rip = next) {P : Flags → Prop}
    (hx : ∀ a, ∃ x, op.eval (s.readReg w .rdx) (s.readReg w .rax) a = .next x ∧ P x.2.2) :
    ∃ s', exec sys (.mulDiv op w src) s = .next s' ∧ s'.rip = s.rip ∧
      WellTyped fetch sys Ψ ix (Γ.afterMulDiv P) s' := by
  obtain ⟨a, ha⟩ := hr.readRM h hrip
  obtain ⟨⟨lo, hi, fl⟩, hx, hP⟩ := hx a
  refine ⟨{ (s.writeReg w .rax lo).writeReg w .rdx hi with flags := fl }, ?_, rfl,
    ((h.setReg (by decide) (HasTy.int _)).setReg (by decide) (HasTy.int _)).setFlags
      (P := P) hP⟩
  simp [exec, ha, hx]

/-- A multiply or divide of exactly known values that produces a result
continues, with exactly known results. -/
theorem mulDivExact_next {Γ : Ctx} {s : State} {op : MulDivOp} {w : Width} {r : Reg}
    {a d b : BitVec 64} {lo hi : BitVec w.bits} {fl : Flags}
    (h : WellTyped fetch sys Ψ ix Γ s) (hr : r ≠ .rsp) (hΓa : Γ.regs .rax = .eq a)
    (hΓd : Γ.regs .rdx = .eq d) (hΓr : Γ.regs r = .eq b)
    (hev : op.eval (d.setWidth w.bits) (a.setWidth w.bits) (b.setWidth w.bits)
      = .next (lo, hi, fl)) :
    ∃ s', exec sys (.mulDiv op w (.reg r)) s = .next s' ∧ s'.rip = s.rip ∧
      WellTyped fetch sys Ψ ix
        { (Γ.setReg .rax (.eq (lo.setWidth 64))).setReg .rdx (.eq (hi.setWidth 64)) with
          flags := (· = fl) } s' := by
  have ha := h.eqReg (by decide) hΓa
  have hd := h.eqReg (by decide) hΓd
  have hb := h.eqReg hr hΓr
  refine ⟨{ (s.writeReg w .rax lo).writeReg w .rdx hi with flags := fl }, ?_, rfl,
    ((h.setReg (by decide) (hasTy_eq.mpr rfl)).setReg (by decide) (hasTy_eq.mpr rfl)).setFlags
      (P := (· = fl)) rfl⟩
  simp [exec, State.readRM, State.readReg_of ha, State.readReg_of hd, State.readReg_of hb, hev]

/-- A straight-line typed instruction, run in a matching state, continues to
the next instruction and leaves a state matching the rule's result context. -/
theorem Straight.sound {next : BitVec 64} {Γ Γ' : Ctx} {i : Instr}
    (ht : Straight Ψ next Γ i Γ')
    (hΨ : Ψ.WF) {s : State} (h : WellTyped fetch sys Ψ ix Γ s) (hrip : s.rip = next) :
    ∃ s', exec sys i s = .next s' ∧ s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases ht with
  | @aluStoreR Γ₁ op w dst src hwd hr hw hc =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    obtain ⟨r, fl, he, hdef⟩ := op.eval_some (cf := s.flags.cf) a (s.readReg w src)
      (fun hrc => hc hrc _ h.flags)
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM h hΨ hrip r
    refine ⟨{ s' with flags := fl }, ?_, hrip', hwt.setFlags (P := Flags.Known) hdef⟩
    simp [exec, Operands.src, Operands.dst, ha, he, Result.ofOption, hwd, hs']
  | @aluStoreI Γ₁ op w dst imm hwd hr hw hc =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    obtain ⟨r, fl, he, hdef⟩ := op.eval_some (cf := s.flags.cf) a (imm.signExtend w.bits)
      (fun hrc => hc hrc _ h.flags)
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM h hΨ hrip r
    refine ⟨{ s' with flags := fl }, ?_, hrip', hwt.setFlags (P := Flags.Known) hdef⟩
    simp [exec, Operands.src, Operands.dst, ha, he, Result.ofOption, hwd, hs']
  | @cmpR op w dst src hwd hr =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    obtain ⟨r, fl, he, hdef⟩ := op.eval_some (cf := s.flags.cf) a (s.readReg w src)
      (fun hrc => absurd hrc (by cases op <;> simp_all [AluOp.writesDst, AluOp.readsCarry]))
    refine ⟨{ s with flags := fl }, ?_, rfl, h.setFlags (P := Flags.Known) hdef⟩
    simp [exec, Operands.src, Operands.dst, ha, he, Result.ofOption, hwd]
  | @cmpI op w dst imm hwd hr =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    obtain ⟨r, fl, he, hdef⟩ := op.eval_some (cf := s.flags.cf) a (imm.signExtend w.bits)
      (fun hrc => absurd hrc (by cases op <;> simp_all [AluOp.writesDst, AluOp.readsCarry]))
    refine ⟨{ s with flags := fl }, ?_, rfl, h.setFlags (P := Flags.Known) hdef⟩
    simp [exec, Operands.src, Operands.dst, ha, he, Result.ofOption, hwd]
  | @aluLoad op w d m hd hr hc =>
    obtain ⟨b, hb⟩ := hr.readRM h hrip
    simp only [State.readRM] at hb
    obtain ⟨r, fl, he, hdef⟩ := op.eval_some (cf := s.flags.cf) (s.readReg w d) b
      (fun hrc => hc hrc _ h.flags)
    refine ⟨{ (if op.writesDst then s.setReg d (r.setWidth 64) else s) with flags := fl }, ?_, ?_,
      h.afterAlu hd hdef _⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, hb, he,
          Result.ofOption, hwd, State.writeReg]
    · cases op.writesDst <;> rfl
  | @testRM w dst src hr =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    refine ⟨{ s with flags := .ofResult (a &&& s.readRI w src) false false }, ?_, rfl,
      h.setFlags (P := Flags.Known) (Flags.ofResult_defined _ _ _)⟩
    simp [exec, ha]
  | @negRM Γ₁ w dst hr hw =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM h hΨ hrip (subBorrow (0#w.bits) a false).1
    refine ⟨{ s' with flags := (subBorrow (0#w.bits) a false).2 }, ?_, hrip',
      hwt.setFlags (P := Flags.Known) (subBorrow_defined _ _ _)⟩
    simp [exec, ha, hs']
  | @notRM Γ₁ w dst hr hw =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM h hΨ hrip (~~~a)
    exact ⟨s', by simp [exec, ha, hs'], hrip', hwt⟩
  | @shiftImm Γ₁ op w dst n hr hw =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    have hfl := op.eval_flagsAfter h.flags a (n.toNat % w.bits)
    generalize hrf : op.eval s.flags a (n.toNat % w.bits) = rf at hfl
    obtain ⟨r, fl⟩ := rf
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM h hΨ hrip r
    refine ⟨{ s' with flags := fl }, ?_, hrip', hwt.setFlags hfl⟩
    simp [exec, ha, State.shiftCount, hrf, hs']
  | @shiftCl Γ₁ op w dst hr hw =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    generalize hrf : op.eval s.flags a (s.shiftCount w .cl) = rf
    obtain ⟨r, fl⟩ := rf
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM h hΨ hrip r
    refine ⟨{ s' with flags := fl }, ?_, hrip', hwt.setFlags (P := Flags.Any) trivial⟩
    simp [exec, ha, hrf, hs']
  | @mulRM w src hr => exact mulDiv_next hr h hrip (fun _ => ⟨_, rfl, Flags.ofMul_defined _⟩)
  | @imulRM w src hr => exact mulDiv_next hr h hrip (fun _ => ⟨_, rfl, Flags.ofMul_defined _⟩)
  | mulDivExact hr hΓa hΓd hΓr hev => exact mulDivExact_next h hr hΓa hΓd hΓr hev
  | @xorSelf w d hd =>
    refine ⟨{ s.setReg d 0 with flags := .ofResult (0 : BitVec w.bits) false false }, ?_, rfl,
      (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = _)) rfl⟩
    simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, AluOp.eval,
      Result.ofOption, AluOp.writesDst, State.writeReg]
  | @mov32Exact d src a hd hs hΓ =>
    have hp := h.eqReg hs hΓ
    refine ⟨s.writeReg .w32 d (a.setWidth 32), ?_, rfl, h.setReg hd (hasTy_eq.mpr rfl)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.readReg_of hp]
  | @aluExact32 op d imm a hd hΓ hnc =>
    have hp := h.eqReg hd hΓ
    generalize hrf : op.apply (a.setWidth 32) (imm.signExtend 32) = rf
    obtain ⟨r, fl⟩ := rf
    have he' : op.eval s.flags.cf (s.readReg .w32 d) (imm.signExtend 32) = some (r, fl) := by
      rw [State.readReg_of hp, AluOp.eval_eq_apply hnc]
      exact congrArg some hrf
    have himm : imm.signExtend 32 = imm := by simp
    rw [himm] at he'
    refine ⟨{ (if op.writesDst then s.setReg d (r.setWidth 64) else s) with flags := fl }, ?_, ?_, ?_⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, he',
          Result.ofOption, hwd, State.writeReg]
    · cases op.writesDst <;> rfl
    · cases hwd : op.writesDst
      · simp only [Bool.cond_false]
        exact h.setFlags (P := (· = fl)) rfl
      · simp only [Bool.cond_true]
        exact (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = fl)) rfl
  | @aluExactRR32 op d src a b hd hs hΓ hΓ' hnc =>
    have hp := h.eqReg hd hΓ
    have hp' := h.eqReg hs hΓ'
    generalize hrf : op.apply (a.setWidth 32) (b.setWidth 32) = rf
    obtain ⟨r, fl⟩ := rf
    have he' : op.eval s.flags.cf (s.readReg .w32 d) (s.readReg .w32 src) = some (r, fl) := by
      rw [State.readReg_of hp, State.readReg_of hp', AluOp.eval_eq_apply hnc]
      exact congrArg some hrf
    refine ⟨{ (if op.writesDst then s.setReg d (r.setWidth 64) else s) with flags := fl }, ?_, ?_, ?_⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, he',
          Result.ofOption, hwd, State.writeReg]
    · cases op.writesDst <;> rfl
    · cases hwd : op.writesDst
      · simp only [Bool.cond_false]
        exact h.setFlags (P := (· = fl)) rfl
      · simp only [Bool.cond_true]
        exact (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = fl)) rfl
  | @shiftExact op w d n a hd hΓ =>
    have hp := h.eqReg hd hΓ
    have hfl := op.eval_flagsAfter h.flags (a.setWidth w.bits) (n.toNat % w.bits)
    have hv := op.eval_fst s.flags (a.setWidth w.bits) (n.toNat % w.bits)
    generalize hrf : op.eval s.flags (a.setWidth w.bits) (n.toNat % w.bits) = rf at hfl hv
    obtain ⟨r, fl⟩ := rf
    have hv' : r = op.apply (a.setWidth w.bits) (n.toNat % w.bits) := hv
    refine ⟨{ s.writeReg w d r with flags := fl }, ?_, rfl,
      (h.setReg hd (hasTy_eq.mpr (by rw [hv']))).setFlags hfl⟩
    simp [exec, State.readRM, State.writeRM, State.readReg_of hp, State.shiftCount, hrf]
  | @leaExactB d b disp a hd hb hΓ =>
    have hp := h.eqReg hb hΓ
    refine ⟨s.writeReg .w64 d ((s.ea (.sib (some b) none disp)).setWidth 64), ?_, rfl,
      h.setReg hd (hasTy_eq.mpr (by simp [State.ea, hp]))⟩
    simp [exec]
  | @leaExactBI d b x sc disp a c hd hb hΓ hΓ' =>
    have hp := h.eqReg hb hΓ
    have hp' := h.eqReg x.toReg_ne_rsp hΓ'
    refine ⟨s.writeReg .w64 d ((s.ea (.sib (some b) (some (x, sc)) disp)).setWidth 64), ?_, rfl,
      h.setReg hd (hasTy_eq.mpr (by simp [State.ea, hp, hp']))⟩
    simp [exec]
  | @negExact w d a hd hΓ =>
    have hp := h.eqReg hd hΓ
    refine ⟨{ s.writeReg w d (subBorrow (0#w.bits) (a.setWidth w.bits) false).1 with
        flags := (subBorrow (0#w.bits) (a.setWidth w.bits) false).2 }, ?_, rfl,
      (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = _)) rfl⟩
    simp [exec, State.readRM, State.writeRM, State.readReg_of hp]
  | @notExact w d a hd hΓ =>
    have hp := h.eqReg hd hΓ
    exact ⟨s.writeReg w d (~~~(a.setWidth w.bits)),
      by simp [exec, State.readRM, State.writeRM, State.readReg_of hp], rfl,
      h.setReg hd (hasTy_eq.mpr rfl)⟩
  | @imul2Exact w d r a b hd hr hΓ hΓ' =>
    have hp := h.eqReg hd hΓ
    have hp' := h.eqReg hr hΓ'
    refine ⟨{ s.writeReg w d (imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).1 with
        flags := (imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).2 }, ?_, rfl,
      (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = _)) rfl⟩
    simp [exec, State.readRM, State.readReg_of hp, State.readReg_of hp']
  | @imul3Exact w d r imm b hd hr hΓ =>
    have hp := h.eqReg hr hΓ
    refine ⟨{ s.writeReg w d (imulTrunc (b.setWidth w.bits) (imm.signExtend w.bits)).1 with
        flags := (imulTrunc (b.setWidth w.bits) (imm.signExtend w.bits)).2 }, ?_, rfl,
      (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = _)) rfl⟩
    simp [exec, State.readRM, State.readReg_of hp]
  | @cdqExact a hΓ =>
    have hp := h.eqReg (by decide) hΓ
    exact ⟨s.writeReg .w32 .rdx (signFill (a.setWidth 32)), by simp [exec, State.readReg_of hp],
      rfl, h.setReg (by decide) (hasTy_eq.mpr rfl)⟩
  | @cqoExact a hΓ =>
    have hp := h.eqReg (by decide) hΓ
    exact ⟨s.writeReg .w64 .rdx (signFill (s.readReg .w64 .rax)), by simp [exec], rfl,
      h.setReg (by decide) (hasTy_eq.mpr (by simp [State.readReg_w64, hp]))⟩
  | @movsxdExact d r a hd hr hΓ =>
    have hp := h.eqReg hr hΓ
    exact ⟨s.setReg d ((a.setWidth 32).signExtend 64),
      by simp [exec, State.readRM, State.readReg_of hp], rfl, h.setReg hd (hasTy_eq.mpr rfl)⟩
  | @movzxExact w sw d r a hd hr hΓ =>
    have hp := h.eqReg hr hΓ
    exact ⟨s.writeReg w d ((a.setWidth sw.bits).setWidth w.bits),
      by simp [exec, State.readNarrow, hp], rfl, h.setReg hd (hasTy_eq.mpr rfl)⟩
  | @movsxExact w sw d r a hd hr hΓ =>
    have hp := h.eqReg hr hΓ
    exact ⟨s.writeReg w d ((a.setWidth sw.bits).signExtend w.bits),
      by simp [exec, State.readNarrow, hp], rfl, h.setReg hd (hasTy_eq.mpr rfl)⟩
  | @popcntExact w d r a hd hr hΓ =>
    have hp := h.eqReg hr hΓ
    refine ⟨{ s.writeReg w d (popcount (a.setWidth w.bits)) with
        flags := ⟨some false, some (a.setWidth w.bits == 0), some false, some false⟩ }, ?_, rfl,
      (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = _)) rfl⟩
    simp [exec, State.readRM, State.readReg_of hp]
  | @bswapExact w r a hr hΓ =>
    have hp := h.eqReg hr hΓ
    exact ⟨s.writeReg w r (TypedAsm.bswap w (a.setWidth w.bits)),
      by simp [exec, State.readReg_of hp], rfl, h.setReg hr (hasTy_eq.mpr rfl)⟩
  | @cmovExact c w d r x a b hd hr hΓ hΓ' hdec =>
    have hpx := h.eqReg hd hΓ
    have hpa := h.eqReg hr hΓ'
    have hb := hdec _ h.flags
    exact ⟨s.writeReg w d (if b then a.setWidth w.bits else x.setWidth w.bits),
      by simp [exec, State.readRM, State.readReg_of hpa, State.readReg_of hpx, hb, Result.ofOption],
      rfl, h.setReg hd (hasTy_eq.mpr rfl)⟩
  | @setccExact c d x b hd hΓ hdec =>
    have hp := h.eqReg hd hΓ
    have hb := hdec _ h.flags
    refine ⟨s.setReg d ((x &&& ~~~0xff) ||| (if b then (1 : BitVec 8) else 0).setWidth 64), ?_,
      rfl, h.setReg hd (hasTy_eq.mpr rfl)⟩
    simp only [exec, hb, Result.ofOption, State.writeRM8, hp]
    rfl
  | @imul2RM w d src hd hr =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    have hfl : Flags.AfterMul (imulTrunc (s.readReg w d) a).2 := Flags.ofMul_defined _
    generalize hrf : imulTrunc (s.readReg w d) a = rf at hfl
    obtain ⟨r, fl⟩ := rf
    refine ⟨{ s.writeReg w d r with flags := fl }, ?_, rfl,
      (h.setReg hd (HasTy.int _)).setFlags hfl⟩
    simp [exec, ha, hrf]
  | @imul3RM w d src imm hd hr =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    have hfl : Flags.AfterMul (imulTrunc a (imm.signExtend w.bits)).2 := Flags.ofMul_defined _
    generalize hrf : imulTrunc a (imm.signExtend w.bits) = rf at hfl
    obtain ⟨r, fl⟩ := rf
    refine ⟨{ s.writeReg w d r with flags := fl }, ?_, rfl,
      (h.setReg hd (HasTy.int _)).setFlags hfl⟩
    simp [exec, ha, hrf]
  | @popcntRM w d src hd hr =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    refine ⟨{ s.writeReg w d (popcount a) with
        flags := ⟨some false, some (a == 0), some false, some false⟩ }, ?_, rfl,
      (h.setReg hd (HasTy.int _)).setFlags (P := Flags.Known) rfl⟩
    simp [exec, ha]
  | @bswap w r hr =>
    exact ⟨s.writeReg w r (TypedAsm.bswap w (s.readReg w r)), by simp [exec], rfl,
      h.setReg hr (HasTy.int _)⟩
  | cdq =>
    exact ⟨s.writeReg .w32 .rdx (signFill (s.readReg .w32 .rax)), by simp [exec], rfl,
      h.setReg (by decide) (HasTy.int _)⟩
  | cqo =>
    exact ⟨s.writeReg .w64 .rdx (signFill (s.readReg .w64 .rax)), by simp [exec], rfl,
      h.setReg (by decide) (HasTy.int _)⟩
  | @movsxdRM d src hd hr =>
    obtain ⟨a, ha⟩ := ReadOk.readRM (w := .w32) hr h hrip
    exact ⟨s.setReg d (a.signExtend 64), by simp [exec, ha], rfl, h.setReg hd (HasTy.int _)⟩
  | @cmovRM c w d src hd hr hdec =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    obtain ⟨b, hb⟩ := hdec _ h.flags
    exact ⟨s.writeReg w d (if b then a else s.readReg w d),
      by simp [exec, ha, hb, Result.ofOption], rfl, h.setReg hd (HasTy.int _)⟩
  | @setccRM Γ₁ c dst hw hdec =>
    obtain ⟨b, hb⟩ := hdec _ h.flags
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM8 h hΨ hrip (if b then 1#8 else 0#8)
    exact ⟨s', by simp [exec, hb, Result.ofOption, hs'], hrip', hwt⟩
  | @movzxRM w d sw src hd hr =>
    obtain ⟨a, ha⟩ := hr.readNarrow h hrip
    exact ⟨s.writeReg w d (a.setWidth w.bits), by simp [exec, ha], rfl,
      h.setReg hd (HasTy.int _)⟩
  | @movsxRM w d sw src hd hr =>
    obtain ⟨a, ha⟩ := hr.readNarrow h hrip
    exact ⟨s.writeReg w d (a.signExtend w.bits), by simp [exec, ha], rfl,
      h.setReg hd (HasTy.int _)⟩
  | @loadInt w d m hd hr =>
    obtain ⟨a, ha⟩ := hr.readRM h hrip
    simp only [State.readRM] at ha
    exact ⟨s.writeReg w d a, by simp [exec, Operands.src, Operands.dst, State.writeRM, ha], rfl,
      h.setReg hd (HasTy.int _)⟩
  | @storeInt Γ₁ w dst src hw =>
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM h hΨ hrip (s.readReg w src)
    exact ⟨s', by simp [exec, Operands.src, Operands.dst, hs'], hrip', hwt⟩
  | @storeImm Γ₁ w dst imm hw =>
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM h hΨ hrip (imm.signExtend w.bits)
    exact ⟨s', by simp [exec, Operands.src, Operands.dst, hs'], hrip', hwt⟩
  | @store16RM Γ₁ m src hw =>
    obtain ⟨s', hs', hrip', hwt⟩ := hw.write16 h hΨ hrip ((s.getReg src).setWidth 16)
    exact ⟨s', by simp [exec, hs'], hrip', hwt⟩
  | @store8RM Γ₁ m src hw =>
    obtain ⟨s', hs', hrip', hwt⟩ := hw.writeRM8 h hΨ hrip ((s.getReg src).setWidth 8)
    simp only [State.writeRM8] at hs'
    exact ⟨s', by simp [exec, hs'], hrip', hwt⟩
  | nop =>
    refine ⟨s, ?_, rfl, h⟩
    simp [exec]
  | @movRR64 d src hd hs =>
    refine ⟨s.setReg d (s.getReg src), ?_, rfl, h.setReg hd (h.regs src hs)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.writeReg, State.readReg,
      Width.bits]
  | @movRR32 d src hd =>
    refine ⟨s.writeReg .w32 d (s.readReg .w32 src), ?_, rfl, h.setReg hd (HasTy.int _)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst]
  | @movRI w d imm hd =>
    refine ⟨s.writeReg w d (imm.signExtend w.bits), ?_, rfl, h.setReg hd (hasTy_eq.mpr rfl)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst]
  | @movAbs d imm hd =>
    refine ⟨s.setReg d imm, ?_, rfl, h.setReg hd (hasTy_eq.mpr rfl)⟩
    simp [exec]
  | @leaRip d disp hd =>
    refine ⟨s.setReg d (s.rip + disp.signExtend 64), ?_, rfl,
      h.setReg hd (hasTy_eq.mpr (by rw [hrip]))⟩
    simp [exec, State.ea, State.writeReg]
  | @leaSp d disp v hd hΓ =>
    have hp : s.getReg .rsp = v := by
      have := h.sp
      rwa [hΓ, hasTy_eq] at this
    refine ⟨s.writeReg .w64 d ((s.ea (.sib (some .rsp) none disp)).setWidth 64), ?_, rfl,
      h.setReg hd (hasTy_eq.mpr (by simp [State.ea, hp]))⟩
    simp [exec]
  | @lea w d m hd =>
    refine ⟨s.writeReg w d ((s.ea m).setWidth w.bits), ?_, rfl, h.setReg hd (HasTy.int _)⟩
    simp [exec]
  | @loadField d b S writable off k disp τ hd hb hΓ hdisp hi =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := hΨ.fits _ l hl _ hm
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (off + k) := by
      rw [State.ea_byte s b hdisp, hva, byte_add]
    refine ⟨s.setReg d (s.load64 (a + BitVec.ofNat 64 (off + k))), ?_, rfl,
      h.setReg hd (h.heap _ l hl _ hm)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.read_w64 (h.canRead_bytes hl hfit), State.writeReg]
  | @storeField b src S off k disp τ hb hs hΓ hdisp hi hso hsub =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hw, hva⟩ := hasTy_ptr.mp hp
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := hΨ.fits _ l hl _ hm
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (off + k) := by
      rw [State.ea_byte s b hdisp, hva, byte_add]
    refine ⟨s.store64 (a + BitVec.ofNat 64 (off + k)) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeHeap hΨ hl hi hso ((h.regs src hs).sub hsub)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.readReg_w64, State.write_w64 _ (h.canWrite_bytes hl (hw rfl) hfit)]
  | @loadOwned d m k a p off S τ hd hm hat hv =>
    obtain ⟨hk, hoff⟩ := hat
    obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
    have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
    have hmem := ShapeOf.mem_of_valAt hv
    have hfit := h.owned.fits _ hin _ hmem
    have hty := h.owned.vals _ hin _ hmem
    simp only at hfit hty
    rw [owned_off] at hty
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hc : s.canRead (a + off) 8 = true :=
      State.canRead_of_canWrite (h.canWrite_owned hk hfit)
    refine ⟨s.setReg d (s.load64 (a + off)), ?_, rfl, h.setReg hd hty⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea, State.read_w64 hc, State.writeReg]
  | @storeOwned src m k a p off S hs hm hat hin8 =>
    obtain ⟨hk, hoff⟩ := hat
    obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
    have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hoa := owned_off a off
    have hc : s.canWrite (a + off) 8 = true := h.canWrite_owned hk hin8
    refine ⟨s.store64 (a + off) (s.getReg src), ?_, State.store64_rip _ _ _,
      h.writeOwned hΨ hk (S' := S.set off.toNat (Γ.regs src)) (lo := off.toNat) (cnt := 8)
        hin8 rfl
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hin8
          · exact h.owned.fits _ hin p (ShapeOf.mem_clear hp).1)
        (State.store64_regs _ _ _) (State.store64_flags _ _ _) (State.store64_perm _ _ _)
        (fun y hd => by rw [hoa] at hd; exact State.load64_store64_disjoint s _ hd)
        (fun x hx => by rw [hoa] at hx; exact State.mem_store_of_disjoint s .w64 _ _ _ hx)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp
          · right
            show HasTy fetch sys _ _ (Γ.regs src) _
            rw [hoa, State.load64_store64_same]
            exact h.regs src hs
          · exact .inl (ShapeOf.mem_clear hp))⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.readReg_w64, State.write_w64 _ hc]
  | @storeOwnedKeep src m k a p off S τ hs hm hat hv hsole hsub =>
    obtain ⟨hk, hoff⟩ := hat
    obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
    have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
    have hmem := ShapeOf.mem_of_valAt hv
    have hfit := h.owned.fits _ hin _ hmem
    simp only at hfit
    have hea : s.ea m = a + off := by rw [hm.sound h, hoff]
    have hoa := owned_off a off
    have hc : s.canWrite (a + off) 8 = true := h.canWrite_owned hk hfit
    have hw := h.writeOwned hΨ hk (S' := S) (lo := off.toNat) (cnt := 8) hfit rfl
      (h.owned.fits _ hin)
      (State.store64_regs _ _ (s.getReg src)) (State.store64_flags _ _ _)
      (State.store64_perm _ _ _)
      (fun y hd => by rw [hoa] at hd; exact State.load64_store64_disjoint s _ hd)
      (fun x hx => by rw [hoa] at hx; exact State.mem_store_of_disjoint s .w64 _ _ _ hx)
      (fun p hp => by
        by_cases hcl : p.1 + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ p.1
        · exact .inl ⟨hp, hcl⟩
        · -- it reaches into the bytes stored: it is the one value that does
          have e : p = (off.toNat, τ) :=
            ShapeOf.eq_of_sole hsole hp hmem hcl (by simp only; omega)
          subst e
          right
          show HasTy fetch sys _ _ τ _
          rw [hoa, State.load64_store64_same]
          exact (h.regs src hs).sub hsub)
    have hset : Γ.owned.set k (a, S) = Γ.owned := by
      rw [← hkeq]; exact List.set_getElem_self hklt
    rw [hset] at hw
    refine ⟨s.store64 (a + off) (s.getReg src), ?_, State.store64_rip _ _ _, hw⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.readReg_w64, State.write_w64 _ hc]
  | @loadIndexed d b x sc S writable off k disp c τ hd hb hΓ hΓx hD hi =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := hΨ.fits _ l hl _ hm
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (off + k) := by
      rw [State.ea_indexed s hx hD, hva, byte_add]
    refine ⟨s.setReg d (s.load64 (a + BitVec.ofNat 64 (off + k))), ?_, rfl,
      h.setReg hd (h.heap _ l hl _ hm)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.read_w64 (h.canRead_bytes hl hfit), State.writeReg]
  | @storeIndexed b src x sc S off k disp c τ hb hs hΓ hΓx hD hi hso hsub =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := hΨ.fits _ l hl _ hm
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (off + k) := by
      rw [State.ea_indexed s hx hD, hva, byte_add]
    refine ⟨s.store64 (a + BitVec.ofNat 64 (off + k)) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeHeap hΨ hl hi hso ((h.regs src hs).sub hsub)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.readReg_w64, State.write_w64 _ (h.canWrite_bytes hl (hwr rfl) hfit)]
  | @loadGlobal d base l k disp τ hd hl haddr hi =>
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := hΨ.fits _ l hl _ hm
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 k := by
      simp only [State.ea, hrip, haddr]
    refine ⟨s.setReg d (s.load64 (base + BitVec.ofNat 64 k)), ?_, rfl,
      h.setReg hd (h.heap _ l hl _ hm)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.read_w64 (h.canRead_bytes hl hfit), State.writeReg]
  | @storeGlobal src base l k disp τ hs hl hwr haddr hi hso hsub =>
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := hΨ.fits _ l hl _ hm
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 k := by
      simp only [State.ea, hrip, haddr]
    refine ⟨s.store64 (base + BitVec.ofNat 64 k) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeHeap hΨ hl hi hso ((h.regs src hs).sub hsub)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.readReg_w64, State.write_w64 _ (h.canWrite_bytes hl hwr hfit)]
  | @loadStack r d k i S disp τ hd hdisp hat hi =>
    obtain ⟨hk, rfl⟩ := hat
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := h.stackFits S (List.mem_of_getElem? hk) _ hm
    refine ⟨s.setReg r (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i))), ?_, rfl, h.setReg hd (h.stack k S hk _ hm)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.ea_byte s .rsp hdisp,
      State.read_w64 (State.canRead_of_canWrite (h.canWrite_piece hk hfit)), State.writeReg]
  | @loadStackIndexed r x sc d k i S disp c τ hd hΓx hD hat hi =>
    obtain ⟨hk, rfl⟩ := hat
    have hm := ShapeOf.mem_of_valAt hi
    have hfit := h.stackFits S (List.mem_of_getElem? hk) _ hm
    have hea : s.ea (.sib (some .rsp) (some (x, sc)) disp) = s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i) :=
      State.ea_indexed s (h.eqReg x.toReg_ne_rsp hΓx) hD
    refine ⟨s.setReg r (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i))), ?_, rfl, h.setReg hd (h.stack k S hk _ hm)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.read_w64 (State.canRead_of_canWrite (h.canWrite_piece hk hfit)), State.writeReg]
  | @storeStack src d k i S disp hs hdisp hat hle =>
    obtain ⟨hk, rfl⟩ := hat
    refine ⟨s.store64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeStack hΨ hk hle (h.regs src hs)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.ea_byte s .rsp hdisp,
      State.readReg_w64, State.write_w64 _ (h.canWrite_piece hk hle)]
  | @push r n hr hroom =>
    have hw : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true :=
      h.canWrite_push hroom
    refine ⟨(s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) (s.getReg r), ?_,
      State.store64_rip _ _ _, h.push hΨ hroom (h.regs r hr)⟩
    have hpush : s.push64 (s.getReg r)
        = .next ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) (s.getReg r)) := by
      simp only [State.push64, State.write64, hw, ite_true]
    simp [exec, hpush]
  | @pop r τ σ hr hst =>
    obtain ⟨hv, hw⟩ := h.pop hst
    have hc : s.canRead (s.getReg .rsp) 8 = true :=
      State.canRead_of_canWrite (h.canWrite_top hst rfl)
    refine ⟨(s.setReg .rsp (s.getReg .rsp + 8)).setReg r (s.load64 (s.getReg .rsp)), ?_, rfl,
      hw.setReg hr hv⟩
    simp [exec, State.pop64, State.read64, hc]
  | @popPlain r S σ hr hst h8 =>
    have hw := h.popAny hst h8
    have hc : s.canRead (s.getReg .rsp) 8 = true :=
      State.canRead_of_canWrite (h.canWrite_top hst h8)
    refine ⟨(s.setReg .rsp (s.getReg .rsp + 8)).setReg r (s.load64 (s.getReg .rsp)), ?_, rfl,
      hw.setReg hr (HasTy.int _)⟩
    simp [exec, State.pop64, State.read64, hc]
  | @aluRR op w d src hd hc =>
    obtain ⟨r, fl, he, hdef⟩ := op.eval_some (cf := s.flags.cf) (s.readReg w d) (s.readReg w src)
      (fun hrc => hc hrc _ h.flags)
    refine ⟨{ (if op.writesDst then s.setReg d (r.setWidth 64) else s) with flags := fl }, ?_, ?_,
      h.afterAlu hd hdef _⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, he, Result.ofOption,
          hwd, State.writeReg]
    · cases op.writesDst <;> rfl
  | @aluRI op w d imm hd hc =>
    obtain ⟨r, fl, he, hdef⟩ := op.eval_some (cf := s.flags.cf) (s.readReg w d)
      (imm.signExtend w.bits) (fun hrc => hc hrc _ h.flags)
    refine ⟨{ (if op.writesDst then s.setReg d (r.setWidth 64) else s) with flags := fl }, ?_, ?_,
      h.afterAlu hd hdef _⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, he, Result.ofOption,
          hwd, State.writeReg]
    · cases op.writesDst <;> rfl
  | @aluExact op d imm a hd hΓ hnc =>
    have hp := h.regs d hd
    rw [hΓ, hasTy_eq] at hp
    generalize hrf : op.apply a (imm.signExtend 64) = rf
    obtain ⟨r, fl⟩ := rf
    have he' : op.eval s.flags.cf (s.readReg .w64 d) (imm.signExtend 64) = some (r, fl) := by
      rw [State.readReg_w64, hp, AluOp.eval_eq_apply hnc, hrf]
    refine ⟨{ (if op.writesDst then s.setReg d r else s) with flags := fl }, ?_, ?_, ?_⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, he',
          Result.ofOption, hwd, State.writeReg]
    · cases op.writesDst <;> rfl
    · cases hwd : op.writesDst
      · simp only [Bool.cond_false]
        exact h.setFlags (P := (· = fl)) rfl
      · simp only [Bool.cond_true]
        exact (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = fl)) rfl
  | @aluExactRR op d src a b hd hs hΓ hΓ' hnc =>
    have hp := h.regs d hd
    have hp' := h.regs src hs
    rw [hΓ, hasTy_eq] at hp
    rw [hΓ', hasTy_eq] at hp'
    generalize hrf : op.apply a b = rf
    obtain ⟨r, fl⟩ := rf
    have he' : op.eval s.flags.cf (s.readReg .w64 d) (s.readReg .w64 src) = some (r, fl) := by
      rw [State.readReg_w64, State.readReg_w64, hp, hp', AluOp.eval_eq_apply hnc, hrf]
    refine ⟨{ (if op.writesDst then s.setReg d r else s) with flags := fl }, ?_, ?_, ?_⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, he',
          Result.ofOption, hwd, State.writeReg]
    · cases op.writesDst <;> rfl
    · cases hwd : op.writesDst
      · simp only [Bool.cond_false]
        exact h.setFlags (P := (· = fl)) rfl
      · simp only [Bool.cond_true]
        exact (h.setReg hd (hasTy_eq.mpr rfl)).setFlags (P := (· = fl)) rfl
  | @allocFrame k m imm hk hroom =>
    obtain ⟨rfl, hlt⟩ := hk
    refine ⟨{ s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 k) with
        flags := (subBorrow (s.getReg .rsp) (BitVec.ofNat 64 k) false).2 }, ?_, rfl,
      (h.allocFrame hΨ hroom).setFlags (P := Flags.Known) (Flags.ofResult_defined _ _ _)⟩
    simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, AluOp.eval,
      AluOp.writesDst, Result.ofOption, State.writeReg, State.readReg_w64, sext_small hlt,
      subBorrow_fst]
  | @freeFrame k imm top rest hk hst hlen =>
    obtain ⟨rfl, hlt⟩ := hk
    refine ⟨{ s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 k) with
        flags := (addCarry (s.getReg .rsp) (BitVec.ofNat 64 k) false).2 }, ?_, rfl,
      (h.freeFrame hst hlen).setFlags (P := Flags.Known) (Flags.ofResult_defined _ _ _)⟩
    simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, AluOp.eval,
      AluOp.writesDst, Result.ofOption, State.writeReg, State.readReg_w64, sext_small hlt,
      addCarry_fst]
  | @addPtr d S writable off k imm hd hΓ hk =>
    have hp := h.regs d hd
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hw, hva⟩ := hasTy_ptr.mp hp
    obtain ⟨rfl, hlt⟩ := hk
    have hv : HasTy fetch sys Ψ ix (.ptr l.shape writable (off + k))
        (s.getReg d + BitVec.ofNat 64 k) :=
      hasTy_ptr.mpr ⟨a, l, hl, rfl, hw, by rw [hva, byte_add]⟩
    refine ⟨{ s.setReg d (s.getReg d + BitVec.ofNat 64 k) with
        flags := (addCarry (s.getReg d) (BitVec.ofNat 64 k) false).2 }, ?_, rfl,
      (h.setReg hd hv).setFlags (P := Flags.Known) (Flags.ofResult_defined _ _ _)⟩
    simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, AluOp.eval,
      AluOp.writesDst, Result.ofOption, State.writeReg, State.readReg_w64, sext_small hlt,
      addCarry_fst]
  | @strNext d hd hΓ =>
    have hp := h.regs d hd
    rw [hΓ] at hp
    obtain ⟨a, l, off, hl, hoff, hva⟩ := hasTy_str.mp hp
    simp only [↓reduceIte] at hoff
    have hsz := hΨ.size_lt a l hl
    have hv : HasTy fetch sys Ψ ix (.str false) (s.getReg d + 1) :=
      hasTy_str.mpr ⟨a, l, off + 1, hl, by simpa using hoff, by
        rw [hva]
        simp only [Layout.size] at hsz
        bv_omega⟩
    refine ⟨{ s.setReg d (s.getReg d + 1) with
        flags := (addCarry (s.getReg d) 1 false).2 }, ?_, rfl,
      (h.setReg hd hv).setFlags (P := Flags.Known) (Flags.ofResult_defined _ _ _)⟩
    have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
    simp only [exec, State.readRM, State.writeRM, Operands.src, Operands.dst,
      AluOp.eval, AluOp.writesDst, Result.ofOption, State.writeReg, State.readReg_w64,
      Width.bits, e1, bind, pure, BitVec.setWidth_eq, ↓reduceIte]
    simp [Result.bind, addCarry_fst]
  | @testExact r r' a b hr hr' hΓ hΓ' =>
    have hp := h.regs r hr
    have hp' := h.regs r' hr'
    rw [hΓ, hasTy_eq] at hp
    rw [hΓ', hasTy_eq] at hp'
    refine ⟨{ s with flags := .ofResult (a &&& b) false false }, ?_, rfl,
      h.setFlags (P := (· = Flags.ofResult (a &&& b) false false)) rfl⟩
    simp [exec, State.readRM, State.readRI, State.readReg_w64, hp, hp']

/-! ## All typed instructions -/

/-- What the induction on step count provides: every program point is safe
for `n` steps from any state matching its context at count `n`, however the
memory typing has grown by then. -/
def SafeUpTo (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) : Prop :=
  ∀ k, k ≤ n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ a Δ, Φ a Δ → ∀ s : State, s.rip = a →
    WellTyped fetch sys Ψ' k Δ s → SafeN fetch sys k s

variable {Ψ' : MemTy}

/-- Entering code that accepts the current context is safe. -/
theorem SafeUpTo.accepts {n : Nat} (ih : SafeUpTo Φ fetch sys Ψ n) (he : Ψ.Ext Ψ') (hΨ : Ψ'.WF)
    {a : BitVec 64} {Γ : Ctx}
    {s : State} (hacc : Accepts Φ a Γ) (hr : s.rip = a)
    (h : WellTyped fetch sys Ψ' (n + 1) Γ s) : SafeN fetch sys n s := by
  obtain ⟨Δ, hΔ, hsub⟩ := hacc
  exact ih n (Nat.le_refl n) Ψ' he hΨ a Δ hΔ s hr ((h.sub hsub).mono (Nat.le_succ n))

/-- A typed instruction, run in a matching state at the right address, has an
acceptable outcome, and any state it continues to is safe for the remaining steps. -/
theorem HasType.sound {next : BitVec 64} {Γ : Ctx} {i : Instr} {n : Nat}
    (ht : HasType Φ fetch sys Ψ next Γ i) (he : Ψ.Ext Ψ') (hΨ : Ψ'.WF)
    (ih : SafeUpTo Φ fetch sys Ψ n) {s : State}
    (h : WellTyped fetch sys Ψ' (n + 1) Γ s) (hrip : s.rip = next) :
    (exec sys i s).isSafe = true ∧ ∀ s', exec sys i s = .next s' → SafeN fetch sys n s' := by
  induction ht generalizing s Ψ' with
  | weaken hsem _ ihw => exact ihw he hΨ (hsem Ψ' he hΨ _ _ h) hrip
  | @grow ι Γ Γ' i hsem _ ihc =>
    obtain ⟨Ψ₂, he₂, hΨ₂, x, hx⟩ := hsem Ψ' he hΨ _ _ h
    exact ihc x (he.trans he₂) hΨ₂ hx hrip
  | straight hst hacc =>
    obtain ⟨s', hex, hr, hw⟩ := (hst.ext he).sound hΨ h hrip
    rw [hex]
    refine ⟨rfl, fun s'' heq => ?_⟩
    cases heq
    exact ih.accepts he hΨ hacc (hr.trans hrip) hw
  | @jmp Γ d hacc =>
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact ih.accepts he hΨ hacc (by rw [← hrip]) (h.congr rfl rfl rfl rfl)
  | @jcc Γ c d hdec hacc hfall =>
    obtain ⟨b, hb⟩ := hdec _ h.flags
    cases b
    · have hex : exec sys (.jcc c d) s = .next s := by simp [exec, hb, Result.ofOption]
      rw [hex]
      refine ⟨rfl, fun s' heq => ?_⟩
      cases heq
      exact ih.accepts he hΨ (hfall _ h.flags hb) hrip h
    · have hex : exec sys (.jcc c d) s = .next { s with rip := s.rip + d.signExtend 64 } := by
        simp [exec, hb, Result.ofOption]
      rw [hex]
      refine ⟨rfl, fun s' heq => ?_⟩
      cases heq
      exact ih.accepts he hΨ (hacc _ h.flags hb) (by rw [← hrip]) (h.congr rfl rfl rfl rfl)
  | @call Γ ret d m hroom hret hacc =>
    have hw : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true :=
      h.canWrite_push hroom
    -- The return address is a code pointer: by the induction hypothesis the
    -- instruction after the call is safe in any state matching its context.
    have hv : HasTy fetch sys Ψ' (n + 1) (.code ret) s.rip := by
      rw [hasTy_code]
      intro k hk Ψ'' he' hΨ'' t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' next ret hret t (ht.trans hrip) hwt
    have hex : exec sys (.call (.rel d)) s
        = .next { (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip with
            rip := s.rip + d.signExtend 64 } := by
      have hpush : s.push64 s.rip
          = .next ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip) := by
        simp only [State.push64, State.write64, hw, ite_true]
      simp [exec, hpush]
    have hw' := h.push hΨ hroom hv
    generalize (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip = s₁
      at hex hw'
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact ih.accepts he hΨ hacc (by rw [← hrip]) (hw'.congr rfl rfl rfl rfl)
  | @callAll Γ ret d m hroom hret hacc =>
    have hw : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true :=
      h.canWrite_push hroom
    -- The return address is code ready for each of the contexts: by the
    -- induction hypothesis, since the instruction after the call is typed
    -- for each.
    have hv : HasTy fetch sys Ψ' (n + 1) (.codeAll ret) s.rip := by
      rw [hasTy_codeAll]
      intro x
      rw [hasTy_code]
      intro k hk Ψ'' he' hΨ'' t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' next (ret x) (hret x) t (ht.trans hrip) hwt
    have hex : exec sys (.call (.rel d)) s
        = .next { (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip with
            rip := s.rip + d.signExtend 64 } := by
      have hpush : s.push64 s.rip
          = .next ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip) := by
        simp only [State.push64, State.write64, hw, ite_true]
      simp [exec, hpush]
    have hw' := h.push hΨ hroom hv
    generalize (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip = s₁
      at hex hw'
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact ih.accepts he hΨ hacc (by rw [← hrip]) (hw'.congr rfl rfl rfl rfl)
  | @ret Γ Δ σ hst hsub =>
    obtain ⟨hv, hw⟩ := h.pop hst
    rw [hasTy_code] at hv
    have hc : s.canRead (s.getReg .rsp) 8 = true :=
      State.canRead_of_canWrite (h.canWrite_top hst rfl)
    have hex : exec sys .ret s
        = .next { s.setReg .rsp (s.getReg .rsp + 8) with rip := s.load64 (s.getReg .rsp) } := by
      simp [exec, State.pop64, State.read64, hc]
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hv n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ _ rfl
      (((hw.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | syscall hret hacc =>
    obtain ⟨s', hex, hr, Ψ₂, he₂, hΨ₂, hw⟩ := hret Ψ' he hΨ _ _ h
    have hex' : exec sys .syscall s = .next s' := hex
    rw [hex']
    refine ⟨rfl, fun s'' heq => ?_⟩
    cases heq
    exact ih.accepts (he.trans he₂) hΨ₂ hacc (hr.trans hrip) hw
  | syscallExit hexit =>
    obtain ⟨c, hex⟩ := hexit Ψ' he hΨ _ _ h
    have hex' : exec sys .syscall s = .exit c := hex
    rw [hex']
    exact ⟨rfl, fun s' heq => nomatch heq⟩
  | @jmpInd Γ Δ rm hcode hsub =>
    obtain ⟨v, hv, hp⟩ := (hcode.ext he).sound h hΨ hrip
    rw [hasTy_code] at hp
    have hex : exec sys (.jmp (.ind rm)) s = .next { s with rip := v } := by
      simp [exec, hv]
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ _ rfl
      (((h.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @callInd Γ Δ ret rm m hcode hroom hret hsub =>
    obtain ⟨v, hv, hp⟩ := (hcode.ext he).sound h hΨ hrip
    rw [hasTy_code] at hp
    have hw : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true :=
      h.canWrite_push hroom
    have hra : HasTy fetch sys Ψ' (n + 1) (.code ret) s.rip := by
      rw [hasTy_code]
      intro k hk Ψ'' he' hΨ'' t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' next ret hret t (ht.trans hrip) hwt
    have hex : exec sys (.call (.ind rm)) s
        = .next { (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip with
            rip := v } := by
      have hpush : s.push64 s.rip
          = .next ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip) := by
        simp only [State.push64, State.write64, hw, ite_true]
      simp [exec, hv, hpush]
    have hw' := h.push hΨ hroom hra
    generalize (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip = s₁
      at hex hw'
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ _ rfl
      (((hw'.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @sem ι Γ Γ' i hsem hacc =>
    obtain ⟨s', x, hex, hr, Ψ₂, he₂, hΨ₂, hw⟩ := hsem Ψ' he hΨ _ _ h hrip
    rw [hex]
    refine ⟨rfl, fun s'' heq => ?_⟩
    cases heq
    exact ih.accepts (he.trans he₂) hΨ₂ (hacc x) (hr.trans hrip) hw
  | @unreachable Γ i hun => exact absurd h (hun Ψ' he hΨ _ _)
  | @fnPtr Γ i r a sig hr hΓ hat _ ihc =>
    have hp := h.eqReg hr hΓ
    -- By the induction hypothesis the function is safe to enter for any caller.
    have hv : HasTy fetch sys Ψ' (n + 1) sig.ty (s.getReg r) := by
      rw [hasTy_fn]
      intro k hk Ψ'' he' hΨ'' saved ret rest room hK t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' a _ (hat saved ret rest room hK) t
        (ht.trans hp) hwt
    exact ihc he hΨ (h.retype hr hv) hrip
  | @callFn Γ ret rm sig m hholds hroom hret hargs hsp hback hneed hgives hown =>
    obtain ⟨v, hv, hp⟩ := (hholds.ext he).sound h hΨ hrip
    rw [hasTy_fn] at hp
    have hw : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true :=
      h.canWrite_push hroom
    have hra : HasTy fetch sys Ψ' (n + 1) (.code ret) s.rip := by
      rw [hasTy_code]
      intro k hk Ψ'' he' hΨ'' t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' next ret hret t (ht.trans hrip) hwt
    have hex : exec sys (.call (.ind rm)) s
        = .next { (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip with
            rip := v } := by
      have hpush : s.push64 s.rip
          = .next ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip) := by
        simp only [State.push64, State.write64, hw, ite_true]
      simp [exec, hv, hpush]
    have hw' := h.push hΨ hroom hra
    generalize (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip = s₁
      at hex hw'
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ (Γ.moveSp (-8)).regs ret Γ.stack m
      (.ofBack hgives hback hneed) _ rfl
      (((hw'.sub (Δ := sig.entry (Γ.moveSp (-8)).regs ret Γ.stack m)
        ⟨fun r hr => by
            show Sub ((Γ.moveSp (-8)).regs r) _
            rw [CtxOf.moveSp_regs hr]
            exact hargs r hr,
          .refl _, rfl, fun _ _ => trivial, by
            show Sub ((Γ.moveSp (-8)).regs .rsp) _
            rw [CtxOf.moveSp_sp]
            exact hsp, hown, hback.above⟩).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @jmpFn Γ ret rm sig saved rest room hholds hK hsub =>
    obtain ⟨v, hv, hp⟩ := (hholds.ext he).sound h hΨ hrip
    rw [hasTy_fn] at hp
    have hex : exec sys (.jmp (.ind rm)) s = .next { s with rip := v } := by
      simp [exec, hv]
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ saved ret rest room hK _ rfl
      (((h.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @fnPtrAll ι inst Γ i r a sig hr hΓ hat _ ihc =>
    have hp := h.eqReg hr hΓ
    -- By the induction hypothesis the function is safe to enter for any
    -- caller; a caller that speaks of sequences is one that speaks of the
    -- values they stand for.
    have hv : HasTy fetch sys Ψ' (n + 1) sig.ty (s.getReg r) := by
      rw [hasTy_fnAll]
      intro k hk Ψ'' he' hΨ'' saved ret rest room frame above hK t ht hwt
      refine ih k (by omega) Ψ'' (he.trans he') hΨ'' a _
        (hat saved (fun x => ret (Chosen.enc x)) rest room frame above hK.ofRaw) t (ht.trans hp) ?_
      exact hwt.sub ⟨fun _ _ => .refl _,
        .cons (.slot (.codeAllMap ret fun s => Chosen.enc (Chosen.dec (ι := ι) s))) (.refl _), rfl,
        fun _ hf => hf, .refl _, rfl, rfl⟩
    exact ihc he hΨ (h.retype hr hv) hrip
  | @callFnAll ι inst Γ ret rm sig m frame hholds hroom hret hargs hsp hback hneed hgives hframe
      hown =>
    obtain ⟨v, hv, hp⟩ := (hholds.ext he).sound h hΨ hrip
    rw [hasTy_fnAll] at hp
    have hw : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true :=
      h.canWrite_push hroom
    have hra : HasTy fetch sys Ψ' (n + 1) (.codeAll fun q => ret (Chosen.dec q)) s.rip := by
      rw [hasTy_codeAll]
      intro q
      rw [hasTy_code]
      intro k hk Ψ'' he' hΨ'' t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' next _ (hret (Chosen.dec q)) t
        (ht.trans hrip) hwt
    have hex : exec sys (.call (.ind rm)) s
        = .next { (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip with
            rip := v } := by
      have hpush : s.push64 s.rip
          = .next ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip) := by
        simp only [State.push64, State.write64, hw, ite_true]
      simp [exec, hv, hpush]
    have hw' := h.push hΨ hroom hra
    generalize (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip = s₁
      at hex hw'
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    have hK : sig.CallerOk (Γ.moveSp (-8)).regs ret Γ.stack m frame Γ.above :=
      ⟨fun x => .ofBack (hgives x) (hback x) hneed, hframe, fun x => (hback x).above.symm⟩
    exact hp n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ (Γ.moveSp (-8)).regs _ Γ.stack m frame Γ.above
      hK.toRaw _ rfl
      (((hw'.sub (Δ := sig.entry (Γ.moveSp (-8)).regs ret Γ.stack m frame Γ.above)
        ⟨fun r hr => by
            show Sub ((Γ.moveSp (-8)).regs r) _
            rw [CtxOf.moveSp_regs hr]
            exact hargs r hr,
          .refl _, rfl, fun _ _ => trivial, by
            show Sub ((Γ.moveSp (-8)).regs .rsp) _
            rw [CtxOf.moveSp_sp]
            exact hsp, hown, rfl⟩).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @jmpFnAll ι inst Γ ret rm sig saved rest room frame above hholds hK hsub =>
    obtain ⟨v, hv, hp⟩ := (hholds.ext he).sound h hΨ hrip
    rw [hasTy_fnAll] at hp
    have hex : exec sys (.jmp (.ind rm)) s = .next { s with rip := v } := by
      simp [exec, hv]
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ saved _ rest room frame above hK.toRaw _ rfl
      (((h.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @cover ι Γ Γ' i hsem _ ihc =>
    obtain ⟨x, hx⟩ := hsem Ψ' he hΨ _ _ h
    exact ihc x he hΨ hx hrip
  | @codePtr Γ Δ i r a hr hΓ hΦ _ ihc =>
    have hp := h.regs r hr
    rw [hΓ, hasTy_eq] at hp
    -- By the induction hypothesis the code at `a` is safe in any state matching `Δ`.
    have hv : HasTy fetch sys Ψ' (n + 1) (.code Δ) (s.getReg r) := by
      rw [hasTy_code]
      intro k hk Ψ'' he' hΨ'' t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' a Δ hΦ t (ht.trans hp) hwt
    exact ihc he hΨ (h.retype hr hv) hrip

/-! ## Programs -/

/-- In a well-typed program, every program point is safe for `n` steps from
any state matching its context at step count `n`. -/
theorem safeUpTo (hP : ProgramOk Φ fetch sys Ψ) (n : Nat) :
    SafeUpTo Φ fetch sys Ψ n := by
  induction n with
  | zero =>
    intro k hk _ _ _ a Δ _ s _ _
    have : k = 0 := by omega
    subst this
    trivial
  | succ n ih =>
    intro k hk Ψ' he hΨ a Δ hΔ s hr hw
    by_cases hkn : k ≤ n
    · exact ih k hkn Ψ' he hΨ a Δ hΔ s hr hw
    · have : k = n + 1 := by omega
      subst this
      obtain ⟨i, len, hf, ht⟩ := hP a Δ hΔ
      have := ht.sound he hΨ ih (s := { s with rip := s.rip + len })
        (hw.congr rfl rfl rfl rfl) (by rw [← hr])
      simpa only [SafeN, TypedAsm.step, hr, hf] using this

/-- **Soundness.** A well-typed program, started in a well-typed state, with a
well-formed memory typing, is safe: it
never gets stuck and never faults: no page fault, no invalid opcode and no
divide error. -/
theorem soundness {s : State} (hP : ProgramOk Φ fetch sys Ψ) (hΨ : Ψ.WF)
    (hs : StateOk Φ fetch sys Ψ s) : Safe fetch sys s := by
  obtain ⟨Γ, hΓ, hw⟩ := hs
  exact safe_of_safeN (fun n =>
    safeUpTo hP n n (Nat.le_refl n) Ψ (.refl _) hΨ s.rip Γ hΓ s rfl (hw n))

end TypedAsm
