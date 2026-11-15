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
  | orErr _ ih => exact hasTy_orErr.mpr (.inr (ih hv))
  | orErrMono _ ih => exact hasTy_orErr.mpr ((hasTy_orErr.mp hv).imp id ih)

theorem SubList.length_eq {σ ρ : List Ty} (h : SubList σ ρ) : σ.length = ρ.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem SubList.get {σ ρ : List Ty} (h : SubList σ ρ) :
    ∀ (i : Nat) (υ : Ty), ρ[i]? = some υ → ∃ τ, σ[i]? = some τ ∧ Sub τ υ := by
  induction h with
  | nil => intro i υ h; simp at h
  | cons hs _ ih =>
    intro i υ h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨_, by simp, h ▸ hs⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simpa using ih i υ h

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

/-- A run of 8-byte slots of a region does not overlap a slot outside the run. -/
theorem disjoint_range_slot {a : BitVec 64} {lo cnt j N : Nat} (hc : 0 < cnt)
    (hout : j < lo ∨ lo + cnt ≤ j) (hr : 8 * (lo + cnt) ≤ N) (hj : 8 * j + 8 ≤ N)
    (hN : N < 2 ^ 64) :
    Disjoint (a + BitVec.ofNat 64 (8 * lo)) (8 * cnt) (a + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega

/-- Two different 8-byte slots of one region do not overlap. -/
theorem disjoint_slots {a : BitVec 64} {i j N : Nat} (hij : i ≠ j) (hi : 8 * i + 8 ≤ N)
    (hj : 8 * j + 8 ≤ N) (hN : N < 2 ^ 64) :
    Disjoint (a + BitVec.ofNat 64 (8 * i)) 8 (a + BitVec.ofNat 64 (8 * j)) 8 := by
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

/-- The address of stack slot `j`, measured from the bottom of the stack region. -/
theorem slot_addr (Γ : Ctx) (s : State) (j : Nat) :
    stackBase Γ s + BitVec.ofNat 64 (8 * Γ.room + 8 * j)
      = s.getReg .rsp + BitVec.ofNat 64 (8 * j) := by
  simp only [stackBase]
  bv_omega

/-- The last byte of a block's text lies outside any run of fields, of its
own block or of another. -/
theorem MemTy.WF.text_outside_fields (hΨ : Ψ.WF) {a b : BitVec 64} {l l' : Layout}
    {lo cnt : Nat} (hl : Ψ a = some l) (hle : lo + cnt ≤ l.fields.length) (hc : 0 < cnt)
    (hl' : Ψ b = some l') (ht : l'.text ≠ 0) :
    BitVec.ofNat 64 (8 * cnt) ≤
      (b + BitVec.ofNat 64 (l'.size - 1)) - (a + BitVec.ofNat 64 (8 * lo)) := by
  have hsz := hΨ.size_lt a l hl
  have hsz' := hΨ.size_lt b l' hl'
  by_cases hab : b = a
  · subst hab
    have e : l' = l := Option.some.inj (hl'.symm.trans hl)
    subst e
    simp only [Layout.size] at hsz ⊢
    bv_omega
  · have hpos := hΨ.nonempty b l' hl'
    have hd := (hΨ.disjoint a b l l' hl hl' (Ne.symm hab)).mono (o := 8 * lo) (p := l'.size - 1)
      (n' := 8 * cnt) (m' := 1) hsz hsz' (by simp only [Layout.size]; omega) (by omega)
      (by omega) (by omega)
    exact hd.1 (by decide)

/-- Bytes unchanged outside a range leave every 64-bit value disjoint from
the range unchanged. -/
theorem State.load64_eq_of_outside {s s' : State} {base y : BitVec 64} {m : Nat}
    (hm : m < 2 ^ 64) (hm0 : m ≠ 0)
    (hmem : ∀ x, BitVec.ofNat 64 m ≤ x - base → s'.mem x = s.mem x)
    (hd : Disjoint base m y 8) : s'.load64 y = s.load64 y := by
  have hd' := hd.of_pos hm0 (by decide)
  refine State.load64_congr_bytes (fun j hj => hmem _ ?_)
  bv_omega

/-! ## Keeping a state well typed -/

namespace WellTyped

variable {Γ : Ctx} {s : State}

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
    stackSize_lt := h.stackSize_lt
    stack := fun i τ hi => by rw [hg, State.load64_congr hm]; exact h.stack i τ hi
    heapPerm := fun a l hl => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm a l hl
    heap := fun a l hl i τ hi => by rw [State.load64_congr hm]; exact h.heap a l hl i τ hi
    stackHeap := fun a l hl => by rw [hb]; exact h.stackHeap a l hl
    text := fun a l hl ht => by rw [hm]; exact h.text a l hl ht
    sp := by rw [hg]; exact h.sp }

/-- A state matching a context matches every weaker context. -/
theorem sub {Δ : Ctx} (h : WellTyped fetch sys Ψ ix Γ s) (hs : CtxSub Γ Δ) : WellTyped fetch sys Ψ ix Δ s := by
  have hl := hs.stack.length_eq
  have hb : stackBase Δ s = stackBase Γ s := by simp only [stackBase, hs.room]
  have hz : stackSize Δ = stackSize Γ := by simp only [stackSize, hs.room, hl]
  exact {
    regs := fun r hr => (h.regs r hr).sub (hs.regs r hr)
    flags := hs.flags _ h.flags
    stackPerm := by rw [hb, hz]; exact h.stackPerm
    stackSize_lt := by rw [hz]; exact h.stackSize_lt
    stack := fun i υ hi => by
      obtain ⟨τ, hτ, hsub⟩ := hs.stack.get i υ hi
      exact (h.stack i τ hτ).sub hsub
    heapPerm := h.heapPerm
    heap := h.heap
    stackHeap := fun a l hl => by rw [hb, hz]; exact h.stackHeap a l hl
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
    stackSize_lt := h.stackSize_lt
    stack := fun i τ' hi => by rw [hsp, State.load64_congr hm]; exact h.stack i τ' hi
    heapPerm := fun a l hl => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm a l hl
    heap := fun a l hl i τ' hi => by rw [State.load64_congr hm]; exact h.heap a l hl i τ' hi
    stackHeap := fun a l hl => by rw [hb]; exact h.stackHeap a l hl
    text := fun a l hl ht => by rw [hm]; exact h.text a l hl ht
    sp := by
      rw [hsp]
      simp only [CtxOf.setReg, Ne.symm hr, ↓reduceIte]
      exact h.sp }

/-- Replacing the flags with ones that satisfy the new context's flags predicate. -/
theorem setFlags {f : Flags} {P : Flags → Prop} (h : WellTyped fetch sys Ψ ix Γ s) (hf : P f) :
    WellTyped fetch sys Ψ ix { Γ with flags := P } { s with flags := f } :=
  { regs := h.regs, flags := hf, stackPerm := h.stackPerm, stackSize_lt := h.stackSize_lt,
    stack := h.stack, heapPerm := h.heapPerm, heap := h.heap, stackHeap := h.stackHeap,
    text := h.text,
    sp := h.sp }

/-- The last byte of a block's text lies outside any run of slots of the
stack region. -/
theorem text_outside_stack {lo cnt : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hle : lo + cnt ≤ Γ.room + Γ.stack.length) (hc : 0 < cnt) {b : BitVec 64} {l' : Layout}
    (hl' : Ψ b = some l') (ht : l'.text ≠ 0) :
    BitVec.ofNat 64 (8 * cnt) ≤
      (b + BitVec.ofNat 64 (l'.size - 1)) - (stackBase Γ s + BitVec.ofNat 64 (8 * lo)) := by
  have hpos := hΨ.nonempty b l' hl'
  have hd := (h.stackHeap b l' hl').mono (o := 8 * lo) (p := l'.size - 1) (n' := 8 * cnt)
    (m' := 1) h.stackSize_lt (hΨ.size_lt b l' hl') (by simp only [stackSize]; omega) (by omega)
    (by omega) (by omega)
  exact hd.1 (by decide)

/-- Field `i` of a block is readable. -/
theorem canRead_field {a : BitVec 64} {l : Layout} {i : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hl : Ψ a = some l) (hi : i < l.fields.length) :
    s.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true :=
  State.canRead_sub (h.heapPerm a l hl).1 (by simp only [Layout.size]; omega)

/-- Field `i` of a writable block is writable. -/
theorem canWrite_field {a : BitVec 64} {l : Layout} {i : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hl : Ψ a = some l) (hw : l.writable = true) (hi : i < l.fields.length) :
    s.canWrite (a + BitVec.ofNat 64 (8 * i)) 8 = true :=
  State.canWrite_sub ((h.heapPerm a l hl).2 hw) (by simp only [Layout.size]; omega)

/-- Stack slot `i` is writable. -/
theorem canWrite_slot {i : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hi : i < Γ.stack.length) :
    s.canWrite (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) 8 = true := by
  have := State.canWrite_sub h.stackPerm (o := 8 * Γ.room + 8 * i) (m := 8)
    (by simp only [stackSize]; omega)
  rwa [slot_addr] at this

/-- When there is room, the slot below `rsp` is writable. -/
theorem canWrite_push {n : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hroom : Γ.room = n + 1) :
    s.canWrite (s.getReg .rsp - 8) 8 = true := by
  have := State.canWrite_sub h.stackPerm (o := 8 * n) (m := 8)
    (by simp only [stackSize, hroom]; omega)
  have e : stackBase Γ s + BitVec.ofNat 64 (8 * n) = s.getReg .rsp - 8 := by
    simp only [stackBase, hroom]; bv_omega
  rwa [e] at this

/-- Storing a value of the field's type into field `i` of a block. -/
theorem storeField {a : BitVec 64} {l : Layout} {i : Nat} {τ : Ty} {v : BitVec 64}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hl : Ψ a = some l) (hi : l.fields[i]? = some τ)
    (hv : HasTy fetch sys Ψ ix τ v) :
    WellTyped fetch sys Ψ ix Γ (s.store64 (a + BitVec.ofNat 64 (8 * i)) v) := by
  have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
  have hsz := hΨ.size_lt a l hl
  have hg : ∀ r, (s.store64 (a + BitVec.ofNat 64 (8 * i)) v).getReg r = s.getReg r :=
    fun r => by simp only [State.getReg, State.store64_regs]
  have hb : stackBase Γ (s.store64 (a + BitVec.ofNat 64 (8 * i)) v) = stackBase Γ s := by
    simp only [stackBase, hg]
  have hp := State.store64_perm s (a + BitVec.ofNat 64 (8 * i)) v
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [State.store64_flags]; exact h.flags
    stackPerm := by rw [hb, State.canWrite_congr hp]; exact h.stackPerm
    stackSize_lt := h.stackSize_lt
    stack := fun j τ' hj => by
      have hjlt : j < Γ.stack.length := (List.getElem?_eq_some_iff.mp hj).1
      have hd := (h.stackHeap a l hl).symm.mono (o := 8 * i) (p := 8 * Γ.room + 8 * j)
        (n' := 8) (m' := 8) hsz h.stackSize_lt (by simp only [Layout.size]; omega)
        (by simp only [stackSize]; omega) (by omega) (by omega)
      rw [slot_addr] at hd
      rw [hg, State.load64_store64_disjoint s v hd]
      exact h.stack j τ' hj
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      have hjlt : j < l'.fields.length := (List.getElem?_eq_some_iff.mp hj).1
      by_cases hab : b = a
      · subst hab
        have e : l' = l := Option.some.inj (hl'.symm.trans hl)
        subst e
        by_cases hij : j = i
        · subst hij
          have e : τ' = τ := Option.some.inj (hj.symm.trans hi)
          subst e
          rw [State.load64_store64_same]
          exact hv
        · rw [State.load64_store64_disjoint s v (disjoint_slots (N := l'.size) (Ne.symm hij)
            (by simp only [Layout.size]; omega) (by simp only [Layout.size]; omega) hsz)]
          exact h.heap b l' hl' j τ' hj
      · have hd := (hΨ.disjoint a b l l' hl hl' (Ne.symm hab)).mono (o := 8 * i) (p := 8 * j)
          (n' := 8) (m' := 8) hsz (hΨ.size_lt b l' hl') (by simp only [Layout.size]; omega)
          (by simp only [Layout.size]; omega) (by omega) (by omega)
        rw [State.load64_store64_disjoint s v hd]
        exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb]; exact h.stackHeap b l' hl'
    text := fun b l' hl' ht => by
      have e : (s.store64 (a + BitVec.ofNat 64 (8 * i)) v).mem (b + BitVec.ofNat 64 (l'.size - 1))
          = s.mem (b + BitVec.ofNat 64 (l'.size - 1)) :=
        State.mem_store_of_disjoint s .w64 _ _ v
          (hΨ.text_outside_fields hl (lo := i) (cnt := 1) (by omega) (by omega) hl' ht)
      rw [e]; exact h.text b l' hl' ht
    sp := by rw [hg]; exact h.sp }

/-- Storing into stack slot `i`; the slot takes the stored value's type. -/
theorem storeStack {i : Nat} {τ : Ty} {v : BitVec 64} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hi : i < Γ.stack.length) (hv : HasTy fetch sys Ψ ix τ v) :
    WellTyped fetch sys Ψ ix { Γ with stack := Γ.stack.set i τ }
      (s.store64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) v) := by
  have hg : ∀ r, (s.store64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) v).getReg r = s.getReg r :=
    fun r => by simp only [State.getReg, State.store64_regs]
  have hp := State.store64_perm s (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) v
  have hz : stackSize { Γ with stack := Γ.stack.set i τ } = stackSize Γ := by
    simp only [stackSize, List.length_set]
  have hb : stackBase { Γ with stack := Γ.stack.set i τ }
      (s.store64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) v) = stackBase Γ s := by
    simp only [stackBase, hg]
  have hlt := h.stackSize_lt
  simp only [stackSize] at hlt
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [State.store64_flags]; exact h.flags
    stackPerm := by rw [hb, hz, State.canWrite_congr hp]; exact h.stackPerm
    stackSize_lt := by rw [hz]; exact h.stackSize_lt
    stack := fun j τ' hj => by
      rw [hg]
      by_cases hji : j = i
      · subst hji
        rw [List.getElem?_set_self hi] at hj
        cases hj
        rw [State.load64_store64_same]
        exact hv
      · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
        have hjlt : j < Γ.stack.length := (List.getElem?_eq_some_iff.mp hj).1
        rw [State.load64_store64_disjoint s v (disjoint_slots (N := 8 * Γ.stack.length)
          (Ne.symm hji) (by omega) (by omega) (by omega))]
        exact h.stack j τ' hj
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      have hjlt : j < l'.fields.length := (List.getElem?_eq_some_iff.mp hj).1
      have hd := (h.stackHeap b l' hl').mono (o := 8 * Γ.room + 8 * i) (p := 8 * j)
        (n' := 8) (m' := 8) h.stackSize_lt (hΨ.size_lt b l' hl') (by simp only [stackSize]; omega)
        (by simp only [Layout.size]; omega) (by omega) (by omega)
      rw [slot_addr] at hd
      rw [State.load64_store64_disjoint s v hd]
      exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl'
    text := fun b l' hl' ht => by
      have hout := h.text_outside_stack hΨ (lo := Γ.room + i) (cnt := 1)
        (by omega) (by omega) hl' ht
      rw [show 8 * (Γ.room + i) = 8 * Γ.room + 8 * i by omega, slot_addr] at hout
      have e : (s.store64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) v).mem
          (b + BitVec.ofNat 64 (l'.size - 1)) = s.mem (b + BitVec.ofNat 64 (l'.size - 1)) :=
        State.mem_store_of_disjoint s .w64 _ _ v hout
      rw [e]; exact h.text b l' hl' ht
    sp := by rw [hg]; exact h.sp }

/-- Pushing a value of type `τ` when there is room. -/
theorem push₀ {n : Nat} {τ : Ty} {v : BitVec 64} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hint : Γ.regs .rsp = .int) (hroom : Γ.room = n + 1) (hv : HasTy fetch sys Ψ ix τ v) :
    WellTyped fetch sys Ψ ix { Γ with stack := τ :: Γ.stack, room := n }
      ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v) := by
  have hg : ∀ r, ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v).getReg r
      = (s.setReg .rsp (s.getReg .rsp - 8)).getReg r :=
    fun r => by simp only [State.getReg, State.store64_regs]
  have hsp : ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v).getReg .rsp
      = s.getReg .rsp - 8 := by rw [hg, State.getReg_setReg_same]
  have hp : ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v).perm = s.perm :=
    State.store64_perm _ _ _
  have hm : (s.setReg .rsp (s.getReg .rsp - 8)).mem = s.mem := rfl
  have hz : stackSize { Γ with stack := τ :: Γ.stack, room := n } = stackSize Γ := by
    simp only [stackSize, hroom, List.length_cons]; omega
  have hb : stackBase { Γ with stack := τ :: Γ.stack, room := n }
      ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v) = stackBase Γ s := by
    simp only [stackBase, hsp, hroom]; bv_omega
  have hlt := h.stackSize_lt
  simp only [stackSize, hroom] at hlt
  have htop : stackBase Γ s + BitVec.ofNat 64 (8 * n) = s.getReg .rsp - 8 := by
    simp only [stackBase, hroom]; bv_omega
  exact {
    regs := fun r hr => by
      rw [hg, State.getReg_setReg_other s .rsp r _ hr]; exact h.regs r hr
    flags := by rw [State.store64_flags]; exact h.flags
    stackPerm := by rw [hb, hz, State.canWrite_congr hp]; exact h.stackPerm
    stackSize_lt := by rw [hz]; exact h.stackSize_lt
    stack := fun j τ' hj => by
      rw [hsp]
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        rw [State.load64_store64_same]
        exact hv
      | succ k =>
        simp only [List.getElem?_cons_succ] at hj
        have hk : k < Γ.stack.length := (List.getElem?_eq_some_iff.mp hj).1
        have hd : Disjoint (s.getReg .rsp - 8) 8
            (s.getReg .rsp - 8 + BitVec.ofNat 64 (8 * (k + 1))) 8 := by
          refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
        have e : s.getReg .rsp - 8 + BitVec.ofNat 64 (8 * (k + 1))
            = s.getReg .rsp + BitVec.ofNat 64 (8 * k) := by bv_omega
        rw [State.load64_store64_disjoint _ v hd, State.load64_congr hm, e]
        exact h.stack k τ' hj
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      have hjlt : j < l'.fields.length := (List.getElem?_eq_some_iff.mp hj).1
      have hd := (h.stackHeap b l' hl').mono (o := 8 * n) (p := 8 * j) (n' := 8) (m' := 8)
        h.stackSize_lt (hΨ.size_lt b l' hl') (by simp only [stackSize, hroom]; omega)
        (by simp only [Layout.size]; omega) (by omega) (by omega)
      rw [htop] at hd
      rw [State.load64_store64_disjoint _ v hd, State.load64_congr hm]
      exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl'
    text := fun b l' hl' ht => by
      have hout := h.text_outside_stack hΨ (lo := n) (cnt := 1) (by omega) (by omega) hl' ht
      have ea : stackBase Γ s + BitVec.ofNat 64 (8 * n) = s.getReg .rsp - 8 := by
        simp only [stackBase, hroom]; bv_omega
      rw [ea] at hout
      have e : ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v).mem
          (b + BitVec.ofNat 64 (l'.size - 1)) = s.mem (b + BitVec.ofNat 64 (l'.size - 1)) :=
        State.mem_store_of_disjoint (s.setReg .rsp (s.getReg .rsp - 8)) .w64 _ _ v hout
      rw [e]; exact h.text b l' hl' ht
    sp := by
      show HasTy fetch sys Ψ ix (Γ.regs .rsp) _
      rw [hint]
      exact HasTy.int _ }

/-- Popping: the top slot holds a value of its type, and the rest of the
state matches the context with that slot removed. -/
theorem pop₀ {τ : Ty} {σ : List Ty} (h : WellTyped fetch sys Ψ ix Γ s)
    (hint : Γ.regs .rsp = .int) (hst : Γ.stack = τ :: σ) :
    HasTy fetch sys Ψ ix τ (s.load64 (s.getReg .rsp)) ∧
    WellTyped fetch sys Ψ ix { Γ with stack := σ, room := Γ.room + 1 }
      (s.setReg .rsp (s.getReg .rsp + 8)) := by
  have hm : (s.setReg .rsp (s.getReg .rsp + 8)).mem = s.mem := rfl
  have hp : (s.setReg .rsp (s.getReg .rsp + 8)).perm = s.perm := rfl
  have hsp : (s.setReg .rsp (s.getReg .rsp + 8)).getReg .rsp = s.getReg .rsp + 8 :=
    State.getReg_setReg_same _ _ _
  have hz : stackSize { Γ with stack := σ, room := Γ.room + 1 } = stackSize Γ := by
    simp only [stackSize, hst, List.length_cons]; omega
  have hlt := h.stackSize_lt
  simp only [stackSize, hst, List.length_cons] at hlt
  have hb : stackBase { Γ with stack := σ, room := Γ.room + 1 }
      (s.setReg .rsp (s.getReg .rsp + 8)) = stackBase Γ s := by
    simp only [stackBase, hsp]; bv_omega
  constructor
  · have := h.stack 0 τ (by simp [hst])
    simpa using this
  · exact {
      regs := fun r hr => by
        rw [State.getReg_setReg_other s .rsp r _ hr]; exact h.regs r hr
      flags := h.flags
      stackPerm := by rw [hb, hz, State.canWrite_congr hp]; exact h.stackPerm
      stackSize_lt := by rw [hz]; exact h.stackSize_lt
      stack := fun j τ' hj => by
        have hj' : Γ.stack[j + 1]? = some τ' := by simpa [hst] using hj
        have hjlt : j < σ.length := (List.getElem?_eq_some_iff.mp hj).1
        have e : s.getReg .rsp + 8 + BitVec.ofNat 64 (8 * j)
            = s.getReg .rsp + BitVec.ofNat 64 (8 * (j + 1)) := by bv_omega
        rw [hsp, State.load64_congr hm, e]
        exact h.stack (j + 1) τ' hj'
      heapPerm := fun b l' hl' => by
        rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm b l' hl'
      heap := fun b l' hl' j τ' hj => by
        rw [State.load64_congr hm]; exact h.heap b l' hl' j τ' hj
      stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl'
      text := fun a l hl ht => by rw [hm]; exact h.text a l hl ht
      sp := by
        show HasTy fetch sys Ψ ix (Γ.regs .rsp) _
        rw [hint]
        exact HasTy.int _ }

/-- Reserving `k` stack slots: they become integer slots. -/
theorem allocFrame₀ {k m : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hint : Γ.regs .rsp = .int) (hroom : Γ.room = m + k) :
    WellTyped fetch sys Ψ ix { Γ with stack := List.replicate k .int ++ Γ.stack, room := m }
      (s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 (8 * k))) := by
  have hm : (s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 (8 * k))).mem = s.mem := rfl
  have hp : (s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 (8 * k))).perm = s.perm := rfl
  have hsp : (s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 (8 * k))).getReg .rsp
      = s.getReg .rsp - BitVec.ofNat 64 (8 * k) := State.getReg_setReg_same _ _ _
  have hz : stackSize { Γ with stack := List.replicate k .int ++ Γ.stack, room := m }
      = stackSize Γ := by
    simp only [stackSize, hroom, List.length_append, List.length_replicate]; omega
  have hlt := h.stackSize_lt
  simp only [stackSize, hroom] at hlt
  have hb : stackBase { Γ with stack := List.replicate k .int ++ Γ.stack, room := m }
      (s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 (8 * k))) = stackBase Γ s := by
    simp only [stackBase, hsp, hroom]; bv_omega
  exact {
    regs := fun r hr => by
      rw [State.getReg_setReg_other s .rsp r _ hr]; exact h.regs r hr
    flags := h.flags
    stackPerm := by rw [hb, hz, State.canWrite_congr hp]; exact h.stackPerm
    stackSize_lt := by rw [hz]; exact h.stackSize_lt
    stack := fun j τ hj => by
      rw [hsp, State.load64_congr hm]
      by_cases hjk : j < k
      · rw [List.getElem?_append_left (by simpa using hjk)] at hj
        have e : τ = .int := by
          simp only [List.getElem?_replicate, hjk, ite_true, Option.some.injEq] at hj
          exact hj.symm
        subst e
        exact HasTy.int _
      · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hjk)] at hj
        simp only [List.length_replicate] at hj
        have hjlt : j - k < Γ.stack.length := (List.getElem?_eq_some_iff.mp hj).1
        have e : s.getReg .rsp - BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (8 * j)
            = s.getReg .rsp + BitVec.ofNat 64 (8 * (j - k)) := by bv_omega
        rw [e]
        exact h.stack (j - k) τ hj
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      rw [State.load64_congr hm]; exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl'
    text := fun a l hl ht => by rw [hm]; exact h.text a l hl ht
    sp := by
      show HasTy fetch sys Ψ ix (Γ.regs .rsp) _
      rw [hint]
      exact HasTy.int _ }

/-- Releasing the top `k` stack slots. -/
theorem freeFrame₀ {k : Nat} {top rest : List Ty} (h : WellTyped fetch sys Ψ ix Γ s)
    (hint : Γ.regs .rsp = .int) (hst : Γ.stack = top ++ rest) (hk : top.length = k) :
    WellTyped fetch sys Ψ ix { Γ with stack := rest, room := Γ.room + k }
      (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 (8 * k))) := by
  have hm : (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 (8 * k))).mem = s.mem := rfl
  have hp : (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 (8 * k))).perm = s.perm := rfl
  have hsp : (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 (8 * k))).getReg .rsp
      = s.getReg .rsp + BitVec.ofNat 64 (8 * k) := State.getReg_setReg_same _ _ _
  have hz : stackSize { Γ with stack := rest, room := Γ.room + k } = stackSize Γ := by
    simp only [stackSize, hst, List.length_append, hk]; omega
  have hlt := h.stackSize_lt
  simp only [stackSize, hst, List.length_append, hk] at hlt
  have hb : stackBase { Γ with stack := rest, room := Γ.room + k }
      (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 (8 * k))) = stackBase Γ s := by
    simp only [stackBase, hsp]; bv_omega
  exact {
    regs := fun r hr => by
      rw [State.getReg_setReg_other s .rsp r _ hr]; exact h.regs r hr
    flags := h.flags
    stackPerm := by rw [hb, hz, State.canWrite_congr hp]; exact h.stackPerm
    stackSize_lt := by rw [hz]; exact h.stackSize_lt
    stack := fun j τ hj => by
      have hj' : Γ.stack[k + j]? = some τ := by
        rw [hst, List.getElem?_append_right (by omega)]
        simpa [hk] using hj
      have e : s.getReg .rsp + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (8 * j)
          = s.getReg .rsp + BitVec.ofNat 64 (8 * (k + j)) := by bv_omega
      rw [hsp, State.load64_congr hm, e]
      exact h.stack (k + j) τ hj'
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hp, State.canWrite_congr hp]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      rw [State.load64_congr hm]; exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl'
    text := fun a l hl ht => by rw [hm]; exact h.text a l hl ht
    sp := by
      show HasTy fetch sys Ψ ix (Γ.regs .rsp) _
      rw [hint]
      exact HasTy.int _ }

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
    (hv : HasTy fetch sys Ψ ix (Γ'.regs .rsp) (s.getReg .rsp)) : WellTyped fetch sys Ψ ix Γ' s :=
  { regs := fun r hr => by rw [hregs r hr]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by
      have := h.stackPerm
      simpa only [stackBase, stackSize, hstack, hroom] using this
    stackSize_lt := by
      have := h.stackSize_lt
      simpa only [stackSize, hstack, hroom] using this
    stack := fun i τ hi => h.stack i τ (by rw [← hstack]; exact hi)
    heapPerm := h.heapPerm
    heap := h.heap
    stackHeap := fun a l hl => by
      have := h.stackHeap a l hl
      simpa only [stackBase, stackSize, hstack, hroom] using this
    text := h.text
    sp := hv }

/-- What is known of the stack pointer's value may be forgotten. -/
theorem forgetSp (h : WellTyped fetch sys Ψ ix Γ s) :
    WellTyped fetch sys Ψ ix (Γ.setReg .rsp .int) s :=
  h.setSp (fun r hr => by simp only [CtxOf.setReg, hr, ↓reduceIte]) rfl rfl rfl (HasTy.int _)

/-- After the stack pointer has moved by `d`, it has its type moved by `d`. -/
theorem sp_moved (h : WellTyped fetch sys Ψ ix Γ s) {v d : BitVec 64}
    (hv : v = s.getReg .rsp + d) : HasTy fetch sys Ψ ix ((Γ.moveSp d).regs .rsp) v := by
  subst hv
  rw [CtxOf.moveSp_sp]
  exact h.sp.shift d

private theorem moved_regs {d : BitVec 64} {r : Reg} (hr : r ≠ .rsp) :
    (Γ.moveSp d).regs r = (Γ.setReg .rsp .int).regs r := by
  simp only [CtxOf.moveSp, CtxOf.setReg, hr, ↓reduceIte]

/-- After a push: the pushed value is on top, and the stack pointer is 8 lower. -/
theorem push {n : Nat} {τ : Ty} {v : BitVec 64} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hroom : Γ.room = n + 1) (hv : HasTy fetch sys Ψ ix τ v) :
    WellTyped fetch sys Ψ ix { Γ.moveSp (-8) with stack := τ :: Γ.stack, room := n }
      ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v) :=
  (h.forgetSp.push₀ hΨ (by simp [CtxOf.setReg]) hroom hv).setSp (fun _ hr => moved_regs hr) rfl
    rfl rfl (h.sp_moved (by
      rw [State.getReg, State.store64_regs]
      show (s.setReg .rsp (s.getReg .rsp - 8)).getReg .rsp = _
      rw [State.getReg_setReg_same, BitVec.sub_eq_add_neg]))

/-- After a pop: the popped value had the top slot's type, and the stack
pointer is 8 higher. -/
theorem pop {τ : Ty} {σ : List Ty} (h : WellTyped fetch sys Ψ ix Γ s) (hst : Γ.stack = τ :: σ) :
    HasTy fetch sys Ψ ix τ (s.load64 (s.getReg .rsp)) ∧
    WellTyped fetch sys Ψ ix { Γ.moveSp 8 with stack := σ, room := Γ.room + 1 }
      (s.setReg .rsp (s.getReg .rsp + 8)) := by
  obtain ⟨hτ, hw⟩ := h.forgetSp.pop₀ (by simp [CtxOf.setReg]) hst
  exact ⟨hτ, hw.setSp (fun _ hr => moved_regs hr) rfl rfl rfl
    (h.sp_moved (State.getReg_setReg_same _ _ _))⟩

theorem allocFrame {k m : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hroom : Γ.room = m + k) :
    WellTyped fetch sys Ψ ix
      { Γ.moveSp (-BitVec.ofNat 64 (8 * k)) with
        stack := List.replicate k .int ++ Γ.stack, room := m }
      (s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 (8 * k))) :=
  (h.forgetSp.allocFrame₀ (by simp [CtxOf.setReg]) hroom).setSp (fun _ hr => moved_regs hr) rfl
    rfl rfl (h.sp_moved (by rw [State.getReg_setReg_same, BitVec.sub_eq_add_neg]))

theorem freeFrame {k : Nat} {top rest : List Ty} (h : WellTyped fetch sys Ψ ix Γ s)
    (hst : Γ.stack = top ++ rest) (hk : top.length = k) :
    WellTyped fetch sys Ψ ix
      { Γ.moveSp (BitVec.ofNat 64 (8 * k)) with stack := rest, room := Γ.room + k }
      (s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 (8 * k))) :=
  (h.forgetSp.freeFrame₀ (by simp [CtxOf.setReg]) hst hk).setSp (fun _ hr => moved_regs hr) rfl
    rfl rfl (h.sp_moved (State.getReg_setReg_same _ _ _))

/-- Any `m` bytes inside field `i` of a writable block are writable. -/
theorem canWrite_inner {a : BitVec 64} {l : Layout} {i k m : Nat}
    (h : WellTyped fetch sys Ψ ix Γ s) (hl : Ψ a = some l) (hw : l.writable = true)
    (hi : i < l.fields.length) (hk : k + m ≤ 8) :
    s.canWrite (a + BitVec.ofNat 64 (8 * i + k)) m = true :=
  State.canWrite_sub ((h.heapPerm a l hl).2 hw) (by simp only [Layout.size]; omega)

/-- Any change to memory confined to one integer field keeps the state well
typed: an integer field may hold anything. -/
theorem writeInt {a : BitVec 64} {l : Layout} {i : Nat} {s' : State}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hl : Ψ a = some l)
    (hi : l.fields[i]? = some .int) (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags)
    (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 (8 * i)) 8 y 8 → s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 (8 * 1) ≤ x - (a + BitVec.ofNat 64 (8 * i)) → s'.mem x = s.mem x) :
    WellTyped fetch sys Ψ ix Γ s' := by
  have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
  have hsz := hΨ.size_lt a l hl
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hb : stackBase Γ s' = stackBase Γ s := by simp only [stackBase, hg]
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by rw [hb, State.canWrite_congr hperm]; exact h.stackPerm
    stackSize_lt := h.stackSize_lt
    stack := fun j τ' hj => by
      have hjlt : j < Γ.stack.length := (List.getElem?_eq_some_iff.mp hj).1
      have hd := (h.stackHeap a l hl).symm.mono (o := 8 * i) (p := 8 * Γ.room + 8 * j)
        (n' := 8) (m' := 8) hsz h.stackSize_lt (by simp only [Layout.size]; omega)
        (by simp only [stackSize]; omega) (by omega) (by omega)
      rw [slot_addr] at hd
      rw [hg, hframe _ hd]
      exact h.stack j τ' hj
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      have hjlt : j < l'.fields.length := (List.getElem?_eq_some_iff.mp hj).1
      by_cases hab : b = a
      · subst hab
        have e : l' = l := Option.some.inj (hl'.symm.trans hl)
        subst e
        by_cases hij : j = i
        · subst hij
          have e : τ' = .int := Option.some.inj (hj.symm.trans hi)
          subst e
          exact HasTy.int _
        · rw [hframe _ (disjoint_slots (N := l'.size) (Ne.symm hij)
            (by simp only [Layout.size]; omega) (by simp only [Layout.size]; omega) hsz)]
          exact h.heap b l' hl' j τ' hj
      · have hd := (hΨ.disjoint a b l l' hl hl' (Ne.symm hab)).mono (o := 8 * i) (p := 8 * j)
          (n' := 8) (m' := 8) hsz (hΨ.size_lt b l' hl') (by simp only [Layout.size]; omega)
          (by simp only [Layout.size]; omega) (by omega) (by omega)
        rw [hframe _ hd]
        exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb]; exact h.stackHeap b l' hl'
    text := fun b l' hl' ht => by
      rw [hmem _ (hΨ.text_outside_fields hl (lo := i) (cnt := 1) (by omega) (by omega) hl' ht)]
      exact h.text b l' hl' ht
    sp := by rw [hg]; exact h.sp }

/-- Any change to memory confined to a run of integer fields keeps the state
well typed. -/
theorem writeInts {a : BitVec 64} {l : Layout} {lo cnt : Nat} {s' : State}
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hl : Ψ a = some l) (hc : 0 < cnt)
    (hle : lo + cnt ≤ l.fields.length)
    (hi : ∀ j, lo ≤ j → j < lo + cnt → l.fields[j]? = some .int) (hregs : s'.regs = s.regs)
    (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 (8 * lo)) (8 * cnt) y 8 →
      s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 (8 * cnt) ≤ x - (a + BitVec.ofNat 64 (8 * lo)) →
      s'.mem x = s.mem x) :
    WellTyped fetch sys Ψ ix Γ s' := by
  have hsz := hΨ.size_lt a l hl
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hb : stackBase Γ s' = stackBase Γ s := by simp only [stackBase, hg]
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by rw [hb, State.canWrite_congr hperm]; exact h.stackPerm
    stackSize_lt := h.stackSize_lt
    stack := fun j τ' hj => by
      have hjlt : j < Γ.stack.length := (List.getElem?_eq_some_iff.mp hj).1
      have hd := (h.stackHeap a l hl).symm.mono (o := 8 * lo) (p := 8 * Γ.room + 8 * j)
        (n' := 8 * cnt) (m' := 8) hsz h.stackSize_lt (by simp only [Layout.size]; omega)
        (by simp only [stackSize]; omega) (by omega) (by omega)
      rw [slot_addr] at hd
      rw [hg, hframe _ hd]
      exact h.stack j τ' hj
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      have hjlt : j < l'.fields.length := (List.getElem?_eq_some_iff.mp hj).1
      by_cases hab : b = a
      · subst hab
        have e : l' = l := Option.some.inj (hl'.symm.trans hl)
        subst e
        by_cases hin : lo ≤ j ∧ j < lo + cnt
        · have e : τ' = .int := Option.some.inj (hj.symm.trans (hi j hin.1 hin.2))
          subst e
          exact HasTy.int _
        · rw [hframe _ (disjoint_range_slot (N := l'.size) hc (by omega)
            (by simp only [Layout.size]; omega) (by simp only [Layout.size]; omega) hsz)]
          exact h.heap b l' hl' j τ' hj
      · have hd := (hΨ.disjoint a b l l' hl hl' (Ne.symm hab)).mono (o := 8 * lo) (p := 8 * j)
          (n' := 8 * cnt) (m' := 8) hsz (hΨ.size_lt b l' hl') (by simp only [Layout.size]; omega)
          (by simp only [Layout.size]; omega) (by omega) (by omega)
        rw [hframe _ hd]
        exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb]; exact h.stackHeap b l' hl'
    text := fun b l' hl' ht => by
      rw [hmem _ (hΨ.text_outside_fields hl hle hc hl' ht)]
      exact h.text b l' hl' ht
    sp := by rw [hg]; exact h.sp }

/-- Any `m` bytes inside field `i` of a block are readable. -/
theorem canRead_inner {a : BitVec 64} {l : Layout} {i k m : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hl : Ψ a = some l) (hi : i < l.fields.length) (hk : k + m ≤ 8) :
    s.canRead (a + BitVec.ofNat 64 (8 * i + k)) m = true :=
  State.canRead_sub (h.heapPerm a l hl).1 (by simp only [Layout.size]; omega)

/-- A register may be given any type its current value has. -/
theorem retype {r : Reg} {τ : Ty} (h : WellTyped fetch sys Ψ ix Γ s) (hr : r ≠ .rsp)
    (hv : HasTy fetch sys Ψ ix τ (s.getReg r)) : WellTyped fetch sys Ψ ix (Γ.setReg r τ) s := by
  refine (h.setReg hr hv).congr ?_ rfl rfl rfl
  funext r'
  simp only [State.regs_setReg, State.getReg]
  split
  · next h' => rw [h']
  · rfl

/-- Any `m` bytes inside stack slot `i` are writable. -/
theorem canWrite_slot_inner {i k m : Nat} (h : WellTyped fetch sys Ψ ix Γ s)
    (hi : i < Γ.stack.length) (hk : k + m ≤ 8) :
    s.canWrite (s.getReg .rsp + BitVec.ofNat 64 (8 * i + k)) m = true := by
  have := State.canWrite_sub h.stackPerm (o := 8 * Γ.room + (8 * i + k)) (m := m)
    (by simp only [stackSize]; omega)
  have e : stackBase Γ s + BitVec.ofNat 64 (8 * Γ.room + (8 * i + k))
      = s.getReg .rsp + BitVec.ofNat 64 (8 * i + k) := by
    simp only [stackBase]; bv_omega
  rwa [e] at this

/-- Any change to memory confined to one stack slot keeps the state well
typed, with that slot now an integer. -/
theorem writeSlotInt {i : Nat} {s' : State} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hi : i < Γ.stack.length) (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags)
    (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) 8 y 8 →
      s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 (8 * 1) ≤ x - (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) →
      s'.mem x = s.mem x) :
    WellTyped fetch sys Ψ ix { Γ with stack := Γ.stack.set i .int } s' := by
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hz : stackSize { Γ with stack := Γ.stack.set i .int } = stackSize Γ := by
    simp only [stackSize, List.length_set]
  have hb : stackBase { Γ with stack := Γ.stack.set i .int } s' = stackBase Γ s := by
    simp only [stackBase, hg]
  have hlt := h.stackSize_lt
  simp only [stackSize] at hlt
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by rw [hb, hz, State.canWrite_congr hperm]; exact h.stackPerm
    stackSize_lt := by rw [hz]; exact h.stackSize_lt
    stack := fun j τ' hj => by
      rw [hg]
      by_cases hji : j = i
      · subst hji
        rw [List.getElem?_set_self hi] at hj
        cases hj
        exact HasTy.int _
      · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
        have hjlt : j < Γ.stack.length := (List.getElem?_eq_some_iff.mp hj).1
        rw [hframe _ (disjoint_slots (N := 8 * Γ.stack.length) (Ne.symm hji) (by omega) (by omega)
          (by omega))]
        exact h.stack j τ' hj
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      have hjlt : j < l'.fields.length := (List.getElem?_eq_some_iff.mp hj).1
      have hd := (h.stackHeap b l' hl').mono (o := 8 * Γ.room + 8 * i) (p := 8 * j)
        (n' := 8) (m' := 8) h.stackSize_lt (hΨ.size_lt b l' hl') (by simp only [stackSize]; omega)
        (by simp only [Layout.size]; omega) (by omega) (by omega)
      rw [slot_addr] at hd
      rw [hframe _ hd]
      exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl'
    text := fun b l' hl' ht => by
      have hout := h.text_outside_stack hΨ (lo := Γ.room + i) (cnt := 1)
        (by omega) (by omega) hl' ht
      rw [show 8 * (Γ.room + i) = 8 * Γ.room + 8 * i by omega, slot_addr] at hout
      rw [hmem _ hout]
      exact h.text b l' hl' ht
    sp := by rw [hg]; exact h.sp }

/-- Any change to memory confined to a run of integer stack slots keeps the
state well typed. -/
theorem writeSlotsInt {lo cnt : Nat} {s' : State} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hc : 0 < cnt) (hle : lo + cnt ≤ Γ.stack.length)
    (hi : ∀ j, lo ≤ j → j < lo + cnt → Γ.stack[j]? = some .int) (hregs : s'.regs = s.regs)
    (hflags : s'.flags = s.flags) (hperm : s'.perm = s.perm)
    (hframe : ∀ y, Disjoint (s.getReg .rsp + BitVec.ofNat 64 (8 * lo)) (8 * cnt) y 8 →
      s'.load64 y = s.load64 y)
    (hmem : ∀ x, BitVec.ofNat 64 (8 * cnt) ≤ x - (s.getReg .rsp + BitVec.ofNat 64 (8 * lo)) →
      s'.mem x = s.mem x) :
    WellTyped fetch sys Ψ ix Γ s' := by
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hb : stackBase Γ s' = stackBase Γ s := by simp only [stackBase, hg]
  have hlt := h.stackSize_lt
  simp only [stackSize] at hlt
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := by rw [hflags]; exact h.flags
    stackPerm := by rw [hb, State.canWrite_congr hperm]; exact h.stackPerm
    stackSize_lt := h.stackSize_lt
    stack := fun j τ' hj => by
      rw [hg]
      have hjlt : j < Γ.stack.length := (List.getElem?_eq_some_iff.mp hj).1
      by_cases hin : lo ≤ j ∧ j < lo + cnt
      · have e : τ' = .int := Option.some.inj (hj.symm.trans (hi j hin.1 hin.2))
        subst e
        exact HasTy.int _
      · rw [hframe _ (disjoint_range_slot (N := 8 * Γ.stack.length) hc (by omega) (by omega)
          (by omega) (by omega))]
        exact h.stack j τ' hj
    heapPerm := fun b l' hl' => by
      rw [State.canRead_congr hperm, State.canWrite_congr hperm]; exact h.heapPerm b l' hl'
    heap := fun b l' hl' j τ' hj => by
      have hjlt : j < l'.fields.length := (List.getElem?_eq_some_iff.mp hj).1
      have hd := (h.stackHeap b l' hl').mono (o := 8 * Γ.room + 8 * lo) (p := 8 * j)
        (n' := 8 * cnt) (m' := 8) h.stackSize_lt (hΨ.size_lt b l' hl')
        (by simp only [stackSize]; omega) (by simp only [Layout.size]; omega) (by omega) (by omega)
      rw [slot_addr] at hd
      rw [hframe _ hd]
      exact h.heap b l' hl' j τ' hj
    stackHeap := fun b l' hl' => by rw [hb]; exact h.stackHeap b l' hl'
    text := fun b l' hl' ht => by
      have hout := h.text_outside_stack hΨ (lo := Γ.room + lo) (cnt := cnt)
        (by omega) hc hl' ht
      rw [show 8 * (Γ.room + lo) = 8 * Γ.room + 8 * lo by omega, slot_addr] at hout
      rw [hmem _ hout]
      exact h.text b l' hl' ht
    sp := by rw [hg]; exact h.sp }

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

/-- A small non-negative displacement sign-extends to itself. -/
theorem sext_slot {i : Nat} (h : 8 * i < 2 ^ 31) :
    (BitVec.ofNat 32 (8 * i)).signExtend 64 = BitVec.ofNat 64 (8 * i) := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_ofNat]
    omega

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

/-- The address of byte `k` of slot `i` from a base register. -/
theorem ea_inner (s : State) (b : Reg) {i k : Nat} {disp : BitVec 32} (h : innerDisp i k disp) :
    s.ea (.sib (some b) none disp) = s.getReg b + BitVec.ofNat 64 (8 * i + k) := by
  obtain ⟨rfl, hlt⟩ := h
  simp [ea, sext_small hlt]

theorem read_w32 {s : State} {a : BitVec 64} (h : s.canRead a 4 = true) :
    s.read .w32 a = .next (s.load32 a) := by
  have h' : s.canRead a Width.w32.bytes.toNat = true := h
  simp only [read, h', ite_true]
  rfl

/-- The address of slot `i` from a base register. -/
theorem ea_slot (s : State) (b : Reg) {i : Nat} {disp : BitVec 32} (h : slotDisp i disp) :
    s.ea (.sib (some b) none disp) = s.getReg b + BitVec.ofNat 64 (8 * i) := by
  obtain ⟨rfl, hlt⟩ := h
  simp [ea, sext_slot hlt]

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
  simp only [addCarry]
  bv_decide

theorem subBorrow_fst (a b : BitVec 64) : (subBorrow a b false).1 = a - b := by
  simp only [subBorrow]
  bv_decide

/-- The zero flag after a subtraction says whether the result is zero. -/
theorem subBorrow_zf {n : Nat} (a b : BitVec n) (c : Bool) :
    (subBorrow a b c).2.zf = some ((subBorrow a b c).1 == 0) := rfl

/-- A store confined to one 8-byte slot leaves every disjoint 64-bit load unchanged. -/
theorem State.load64_store_inner (s : State) (w : Width) {base y : BitVec 64} {k : Nat}
    (v : BitVec w.bits) (hk : k + w.bytes.toNat ≤ 8) (hd : Disjoint base 8 y 8) :
    (s.store w (base + BitVec.ofNat 64 k) v).load64 y = s.load64 y := by
  have hd := hd.of_pos (by decide) (by decide)
  cases w
  · have hk' : k + 4 ≤ 8 := hk
    exact State.load_store_disjoint s .w32 .w64 _ _ v
      (by simp only [Width.bytes]; bv_omega) (by simp only [Width.bytes]; bv_omega)
  · have hk' : k + 8 ≤ 8 := hk
    exact State.load_store_disjoint s .w64 .w64 _ _ v
      (by simp only [Width.bytes]; bv_omega) (by simp only [Width.bytes]; bv_omega)

/-- A byte store inside one 8-byte slot leaves every disjoint 64-bit load unchanged. -/
theorem State.load64_store8_inner (s : State) {base y : BitVec 64} {k : Nat} (v : BitVec 8)
    (hk : k + 1 ≤ 8) (hd : Disjoint base 8 y 8) :
    (s.store8 (base + BitVec.ofNat 64 k) v).load64 y = s.load64 y := by
  have hd := hd.of_pos (by decide) (by decide)
  exact State.load64_store8_disjoint s v (by bv_omega)

/-- A 16-bit store inside one 8-byte slot leaves every other slot unchanged. -/
theorem State.load64_store16_inner (s : State) {base y : BitVec 64} {k : Nat} (v : BitVec 16)
    (hk : k + 2 ≤ 8) (hd : Disjoint base 8 y 8) :
    (s.store16 (base + BitVec.ofNat 64 k) v).load64 y = s.load64 y := by
  have e : base + BitVec.ofNat 64 k + 1 = base + BitVec.ofNat 64 (k + 1) := by bv_omega
  rw [State.store16, e, State.load64_store8_inner _ _ (by omega) hd,
    State.load64_store8_inner _ _ (by omega) hd]

/-- A store confined to one 8-byte slot leaves every byte outside the slot unchanged. -/
theorem State.mem_store_inner (s : State) (w : Width) {base x : BitVec 64} {k : Nat}
    (v : BitVec w.bits) (hk : k + w.bytes.toNat ≤ 8) (hx : BitVec.ofNat 64 (8 * 1) ≤ x - base) :
    (s.store w (base + BitVec.ofNat 64 k) v).mem x = s.mem x := by
  refine State.mem_store_of_disjoint s w _ x v ?_
  cases w <;> simp only [Width.bytes] at * <;> bv_omega

theorem State.mem_store8_inner (s : State) {base x : BitVec 64} {k : Nat} (v : BitVec 8)
    (hk : k + 1 ≤ 8) (hx : BitVec.ofNat 64 (8 * 1) ≤ x - base) :
    (s.store8 (base + BitVec.ofNat 64 k) v).mem x = s.mem x := by
  rw [State.mem_store8]
  split
  · next he => subst he; exact absurd hx (by bv_omega)
  · rfl

theorem State.mem_store16_inner (s : State) {base x : BitVec 64} {k : Nat} (v : BitVec 16)
    (hk : k + 2 ≤ 8) (hx : BitVec.ofNat 64 (8 * 1) ≤ x - base) :
    (s.store16 (base + BitVec.ofNat 64 k) v).mem x = s.mem x := by
  have e : base + BitVec.ofNat 64 k + 1 = base + BitVec.ofNat 64 (k + 1) := by bv_omega
  rw [State.store16, e, State.mem_store8_inner _ _ (by omega) hx,
    State.mem_store8_inner _ _ (by omega) hx]

/-- Byte `k` of slot `i`, as an offset from the start of the slot. -/
theorem inner_split (a : BitVec 64) (i k : Nat) :
    a + BitVec.ofNat 64 (8 * i + k) = a + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem AluOp.apply_defined {n : Nat} (op : AluOp) (a b : BitVec n) :
    (op.apply a b).2.defined = true := by
  cases op <;> exact Flags.ofResult_defined _ _ _

/-- Stepping to byte `k` of the slot `i` slots on from slot `off`. -/
theorem slot_add_inner (a : BitVec 64) (off i k : Nat) :
    a + BitVec.ofNat 64 (8 * off) + BitVec.ofNat 64 (8 * i + k)
      = a + BitVec.ofNat 64 (8 * (off + i) + k) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.add_assoc]

/-- Stepping `i` slots on from slot `off`. -/
theorem slot_add (a : BitVec 64) (off i : Nat) :
    a + BitVec.ofNat 64 (8 * off) + BitVec.ofNat 64 (8 * i) = a + BitVec.ofNat 64 (8 * (off + i)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

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

/-- A readable memory operand's bytes are readable. -/
theorem ReadOk.canRead {n : Nat} {m : Mem} (hr : ReadOk Ψ next Γ n (.mem m))
    (h : WellTyped fetch sys Ψ ix Γ s) (hrip : s.rip = next) : s.canRead (s.ea m) n = true := by
  cases hr with
  | @global base l i k disp τ hl haddr hi hk =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i + k) := by
      simp only [State.ea, hrip, haddr]
    rw [hea]
    exact h.canRead_inner hl hilt hk
  | @indexed b x sc fields writable off i k disp c τ hb hΓ hΓx hD hi hk =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    rw [State.ea_indexed s hx hD, hva, slot_add_inner]
    exact h.canRead_inner hl hilt hk
  | @field b fields writable off i k disp τ hb hΓ hdisp hi hk =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [State.ea_inner s b hdisp, hva, slot_add_inner]
    exact h.canRead_inner hl hilt hk
  | @slot i k disp τ hdisp hi hk =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [State.ea_inner s .rsp hdisp]
    exact State.canRead_of_canWrite (h.canWrite_slot_inner hilt hk)

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
  | @indexed b x sc fields off i k disp c hb hΓ hΓx hD hi hk =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp)
        = a + BitVec.ofNat 64 (8 * (off + i) + k) := by
      rw [State.ea_indexed s hx hD, hva, slot_add_inner]
    have hc := h.canWrite_inner (m := w.bytes.toNat) hl (hwr rfl) hilt hk
    refine ⟨s.store w (a + BitVec.ofNat 64 (8 * (off + i) + k)) v, ?_, State.rip_store _ _ _ _,
      h.writeInt hΨ hl hi (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _) (fun y hd => by
          rw [inner_split]; exact State.load64_store_inner s w _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store_inner s w _ hk hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @global base l i k disp hl hwr haddr hi hk =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i + k) := by
      simp only [State.ea, hrip, haddr]
    have hc := h.canWrite_inner (m := w.bytes.toNat) hl hwr hilt hk
    refine ⟨s.store w (base + BitVec.ofNat 64 (8 * i + k)) v, ?_, State.rip_store _ _ _ _,
      h.writeInt hΨ hl hi (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _) (fun y hd => by
          rw [inner_split]; exact State.load64_store_inner s w _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store_inner s w _ hk hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @reg d hd => exact ⟨s.writeReg w d v, rfl, rfl, h.setReg hd (HasTy.int _)⟩
  | @field b fields off i k disp hb hΓ hdisp hi hk =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (8 * (off + i) + k) := by
      rw [State.ea_inner s b hdisp, hva, slot_add_inner]
    have hc := h.canWrite_inner (m := w.bytes.toNat) hl (hwr rfl) hilt hk
    refine ⟨s.store w (a + BitVec.ofNat 64 (8 * (off + i) + k)) v, ?_, State.rip_store _ _ _ _,
      h.writeInt hΨ hl hi (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _) (fun y hd => by
          rw [inner_split]; exact State.load64_store_inner s w _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store_inner s w _ hk hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @slot i k disp τ hdisp hi hk =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea := State.ea_inner s .rsp hdisp
    have hc := h.canWrite_slot_inner (m := w.bytes.toNat) hilt hk
    refine ⟨s.store w (s.getReg .rsp + BitVec.ofNat 64 (8 * i + k)) v, ?_, State.rip_store _ _ _ _,
      h.writeSlotInt hΨ hilt (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _) (fun y hd => by
          rw [inner_split]; exact State.load64_store_inner s w _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store_inner s w _ hk hx)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]

/-- Writing any byte to a writable operand succeeds likewise. -/
theorem WriteIntOk.writeRM8 {rm : RM} {Γ' : Ctx} (hw : WriteIntOk Ψ next Γ 1 rm Γ')
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hrip : s.rip = next) (v : BitVec 8) :
    ∃ s', s.writeRM8 rm v = .next s' ∧ s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases hw with
  | @indexed b x sc fields off i k disp c hb hΓ hΓx hD hi hk =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp)
        = a + BitVec.ofNat 64 (8 * (off + i) + k) := by
      rw [State.ea_indexed s hx hD, hva, slot_add_inner]
    have hc := h.canWrite_inner (m := 1) hl (hwr rfl) hilt hk
    refine ⟨s.store8 (a + BitVec.ofNat 64 (8 * (off + i) + k)) v, ?_, rfl,
      h.writeInt hΨ hl hi rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store8_inner s _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store8_inner s _ hk hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @global base l i k disp hl hwr haddr hi hk =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i + k) := by
      simp only [State.ea, hrip, haddr]
    have hc := h.canWrite_inner (m := 1) hl hwr hilt hk
    refine ⟨s.store8 (base + BitVec.ofNat 64 (8 * i + k)) v, ?_, rfl,
      h.writeInt hΨ hl hi rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store8_inner s _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store8_inner s _ hk hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @reg d hd => exact ⟨_, rfl, rfl, h.setReg hd (HasTy.int _)⟩
  | @field b fields off i k disp hb hΓ hdisp hi hk =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (8 * (off + i) + k) := by
      rw [State.ea_inner s b hdisp, hva, slot_add_inner]
    have hc := h.canWrite_inner (m := 1) hl (hwr rfl) hilt hk
    refine ⟨s.store8 (a + BitVec.ofNat 64 (8 * (off + i) + k)) v, ?_, rfl,
      h.writeInt hΨ hl hi rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store8_inner s _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store8_inner s _ hk hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @slot i k disp τ hdisp hi hk =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea := State.ea_inner s .rsp hdisp
    have hc := h.canWrite_slot_inner (m := 1) hilt hk
    refine ⟨s.store8 (s.getReg .rsp + BitVec.ofNat 64 (8 * i + k)) v, ?_, rfl,
      h.writeSlotInt hΨ hilt rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store8_inner s _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store8_inner s _ hk hx)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]

/-- Writing any 16-bit value to a writable memory operand succeeds likewise. -/
theorem WriteIntOk.write16 {m : Mem} {Γ' : Ctx} (hw : WriteIntOk Ψ next Γ 2 (.mem m) Γ')
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hrip : s.rip = next) (v : BitVec 16) :
    ∃ s', s.write16 (s.ea m) v = .next s' ∧ s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases hw with
  | @indexed b x sc fields off i k disp c hb hΓ hΓx hD hi hk =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp)
        = a + BitVec.ofNat 64 (8 * (off + i) + k) := by
      rw [State.ea_indexed s hx hD, hva, slot_add_inner]
    have hc := h.canWrite_inner (m := 2) hl (hwr rfl) hilt hk
    refine ⟨s.store16 (a + BitVec.ofNat 64 (8 * (off + i) + k)) v, ?_, rfl,
      h.writeInt hΨ hl hi rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store16_inner s _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store16_inner s _ hk hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @global base l i k disp hl hwr haddr hi hk =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i + k) := by
      simp only [State.ea, hrip, haddr]
    have hc := h.canWrite_inner (m := 2) hl hwr hilt hk
    refine ⟨s.store16 (base + BitVec.ofNat 64 (8 * i + k)) v, ?_, rfl,
      h.writeInt hΨ hl hi rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store16_inner s _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store16_inner s _ hk hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @field b fields off i k disp hb hΓ hdisp hi hk =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (8 * (off + i) + k) := by
      rw [State.ea_inner s b hdisp, hva, slot_add_inner]
    have hc := h.canWrite_inner (m := 2) hl (hwr rfl) hilt hk
    refine ⟨s.store16 (a + BitVec.ofNat 64 (8 * (off + i) + k)) v, ?_, rfl,
      h.writeInt hΨ hl hi rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store16_inner s _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store16_inner s _ hk hx)⟩
    simp only [hea, State.write16, hc, ite_true]
  | @slot i k disp τ hdisp hi hk =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea := State.ea_inner s .rsp hdisp
    have hc := h.canWrite_slot_inner (m := 2) hilt hk
    refine ⟨s.store16 (s.getReg .rsp + BitVec.ofNat 64 (8 * i + k)) v, ?_, rfl,
      h.writeSlotInt hΨ hilt rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store16_inner s _ hk hd)
        (fun x hx => by rw [inner_split]; exact State.mem_store16_inner s _ hk hx)⟩
    simp only [hea, State.write16, hc, ite_true]

/-- An operand holding a code pointer can be read, and what is read is a code pointer. -/
theorem Holds.sound {rm : RM} {τ : Ty} (hc : Holds Ψ next Γ rm τ)
    (h : WellTyped fetch sys Ψ ix Γ s) (hrip : s.rip = next) :
    ∃ v, s.readRM .w64 rm = .next v ∧ HasTy fetch sys Ψ ix τ v := by
  cases hc with
  | @indexed b x sc fields writable off i disp c Δ hb hΓ hΓx hD hi =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (8 * (off + i)) := by
      rw [State.ea_indexed s hx hD, hva, slot_add]
    refine ⟨s.load64 (a + BitVec.ofNat 64 (8 * (off + i))), ?_, h.heap _ l hl (off + i) _ hi⟩
    simp [State.readRM, hea, State.read_w64 (h.canRead_field hl hilt)]
  | @global base l i disp Δ hl haddr hi =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i) := by
      simp only [State.ea, hrip, haddr]
    refine ⟨s.load64 (base + BitVec.ofNat 64 (8 * i)), ?_, h.heap _ l hl i _ hi⟩
    simp [State.readRM, hea, State.read_w64 (h.canRead_field hl hilt)]
  | @reg r Δ hr hΓ =>
    refine ⟨s.getReg r, ?_, by have := h.regs r hr; rwa [hΓ] at this⟩
    simp [State.readRM, State.readReg_w64]
  | @field b fields writable off i disp Δ hb hΓ hdisp hi =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (8 * (off + i)) := by
      rw [State.ea_slot s b hdisp, hva, slot_add]
    refine ⟨s.load64 (a + BitVec.ofNat 64 (8 * (off + i))), ?_, h.heap _ l hl (off + i) _ hi⟩
    simp [State.readRM, hea, State.read_w64 (h.canRead_field hl hilt)]
  | @slot i disp Δ hdisp hi =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)), ?_, h.stack i _ hi⟩
    simp [State.readRM, State.ea_slot s .rsp hdisp,
      State.read_w64 (State.canRead_of_canWrite (h.canWrite_slot hilt))]

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
  | @loadField d b fields writable off i disp τ hd hb hΓ hdisp hi =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (8 * (off + i)) := by
      rw [State.ea_slot s b hdisp, hva, slot_add]
    refine ⟨s.setReg d (s.load64 (a + BitVec.ofNat 64 (8 * (off + i)))), ?_, rfl,
      h.setReg hd (h.heap _ l hl (off + i) τ hi)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.read_w64 (h.canRead_field hl hilt), State.writeReg]
  | @storeField b src fields off i disp τ hb hs hΓ hdisp hi hsub =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hw, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.sib (some b) none disp) = a + BitVec.ofNat 64 (8 * (off + i)) := by
      rw [State.ea_slot s b hdisp, hva, slot_add]
    refine ⟨s.store64 (a + BitVec.ofNat 64 (8 * (off + i))) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeField hΨ hl hi ((h.regs src hs).sub hsub)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.readReg_w64, State.write_w64 _ (h.canWrite_field hl (hw rfl) hilt)]
  | @loadIndexed d b x sc fields writable off i disp c τ hd hb hΓ hΓx hD hi =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (8 * (off + i)) := by
      rw [State.ea_indexed s hx hD, hva, slot_add]
    refine ⟨s.setReg d (s.load64 (a + BitVec.ofNat 64 (8 * (off + i)))), ?_, rfl,
      h.setReg hd (h.heap _ l hl (off + i) τ hi)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.read_w64 (h.canRead_field hl hilt), State.writeReg]
  | @storeIndexed b src x sc fields off i disp c τ hb hs hΓ hΓx hD hi hsub =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
    have hilt : off + i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some b) (some (x, sc)) disp) = a + BitVec.ofNat 64 (8 * (off + i)) := by
      rw [State.ea_indexed s hx hD, hva, slot_add]
    refine ⟨s.store64 (a + BitVec.ofNat 64 (8 * (off + i))) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeField hΨ hl hi ((h.regs src hs).sub hsub)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.readReg_w64, State.write_w64 _ (h.canWrite_field hl (hwr rfl) hilt)]
  | @loadGlobal d base l i disp τ hd hl haddr hi =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i) := by
      simp only [State.ea, hrip, haddr]
    refine ⟨s.setReg d (s.load64 (base + BitVec.ofNat 64 (8 * i))), ?_, rfl,
      h.setReg hd (h.heap _ l hl i τ hi)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.read_w64 (h.canRead_field hl hilt), State.writeReg]
  | @storeGlobal src base l i disp τ hs hl hwr haddr hi hsub =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i) := by
      simp only [State.ea, hrip, haddr]
    refine ⟨s.store64 (base + BitVec.ofNat 64 (8 * i)) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeField hΨ hl hi ((h.regs src hs).sub hsub)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.readReg_w64, State.write_w64 _ (h.canWrite_field hl hwr hilt)]
  | @loadStack d i disp τ hd hdisp hi =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨s.setReg d (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i))), ?_, rfl,
      h.setReg hd (h.stack i τ hi)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.ea_slot s .rsp hdisp,
      State.read_w64 (State.canRead_of_canWrite (h.canWrite_slot hilt)), State.writeReg]
  | @loadStackIndexed d x sc i disp c τ hd hΓx hD hi =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    have hx := h.eqReg x.toReg_ne_rsp hΓx
    have hea : s.ea (.sib (some .rsp) (some (x, sc)) disp)
        = s.getReg .rsp + BitVec.ofNat 64 (8 * i) := State.ea_indexed s hx hD
    refine ⟨s.setReg d (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i))), ?_, rfl,
      h.setReg hd (h.stack i τ hi)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, hea,
      State.read_w64 (State.canRead_of_canWrite (h.canWrite_slot hilt)), State.writeReg]
  | @storeStack src i disp τ hs hdisp hslot =>
    have hi : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hslot).1
    refine ⟨s.store64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeStack hΨ hi (h.regs src hs)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.ea_slot s .rsp hdisp,
      State.readReg_w64, State.write_w64 _ (h.canWrite_slot hi)]
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
    have hc : s.canRead (s.getReg .rsp) 8 = true := by
      have := State.canRead_of_canWrite (h.canWrite_slot (i := 0) (by simp [hst]))
      simpa using this
    refine ⟨(s.setReg .rsp (s.getReg .rsp + 8)).setReg r (s.load64 (s.getReg .rsp)), ?_, rfl,
      hw.setReg hr hv⟩
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
    refine ⟨{ s.setReg .rsp (s.getReg .rsp - BitVec.ofNat 64 (8 * k)) with
        flags := (subBorrow (s.getReg .rsp) (BitVec.ofNat 64 (8 * k)) false).2 }, ?_, rfl,
      (h.allocFrame hroom).setFlags (P := Flags.Known) (Flags.ofResult_defined _ _ _)⟩
    simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, AluOp.eval,
      AluOp.writesDst, Result.ofOption, State.writeReg, State.readReg_w64, sext_slot hlt,
      subBorrow_fst]
  | @freeFrame k imm top rest hk hst hlen =>
    obtain ⟨rfl, hlt⟩ := hk
    refine ⟨{ s.setReg .rsp (s.getReg .rsp + BitVec.ofNat 64 (8 * k)) with
        flags := (addCarry (s.getReg .rsp) (BitVec.ofNat 64 (8 * k)) false).2 }, ?_, rfl,
      (h.freeFrame hst hlen).setFlags (P := Flags.Known) (Flags.ofResult_defined _ _ _)⟩
    simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, AluOp.eval,
      AluOp.writesDst, Result.ofOption, State.writeReg, State.readReg_w64, sext_slot hlt,
      addCarry_fst]
  | @addPtr d fields writable off k imm hd hΓ hk =>
    have hp := h.regs d hd
    rw [hΓ] at hp
    obtain ⟨a, l, hl, rfl, hw, hva⟩ := hasTy_ptr.mp hp
    obtain ⟨rfl, hlt⟩ := hk
    have hv : HasTy fetch sys Ψ ix (.ptr l.fields writable (off + k))
        (s.getReg d + BitVec.ofNat 64 (8 * k)) :=
      hasTy_ptr.mpr ⟨a, l, hl, rfl, hw, by rw [hva, slot_add]⟩
    refine ⟨{ s.setReg d (s.getReg d + BitVec.ofNat 64 (8 * k)) with
        flags := (addCarry (s.getReg d) (BitVec.ofNat 64 (8 * k)) false).2 }, ?_, rfl,
      (h.setReg hd hv).setFlags (P := Flags.Known) (Flags.ofResult_defined _ _ _)⟩
    simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, AluOp.eval,
      AluOp.writesDst, Result.ofOption, State.writeReg, State.readReg_w64, sext_slot hlt,
      addCarry_fst]
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
  induction ht generalizing s with
  | weaken hsem _ ihw => exact ihw (hsem Ψ' he hΨ _ _ h) hrip
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
  | @ret Γ Δ σ hst hsub =>
    obtain ⟨hv, hw⟩ := h.pop hst
    rw [hasTy_code] at hv
    have hc : s.canRead (s.getReg .rsp) 8 = true := by
      have := State.canRead_of_canWrite (h.canWrite_slot (i := 0) (by simp [hst]))
      simpa using this
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
    obtain ⟨v, hv, hp⟩ := (hcode.ext he).sound h hrip
    rw [hasTy_code] at hp
    have hex : exec sys (.jmp (.ind rm)) s = .next { s with rip := v } := by
      simp [exec, hv]
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ _ rfl
      (((h.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @callInd Γ Δ ret rm m hcode hroom hret hsub =>
    obtain ⟨v, hv, hp⟩ := (hcode.ext he).sound h hrip
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
  | @unreachable Γ i hun => exact absurd h (hun Ψ' he hΨ _ _)
  | @fnPtr Γ i r a sig hr hΓ hat _ ihc =>
    have hp := h.eqReg hr hΓ
    -- By the induction hypothesis the function is safe to enter for any caller.
    have hv : HasTy fetch sys Ψ' (n + 1) sig.ty (s.getReg r) := by
      rw [hasTy_fn]
      intro k hk Ψ'' he' hΨ'' saved ret rest room hK t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' a _ (hat saved ret rest room hK) t
        (ht.trans hp) hwt
    exact ihc (h.retype hr hv) hrip
  | @callFn Γ ret rm sig m hholds hroom hret hargs hsp hback hneed =>
    obtain ⟨v, hv, hp⟩ := (hholds.ext he).sound h hrip
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
      ⟨hback, hneed⟩ _ rfl
      (((hw'.sub (Δ := sig.entry (Γ.moveSp (-8)).regs ret Γ.stack m)
        ⟨fun r hr => by
            show Sub ((Γ.moveSp (-8)).regs r) _
            rw [CtxOf.moveSp_regs hr]
            exact hargs r hr,
          .refl _, rfl, fun _ _ => trivial, by
            show Sub ((Γ.moveSp (-8)).regs .rsp) _
            rw [CtxOf.moveSp_sp]
            exact hsp⟩).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @jmpFn Γ ret rm sig saved rest room hholds hK hsub =>
    obtain ⟨v, hv, hp⟩ := (hholds.ext he).sound h hrip
    rw [hasTy_fn] at hp
    have hex : exec sys (.jmp (.ind rm)) s = .next { s with rip := v } := by
      simp [exec, hv]
    rw [hex]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) Ψ' (.refl _) hΨ saved ret rest room hK _ rfl
      (((h.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @cover ι Γ Γ' i hsem _ ihc =>
    obtain ⟨x, hx⟩ := hsem Ψ' he hΨ _ _ h
    exact ihc x hx hrip
  | @codePtr Γ Δ i r a hr hΓ hΦ _ ihc =>
    have hp := h.regs r hr
    rw [hΓ, hasTy_eq] at hp
    -- By the induction hypothesis the code at `a` is safe in any state matching `Δ`.
    have hv : HasTy fetch sys Ψ' (n + 1) (.code Δ) (s.getReg r) := by
      rw [hasTy_code]
      intro k hk Ψ'' he' hΨ'' t ht hwt
      exact ih k (by omega) Ψ'' (he.trans he') hΨ'' a Δ hΦ t (ht.trans hp) hwt
    exact ihc (h.retype hr hv) hrip

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
