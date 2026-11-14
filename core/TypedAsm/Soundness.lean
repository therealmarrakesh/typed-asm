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
  cases h with
  | refl => exact hv
  | int => exact HasTy.int v
  | readOnly fields w index =>
    obtain ⟨a, l, hl, hf, hw, hva⟩ := hasTy_ptr.mp hv
    exact hasTy_ptr.mpr ⟨a, l, hl, hf, fun _ => hw rfl, hva⟩

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
  simp only [Disjoint] at *
  constructor <;> bv_omega

/-- Two different 8-byte slots of one region do not overlap. -/
theorem disjoint_slots {a : BitVec 64} {i j N : Nat} (hij : i ≠ j) (hi : 8 * i + 8 ≤ N)
    (hj : 8 * j + 8 ≤ N) (hN : N < 2 ^ 64) :
    Disjoint (a + BitVec.ofNat 64 (8 * i)) 8 (a + BitVec.ofNat 64 (8 * j)) 8 := by
  simp only [Disjoint]
  constructor <;> bv_omega

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
  simp only [store64, store32, store16, store8]

theorem store64_flags (s : State) (a v : BitVec 64) : (s.store64 a v).flags = s.flags := by
  simp only [store64, store32, store16, store8]

theorem store64_perm (s : State) (a v : BitVec 64) : (s.store64 a v).perm = s.perm := by
  simp only [store64, store32, store16, store8]

theorem store64_rip (s : State) (a v : BitVec 64) : (s.store64 a v).rip = s.rip := by
  simp only [store64, store32, store16, store8]

theorem load64_store64_same (s : State) (a v : BitVec 64) : (s.store64 a v).load64 a = v :=
  load_store_same s .w64 a v

theorem load64_store64_disjoint (s : State) {a b : BitVec 64} (v : BitVec 64)
    (h : Disjoint a 8 b 8) : (s.store64 a v).load64 b = s.load64 b :=
  load_store_disjoint s .w64 .w64 a b v h.1 h.2

end State

/-! ## The stack region -/

/-- The address of stack slot `j`, measured from the bottom of the stack region. -/
theorem slot_addr (Γ : Ctx) (s : State) (j : Nat) :
    stackBase Γ s + BitVec.ofNat 64 (8 * Γ.room + 8 * j)
      = s.getReg .rsp + BitVec.ofNat 64 (8 * j) := by
  simp only [stackBase]
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
    stackHeap := fun a l hl => by rw [hb]; exact h.stackHeap a l hl }

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
    stackHeap := fun a l hl => by rw [hb, hz]; exact h.stackHeap a l hl }

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
    stackHeap := fun a l hl => by rw [hb]; exact h.stackHeap a l hl }

/-- Replacing the flags with ones that satisfy the new context's flags predicate. -/
theorem setFlags {f : Flags} {P : Flags → Prop} (h : WellTyped fetch sys Ψ ix Γ s) (hf : P f) :
    WellTyped fetch sys Ψ ix { Γ with flags := P } { s with flags := f } :=
  { regs := h.regs, flags := hf, stackPerm := h.stackPerm, stackSize_lt := h.stackSize_lt,
    stack := h.stack, heapPerm := h.heapPerm, heap := h.heap, stackHeap := h.stackHeap }

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
    stackHeap := fun b l' hl' => by rw [hb]; exact h.stackHeap b l' hl' }

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
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl' }

/-- Pushing a value of type `τ` when there is room. -/
theorem push {n : Nat} {τ : Ty} {v : BitVec 64} (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF)
    (hroom : Γ.room = n + 1) (hv : HasTy fetch sys Ψ ix τ v) :
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
          simp only [Disjoint]; constructor <;> bv_omega
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
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl' }

/-- Popping: the top slot holds a value of its type, and the rest of the
state matches the context with that slot removed. -/
theorem pop {τ : Ty} {σ : List Ty} (h : WellTyped fetch sys Ψ ix Γ s) (hst : Γ.stack = τ :: σ) :
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
      stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl' }

/-- Reserving `k` stack slots: they become integer slots. -/
theorem allocFrame {k m : Nat} (h : WellTyped fetch sys Ψ ix Γ s) (hroom : Γ.room = m + k) :
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
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl' }

/-- Releasing the top `k` stack slots. -/
theorem freeFrame {k : Nat} {top rest : List Ty} (h : WellTyped fetch sys Ψ ix Γ s)
    (hst : Γ.stack = top ++ rest) (hk : top.length = k) :
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
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl' }

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
    (hframe : ∀ y, Disjoint (a + BitVec.ofNat 64 (8 * i)) 8 y 8 → s'.load64 y = s.load64 y) :
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
    stackHeap := fun b l' hl' => by rw [hb]; exact h.stackHeap b l' hl' }

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
  simp only [State.setReg, State.getReg]
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
      s'.load64 y = s.load64 y) :
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
    stackHeap := fun b l' hl' => by rw [hb, hz]; exact h.stackHeap b l' hl' }

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
  simp only [Disjoint] at hd
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
  simp only [Disjoint] at hd
  exact State.load64_store8_disjoint s v (by bv_omega)

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
  | @global base l i k disp hl hwr haddr hi hk =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i + k) := by
      simp only [State.ea, hrip, haddr]
    have hc := h.canWrite_inner (m := w.bytes.toNat) hl hwr hilt hk
    refine ⟨s.store w (base + BitVec.ofNat 64 (8 * i + k)) v, ?_, State.rip_store _ _ _ _,
      h.writeInt hΨ hl hi (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _) (fun y hd => by
          rw [inner_split]; exact State.load64_store_inner s w _ hk hd)⟩
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
          rw [inner_split]; exact State.load64_store_inner s w _ hk hd)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]
  | @slot i k disp τ hdisp hi hk =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea := State.ea_inner s .rsp hdisp
    have hc := h.canWrite_slot_inner (m := w.bytes.toNat) hilt hk
    refine ⟨s.store w (s.getReg .rsp + BitVec.ofNat 64 (8 * i + k)) v, ?_, State.rip_store _ _ _ _,
      h.writeSlotInt hΨ hilt (State.regs_store _ _ _ _) (State.flags_store _ _ _ _)
        (State.perm_store _ _ _ _) (fun y hd => by
          rw [inner_split]; exact State.load64_store_inner s w _ hk hd)⟩
    simp only [State.writeRM, hea, State.write, hc, ite_true]

/-- Writing any byte to a writable operand succeeds likewise. -/
theorem WriteIntOk.writeRM8 {rm : RM} {Γ' : Ctx} (hw : WriteIntOk Ψ next Γ 1 rm Γ')
    (h : WellTyped fetch sys Ψ ix Γ s) (hΨ : Ψ.WF) (hrip : s.rip = next) (v : BitVec 8) :
    ∃ s', s.writeRM8 rm v = .next s' ∧ s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases hw with
  | @global base l i k disp hl hwr haddr hi hk =>
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea : s.ea (.rip disp) = base + BitVec.ofNat 64 (8 * i + k) := by
      simp only [State.ea, hrip, haddr]
    have hc := h.canWrite_inner (m := 1) hl hwr hilt hk
    refine ⟨s.store8 (base + BitVec.ofNat 64 (8 * i + k)) v, ?_, rfl,
      h.writeInt hΨ hl hi rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store8_inner s _ hk hd)⟩
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
        rw [inner_split]; exact State.load64_store8_inner s _ hk hd)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]
  | @slot i k disp τ hdisp hi hk =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    have hea := State.ea_inner s .rsp hdisp
    have hc := h.canWrite_slot_inner (m := 1) hilt hk
    refine ⟨s.store8 (s.getReg .rsp + BitVec.ofNat 64 (8 * i + k)) v, ?_, rfl,
      h.writeSlotInt hΨ hilt rfl rfl rfl (fun y hd => by
        rw [inner_split]; exact State.load64_store8_inner s _ hk hd)⟩
    simp only [State.writeRM8, hea, State.write8, hc, ite_true]

/-- An operand holding a code pointer can be read, and what is read is a code pointer. -/
theorem CodeAt.sound {rm : RM} {Δ : Ctx} (hc : CodeAt Ψ next Γ rm Δ)
    (h : WellTyped fetch sys Ψ ix Γ s) (hrip : s.rip = next) :
    ∃ v, s.readRM .w64 rm = .next v ∧ HasTy fetch sys Ψ ix (.code Δ) v := by
  cases hc with
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

/-! ## Multiply and divide -/

/-- A multiply or divide either produces a result or raises a divide error. -/
theorem MulDivOp.eval_cases {n : Nat} (op : MulDivOp) (hi lo src : BitVec n) :
    (∃ x, op.eval hi lo src = .next x) ∨ op.eval hi lo src = .fault .divideError := by
  cases op
  · exact .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · simp only [MulDivOp.eval]
    split
    · exact .inr rfl
    · exact .inl ⟨_, rfl⟩
  · simp only [MulDivOp.eval]
    split
    · exact .inr rfl
    · exact .inl ⟨_, rfl⟩

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

/-- A divide either raises a divide error or continues. -/
theorem mulDiv_sound {Γ : Ctx} {s : State} {op : MulDivOp} {w : Width} {src : RM}
    (hr : ReadOk Ψ next Γ w.bytes.toNat src) (h : WellTyped fetch sys Ψ ix Γ s)
    (hrip : s.rip = next) :
    (exec sys (.mulDiv op w src) s).isSafe = true ∧
      ∀ s', exec sys (.mulDiv op w src) s = .next s' →
        s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix (Γ.afterMulDiv Flags.Any) s' := by
  obtain ⟨a, ha⟩ := hr.readRM h hrip
  rcases op.eval_cases (s.readReg w .rdx) (s.readReg w .rax) a with ⟨⟨lo, hi, fl⟩, hx⟩ | hx
  · have he : exec sys (.mulDiv op w src) s
        = .next { (s.writeReg w .rax lo).writeReg w .rdx hi with flags := fl } := by
      simp [exec, ha, hx]
    rw [he]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact ⟨rfl, ((h.setReg (by decide) (HasTy.int _)).setReg (by decide) (HasTy.int _)).setFlags
      (P := Flags.Any) trivial⟩
  · have he : exec sys (.mulDiv op w src) s = .fault .divideError := by
      simp [exec, ha, hx]
    rw [he]
    exact ⟨rfl, fun s' heq => nomatch heq⟩

/-- A straight-line typed instruction other than a divide, run in a matching
state, continues to the next instruction and leaves a state matching the
rule's result context. -/
theorem Straight.sound_next {next : BitVec 64} {Γ Γ' : Ctx} {i : Instr}
    (ht : Straight Ψ next Γ i Γ') (hnd : i.isDivide = false)
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
  | divRM => exact absurd hnd (by simp [Instr.isDivide])
  | idivRM => exact absurd hnd (by simp [Instr.isDivide])
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

/-- A straight-line typed instruction, run in a matching state, has an
acceptable outcome, and if it continues, it continues to the next instruction
in a state matching the rule's result context. (A divide may instead raise a
divide error.) -/
theorem Straight.sound {next : BitVec 64} {Γ Γ' : Ctx} {i : Instr} (ht : Straight Ψ next Γ i Γ')
    (hΨ : Ψ.WF) {s : State} (h : WellTyped fetch sys Ψ ix Γ s) (hrip : s.rip = next) :
    (exec sys i s).isSafe = true ∧
      ∀ s', exec sys i s = .next s' → s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases hd : i.isDivide
  · obtain ⟨s', he, hr, hw⟩ := ht.sound_next hd hΨ h hrip
    rw [he]
    refine ⟨rfl, fun s'' heq => ?_⟩
    cases heq
    exact ⟨hr, hw⟩
  · cases ht with
    | divRM hr => exact mulDiv_sound hr h hrip
    | idivRM hr => exact mulDiv_sound hr h hrip
    | _ => simp [Instr.isDivide] at hd

/-! ## All typed instructions -/

/-- What the induction on step count provides: every program point is safe
for `n` steps from any state matching its context at count `n`. -/
def SafeUpTo (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) : Prop :=
  ∀ k, k ≤ n → ∀ a Δ, Φ a Δ → ∀ s : State, s.rip = a →
    WellTyped fetch sys Ψ k Δ s → SafeN fetch sys k s

/-- Entering code that accepts the current context is safe. -/
theorem SafeUpTo.accepts {n : Nat} (ih : SafeUpTo Φ fetch sys Ψ n) {a : BitVec 64} {Γ : Ctx}
    {s : State} (hacc : Accepts Φ a Γ) (hr : s.rip = a)
    (h : WellTyped fetch sys Ψ (n + 1) Γ s) : SafeN fetch sys n s := by
  obtain ⟨Δ, hΔ, hsub⟩ := hacc
  exact ih n (Nat.le_refl n) a Δ hΔ s hr ((h.sub hsub).mono (Nat.le_succ n))

/-- A typed instruction, run in a matching state at the right address, has an
acceptable outcome, and any state it continues to is safe for the remaining steps. -/
theorem HasType.sound {next : BitVec 64} {Γ : Ctx} {i : Instr} {n : Nat}
    (ht : HasType Φ fetch sys Ψ next Γ i) (hΨ : Ψ.WF) (hsys : SysOk fetch sys Ψ)
    (ih : SafeUpTo Φ fetch sys Ψ n) {s : State}
    (h : WellTyped fetch sys Ψ (n + 1) Γ s) (hrip : s.rip = next) :
    (exec sys i s).isSafe = true ∧ ∀ s', exec sys i s = .next s' → SafeN fetch sys n s' := by
  induction ht generalizing s with
  | weaken hsem _ ihw => exact ihw (hsem _ _ h) hrip
  | straight hst hacc =>
    obtain ⟨hsafe, hnext⟩ := hst.sound hΨ h hrip
    refine ⟨hsafe, fun s' heq => ?_⟩
    obtain ⟨hr, hw⟩ := hnext s' heq
    exact ih.accepts hacc (hr.trans hrip) hw
  | @jmp Γ d hacc =>
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact ih.accepts hacc (by rw [← hrip]) (h.congr rfl rfl rfl rfl)
  | @jcc Γ c d hdec hacc hfall =>
    obtain ⟨b, hb⟩ := hdec _ h.flags
    cases b
    · have he : exec sys (.jcc c d) s = .next s := by simp [exec, hb, Result.ofOption]
      rw [he]
      refine ⟨rfl, fun s' heq => ?_⟩
      cases heq
      exact ih.accepts (hfall _ h.flags hb) hrip h
    · have he : exec sys (.jcc c d) s = .next { s with rip := s.rip + d.signExtend 64 } := by
        simp [exec, hb, Result.ofOption]
      rw [he]
      refine ⟨rfl, fun s' heq => ?_⟩
      cases heq
      exact ih.accepts (hacc _ h.flags hb) (by rw [← hrip]) (h.congr rfl rfl rfl rfl)
  | @call Γ ret d m hroom hret hacc =>
    have hw : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true :=
      h.canWrite_push hroom
    -- The return address is a code pointer: by the induction hypothesis the
    -- instruction after the call is safe in any state matching its context.
    have hv : HasTy fetch sys Ψ (n + 1) (.code ret) s.rip := by
      rw [hasTy_code]
      intro k hk t ht hwt
      exact ih k (by omega) next ret hret t (ht.trans hrip) hwt
    have he : exec sys (.call (.rel d)) s
        = .next { (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip with
            rip := s.rip + d.signExtend 64 } := by
      have hpush : s.push64 s.rip
          = .next ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip) := by
        simp only [State.push64, State.write64, hw, ite_true]
      simp [exec, hpush]
    have hw' := h.push hΨ hroom hv
    generalize (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip = s₁
      at he hw'
    rw [he]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact ih.accepts hacc (by rw [← hrip]) (hw'.congr rfl rfl rfl rfl)
  | @ret Γ Δ σ hst hsub =>
    obtain ⟨hv, hw⟩ := h.pop hst
    rw [hasTy_code] at hv
    have hc : s.canRead (s.getReg .rsp) 8 = true := by
      have := State.canRead_of_canWrite (h.canWrite_slot (i := 0) (by simp [hst]))
      simpa using this
    have he : exec sys .ret s
        = .next { s.setReg .rsp (s.getReg .rsp + 8) with rip := s.load64 (s.getReg .rsp) } := by
      simp [exec, State.pop64, State.read64, hc]
    rw [he]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hv n (Nat.lt_succ_self n) _ rfl
      (((hw.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | syscall hacc =>
    obtain ⟨hsafe, hnext⟩ := hsys _ _ _ h
    refine ⟨hsafe, fun s' heq => ?_⟩
    obtain ⟨hr, hw⟩ := hnext s' heq
    exact ih.accepts hacc (hr.trans hrip) hw
  | @jmpInd Γ Δ rm hcode hsub =>
    obtain ⟨v, hv, hp⟩ := hcode.sound h hrip
    rw [hasTy_code] at hp
    have he : exec sys (.jmp (.ind rm)) s = .next { s with rip := v } := by
      simp [exec, hv]
    rw [he]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) _ rfl
      (((h.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @callInd Γ Δ ret rm m hcode hroom hret hsub =>
    obtain ⟨v, hv, hp⟩ := hcode.sound h hrip
    rw [hasTy_code] at hp
    have hw : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true :=
      h.canWrite_push hroom
    have hra : HasTy fetch sys Ψ (n + 1) (.code ret) s.rip := by
      rw [hasTy_code]
      intro k hk t ht hwt
      exact ih k (by omega) next ret hret t (ht.trans hrip) hwt
    have he : exec sys (.call (.ind rm)) s
        = .next { (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip with
            rip := v } := by
      have hpush : s.push64 s.rip
          = .next ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip) := by
        simp only [State.push64, State.write64, hw, ite_true]
      simp [exec, hv, hpush]
    have hw' := h.push hΨ hroom hra
    generalize (s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) s.rip = s₁
      at he hw'
    rw [he]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) _ rfl
      (((hw'.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @unreachable Γ i hun => exact absurd h (hun _ _)
  | @codePtr Γ Δ i r a hr hΓ hΦ _ ihc =>
    have hp := h.regs r hr
    rw [hΓ, hasTy_eq] at hp
    -- By the induction hypothesis the code at `a` is safe in any state matching `Δ`.
    have hv : HasTy fetch sys Ψ (n + 1) (.code Δ) (s.getReg r) := by
      rw [hasTy_code]
      intro k hk t ht hwt
      exact ih k (by omega) a Δ hΦ t (ht.trans hp) hwt
    exact ihc (h.retype hr hv) hrip

/-! ## Programs -/

/-- In a well-typed program, every program point is safe for `n` steps from
any state matching its context at step count `n`. -/
theorem safeUpTo (hP : ProgramOk Φ fetch sys Ψ) (hΨ : Ψ.WF) (hsys : SysOk fetch sys Ψ) (n : Nat) :
    SafeUpTo Φ fetch sys Ψ n := by
  induction n with
  | zero =>
    intro k hk a Δ _ s _ _
    have : k = 0 := by omega
    subst this
    trivial
  | succ n ih =>
    intro k hk a Δ hΔ s hr hw
    by_cases hkn : k ≤ n
    · exact ih k hkn a Δ hΔ s hr hw
    · have : k = n + 1 := by omega
      subst this
      obtain ⟨i, len, hf, ht⟩ := hP a Δ hΔ
      have := ht.sound hΨ hsys ih (s := { s with rip := s.rip + len })
        (hw.congr rfl rfl rfl rfl) (by rw [← hr])
      simpa only [SafeN, TypedAsm.step, hr, hf] using this

/-- **Soundness.** A well-typed program, started in a well-typed state, with a
well-formed memory typing and a well-behaved operating system, is safe: it
never gets stuck, never page-faults, and never executes an invalid opcode. -/
theorem soundness {s : State} (hP : ProgramOk Φ fetch sys Ψ) (hΨ : Ψ.WF) (hsys : SysOk fetch sys Ψ)
    (hs : StateOk Φ fetch sys Ψ s) : Safe fetch sys s := by
  obtain ⟨Γ, hΓ, hw⟩ := hs
  exact safe_of_safeN (fun n => safeUpTo hP hΨ hsys n n (Nat.le_refl n) s.rip Γ hΓ s rfl (hw n))

end TypedAsm
