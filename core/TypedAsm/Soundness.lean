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
  | readOnly fields w =>
    obtain ⟨l, hl, hf, hw⟩ := hasTy_ptr.mp hv
    exact hasTy_ptr.mpr ⟨l, hl, hf, fun _ => hw rfl⟩

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
    flags := fun hfl => by rw [hf]; exact h.flags hfl
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
    flags := fun hf => h.flags (hs.flags hf)
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

/-- Replacing the flags, provided they are known whenever the new context says so. -/
theorem setFlags {f : Flags} {b : Bool} (h : WellTyped fetch sys Ψ ix Γ s)
    (hf : b = true → f.defined = true) :
    WellTyped fetch sys Ψ ix { Γ with flags := b } { s with flags := f } :=
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
    flags := fun hf => by rw [State.store64_flags]; exact h.flags hf
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
    flags := fun hf => by rw [State.store64_flags]; exact h.flags hf
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
    flags := fun hf => by rw [State.store64_flags]; exact h.flags hf
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

/-- After a two-operand operation on register `d` that left known flags. -/
theorem afterAlu {op : AluOp} {d : Reg} {fl : Flags} (h : WellTyped fetch sys Ψ ix Γ s) (hd : d ≠ .rsp)
    (hdef : fl.defined = true) (v : BitVec 64) :
    WellTyped fetch sys Ψ ix (Γ.afterAlu op d)
      { (if op.writesDst then s.setReg d v else s) with flags := fl } := by
  cases hwd : op.writesDst
  · simp only [CtxOf.afterAlu, hwd, Bool.false_eq_true, ↓reduceIte]
    exact h.setFlags (fun _ => hdef)
  · simp only [CtxOf.afterAlu, hwd, ↓reduceIte]
    exact (h.setReg hd (HasTy.int v)).setFlags (fun _ => hdef)

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

namespace State

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

/-! ## Instructions that continue to the next one -/

/-- A straight-line typed instruction, run in a matching state, continues to
the next instruction and leaves a state matching the rule's result context. -/
theorem Straight.sound {Γ Γ' : Ctx} {i : Instr} (ht : Straight Γ i Γ') (hΨ : Ψ.WF)
    {s : State} (h : WellTyped fetch sys Ψ ix Γ s) :
    ∃ s', exec sys i s = .next s' ∧ s'.rip = s.rip ∧ WellTyped fetch sys Ψ ix Γ' s' := by
  cases ht with
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
    refine ⟨s.writeReg w d (imm.signExtend w.bits), ?_, rfl, h.setReg hd (HasTy.int _)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst]
  | @movAbs d imm hd =>
    refine ⟨s.setReg d imm, ?_, rfl, h.setReg hd (HasTy.int _)⟩
    simp [exec]
  | @lea w d m hd =>
    refine ⟨s.writeReg w d ((s.ea m).setWidth w.bits), ?_, rfl, h.setReg hd (HasTy.int _)⟩
    simp [exec]
  | @loadField d b fields writable i disp τ hd hb hΓ hi hdisp =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨l, hl, rfl, -⟩ := hasTy_ptr.mp hp
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨s.setReg d (s.load64 (s.getReg b + BitVec.ofNat 64 (8 * i))), ?_, rfl,
      h.setReg hd (h.heap _ l hl i τ hi)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.ea_slot s b hdisp,
      State.read_w64 (h.canRead_field hl hilt), State.writeReg]
  | @storeField b src fields i disp τ hb hs hΓ hi hsub hdisp =>
    have hp := h.regs b hb
    rw [hΓ] at hp
    obtain ⟨l, hl, rfl, hw⟩ := hasTy_ptr.mp hp
    have hilt : i < l.fields.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨s.store64 (s.getReg b + BitVec.ofNat 64 (8 * i)) (s.getReg src), ?_,
      State.store64_rip _ _ _, h.storeField hΨ hl hi ((h.regs src hs).sub hsub)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.ea_slot s b hdisp,
      State.readReg_w64, State.write_w64 _ (h.canWrite_field hl (hw rfl) hilt)]
  | @loadStack d i disp τ hd hi hdisp =>
    have hilt : i < Γ.stack.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨s.setReg d (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i))), ?_, rfl,
      h.setReg hd (h.stack i τ hi)⟩
    simp [exec, State.writeRM, Operands.src, Operands.dst, State.ea_slot s .rsp hdisp,
      State.read_w64 (State.canRead_of_canWrite (h.canWrite_slot hilt)), State.writeReg]
  | @storeStack src i disp hs hi hdisp =>
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
      (fun hrc => by
        have := h.flags (hc hrc)
        simp only [Flags.defined, Bool.and_eq_true] at this
        exact this.1.1.1)
    refine ⟨{ (if op.writesDst then s.setReg d (r.setWidth 64) else s) with flags := fl }, ?_, ?_,
      h.afterAlu hd hdef _⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, he, Result.ofOption,
          hwd, State.writeReg]
    · cases op.writesDst <;> rfl
  | @aluRI op w d imm hd hc =>
    obtain ⟨r, fl, he, hdef⟩ := op.eval_some (cf := s.flags.cf) (s.readReg w d)
      (imm.signExtend w.bits) (fun hrc => by
        have := h.flags (hc hrc)
        simp only [Flags.defined, Bool.and_eq_true] at this
        exact this.1.1.1)
    refine ⟨{ (if op.writesDst then s.setReg d (r.setWidth 64) else s) with flags := fl }, ?_, ?_,
      h.afterAlu hd hdef _⟩
    · cases hwd : op.writesDst <;>
        simp [exec, State.readRM, State.writeRM, Operands.src, Operands.dst, he, Result.ofOption,
          hwd, State.writeReg]
    · cases op.writesDst <;> rfl
  | @test w r src =>
    refine ⟨{ s with flags := .ofResult (s.readReg w r &&& s.readRI w src) false false }, ?_, rfl,
      h.setFlags (b := true) (fun _ => Flags.ofResult_defined _ _ _)⟩
    simp [exec, State.readRM]

/-! ## All typed instructions -/

/-- What the induction on step count provides: every program point is safe
for `n` steps from any state matching its context at count `n`. -/
def SafeUpTo (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) : Prop :=
  ∀ k, k ≤ n → ∀ a Δ, Φ a = some Δ → ∀ s : State, s.rip = a →
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
    (ht : HasType Φ next Γ i) (hΨ : Ψ.WF) (hsys : SysOk fetch sys Ψ)
    (ih : SafeUpTo Φ fetch sys Ψ n) {s : State}
    (h : WellTyped fetch sys Ψ (n + 1) Γ s) (hrip : s.rip = next) :
    (exec sys i s).isSafe = true ∧ ∀ s', exec sys i s = .next s' → SafeN fetch sys n s' := by
  cases ht with
  | straight hst hacc =>
    obtain ⟨s', he, hr, hw⟩ := hst.sound hΨ h
    rw [he]
    refine ⟨rfl, fun s'' heq => ?_⟩
    cases heq
    exact ih.accepts hacc (hr.trans hrip) hw
  | @jmp d hacc =>
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact ih.accepts hacc (by rw [← hrip]) (h.congr rfl rfl rfl rfl)
  | @jcc c d hf hacc hfall =>
    obtain ⟨b, hb⟩ := Cond.eval_some (h.flags hf) c
    cases b
    · have he : exec sys (.jcc c d) s = .next s := by simp [exec, hb, Result.ofOption]
      rw [he]
      refine ⟨rfl, fun s' heq => ?_⟩
      cases heq
      exact ih.accepts hfall hrip h
    · have he : exec sys (.jcc c d) s = .next { s with rip := s.rip + d.signExtend 64 } := by
        simp [exec, hb, Result.ofOption]
      rw [he]
      refine ⟨rfl, fun s' heq => ?_⟩
      cases heq
      exact ih.accepts hacc (by rw [← hrip]) (h.congr rfl rfl rfl rfl)
  | @jmpReg Δ r hr hΓ hsub =>
    have hp := h.regs r hr
    rw [hΓ, hasTy_code] at hp
    have he : exec sys (.jmp (.ind (.reg r))) s = .next { s with rip := s.getReg r } := by
      simp [exec, State.readRM, State.readReg_w64]
    rw [he]
    refine ⟨rfl, fun s' heq => ?_⟩
    cases heq
    exact hp n (Nat.lt_succ_self n) _ rfl
      (((h.sub hsub).mono (Nat.le_succ n)).congr rfl rfl rfl rfl)
  | @call ret d m hroom hret hacc =>
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
  | @ret Δ σ hst hsub =>
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
    obtain ⟨hsafe, hnext⟩ := hsys (n + 1) Γ s h
    refine ⟨hsafe, fun s' heq => ?_⟩
    obtain ⟨hr, hw⟩ := hnext s' heq
    exact ih.accepts hacc (hr.trans hrip) hw

/-! ## Programs -/

/-- In a well-typed program, every program point is safe for `n` steps from
any state matching its context at step count `n`. -/
theorem safeUpTo (hP : ProgramOk Φ fetch) (hΨ : Ψ.WF) (hsys : SysOk fetch sys Ψ) (n : Nat) :
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
theorem soundness {s : State} (hP : ProgramOk Φ fetch) (hΨ : Ψ.WF) (hsys : SysOk fetch sys Ψ)
    (hs : StateOk Φ fetch sys Ψ s) : Safe fetch sys s := by
  obtain ⟨Γ, hΓ, hw⟩ := hs
  exact safe_of_safeN (fun n => safeUpTo hP hΨ hsys n n (Nat.le_refl n) s.rip Γ hΓ s rfl (hw n))

end TypedAsm
