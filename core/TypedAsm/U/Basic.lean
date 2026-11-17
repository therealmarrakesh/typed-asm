import TypedAsm.U.Types

/-!
# What knowing something of a value comes to

What each form of knowledge says, spelled out; that it survives a smaller
step count and a larger memory typing; and that what follows from it by
`Sub` is so.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat}

theorem HasTy.any (v : BitVec 64) : HasTy fetch sys Ψ n .any v := by
  simp [HasTy]

theorem hasTy_ptr {shape : Shape} {writable : Bool} {off : Nat} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.ptr shape writable off) v ↔
      ∃ a l, Ψ a = some l ∧ l.shape = shape ∧ (writable = true → l.writable = true) ∧
        v = a + BitVec.ofNat 64 off := by
  simp [HasTy]

theorem hasTy_ref {tag : Nat} {writable : Bool} {off : Nat} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.ref tag writable off) v ↔
      ∃ a l, Ψ a = some l ∧ l.tag = some tag ∧ (writable = true → l.writable = true) ∧
        v = a + BitVec.ofNat 64 off := by
  simp [HasTy]

theorem hasTy_nullable {τ : Ty} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.nullable τ) v ↔ v = 0 ∨ HasTy fetch sys Ψ n τ v := by
  rw [HasTy]

theorem hasTy_orErr {τ : Ty} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.orErr τ) v ↔ SysErr v ∨ HasTy fetch sys Ψ n τ v := by
  rw [HasTy]

theorem hasTy_str {more : Bool} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.str more) v ↔
      ∃ a l off, Ψ a = some l ∧ off + (if more then 1 else 0) < l.text ∧
        v = a + BitVec.ofNat 64 (l.shape.size + off) := by
  simp [HasTy]

/-- A value is code wanting a family of contexts if entering it, in any
state matching any of them, is safe for any smaller number of steps, now and
however the memory typing grows. -/
theorem hasTy_code {pre : Seq → Ctx} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.code pre) v ↔
      ∀ x : Seq, ∀ k, k < n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = v →
        WellTyped fetch sys Ψ' k (pre x) s → SafeN fetch sys k s := by
  rw [HasTy]

/-- A value is a function if entering it, from any caller that hands it
what its signature asks, is safe for any smaller number of steps. -/
theorem hasTy_fn {sig : Sig} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.fn sig) v ↔
      ∀ k, k < n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
        ∀ (p : Seq) (saved : Reg → BitVec 64) (lo : BitVec 64) (m : Nat) (ra : BitVec 64)
          (frame : List Region) (s : State), s.rip = v →
        WellTyped fetch sys Ψ' k (sig.entry p saved lo m ra frame) s → SafeN fetch sys k s := by
  rw [HasTy]

/-- What is known of a value at a step count is known at every smaller one. -/
theorem HasTy.mono {m : Nat} {τ : Ty} {v : BitVec 64} (h : HasTy fetch sys Ψ n τ v)
    (hle : m ≤ n) : HasTy fetch sys Ψ m τ v := by
  cases τ with
  | any => exact HasTy.any v
  | ptr shape writable off => exact hasTy_ptr.mpr (hasTy_ptr.mp h)
  | ref tag writable off => exact hasTy_ref.mpr (hasTy_ref.mp h)
  | nullable τ =>
    rw [hasTy_nullable] at h ⊢
    exact h.imp id (fun h' => HasTy.mono h' hle)
  | orErr τ =>
    rw [hasTy_orErr] at h ⊢
    exact h.imp id (fun h' => HasTy.mono h' hle)
  | str more => exact hasTy_str.mpr (hasTy_str.mp h)
  | code pre =>
    rw [hasTy_code] at h ⊢
    exact fun x k hk => h x k (by omega)
  | fn sig =>
    rw [hasTy_fn] at h ⊢
    exact fun k hk => h k (by omega)
termination_by sizeOf τ

/-- And stays known when the memory typing grows. -/
theorem HasTy.ext {Ψ' : MemTy} {τ : Ty} {v : BitVec 64} (h : HasTy fetch sys Ψ n τ v)
    (he : Ψ.Ext Ψ') : HasTy fetch sys Ψ' n τ v := by
  cases τ with
  | any => exact HasTy.any v
  | ptr shape writable off =>
    obtain ⟨a, l, hl, h'⟩ := hasTy_ptr.mp h
    exact hasTy_ptr.mpr ⟨a, l, he.blocks a l hl, h'⟩
  | ref tag writable off =>
    obtain ⟨a, l, hl, h'⟩ := hasTy_ref.mp h
    exact hasTy_ref.mpr ⟨a, l, he.blocks a l hl, h'⟩
  | nullable τ =>
    rw [hasTy_nullable] at h ⊢
    exact h.imp id (fun h' => HasTy.ext h' he)
  | orErr τ =>
    rw [hasTy_orErr] at h ⊢
    exact h.imp id (fun h' => HasTy.ext h' he)
  | str more =>
    obtain ⟨a, l, off, hl, h'⟩ := hasTy_str.mp h
    exact hasTy_str.mpr ⟨a, l, off, he.blocks a l hl, h'⟩
  | code pre =>
    rw [hasTy_code] at h ⊢
    exact fun x k hk Ψ'' he' => h x k hk Ψ'' (he.trans he')
  | fn sig =>
    rw [hasTy_fn] at h ⊢
    exact fun k hk Ψ'' he' => h k hk Ψ'' (he.trans he')
termination_by sizeOf τ

/-- **What follows by `Sub` is so.** -/
theorem HasTy.sub {τ υ : Ty} {v : BitVec 64} (h : Sub v τ υ) (hv : HasTy fetch sys Ψ n τ v) :
    HasTy fetch sys Ψ n υ v := by
  induction h with
  | refl => exact hv
  | any => exact HasTy.any _
  | readOnly v shape w off =>
    obtain ⟨a, l, hl, hf, hw, hva⟩ := hasTy_ptr.mp hv
    exact hasTy_ptr.mpr ⟨a, l, hl, hf, fun _ => hw rfl, hva⟩
  | refReadOnly v tag w off =>
    obtain ⟨a, l, hl, ht, hw, hva⟩ := hasTy_ref.mp hv
    exact hasTy_ref.mpr ⟨a, l, hl, ht, fun _ => hw rfl, hva⟩
  | nullable _ ih => exact hasTy_nullable.mpr (.inr (ih hv))
  | null τ υ => exact hasTy_nullable.mpr (.inl rfl)
  | nonNull τ hne => exact (hasTy_nullable.mp hv).resolve_left hne
  | nullableMono _ ih => exact hasTy_nullable.mpr ((hasTy_nullable.mp hv).imp id ih)
  | orErr _ ih => exact hasTy_orErr.mpr (.inr (ih hv))
  | err τ υ he => exact hasTy_orErr.mpr (.inl he)
  | noErr τ hne => exact (hasTy_orErr.mp hv).resolve_left hne
  | orErrMono _ ih => exact hasTy_orErr.mpr ((hasTy_orErr.mp hv).imp id ih)
  | strLess v more =>
    obtain ⟨a, l, off, hl, hoff, hva⟩ := hasTy_str.mp hv
    exact hasTy_str.mpr ⟨a, l, off, hl, by
      simp only [↓reduceIte] at hoff
      cases more <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega, hva⟩
  | codeMap v pre f =>
    rw [hasTy_code] at hv ⊢
    exact fun x => hv (f x)

/-- Matching a context carries over to any weaker notion of what is known. -/
theorem Matches.imp {H H' : Ty → BitVec 64 → Prop} {Γ : Ctx} {s : State}
    (h : Matches H Ψ Γ s) (himp : ∀ τ v, H τ v → H' τ v) : Matches H' Ψ Γ s :=
  { val := h.val
    known := fun f hf => himp _ _ (h.known f hf)
    flags := h.flags
    heapPerm := h.heapPerm
    heap := fun a l hl p hp => himp _ _ (h.heap a l hl p hp)
    text := h.text
    said := h.said
    held := h.held }

/-- A state well typed at a step count is well typed at every smaller one. -/
theorem WellTyped.mono {m : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (hle : m ≤ n) : WellTyped fetch sys Ψ m Γ s :=
  Matches.imp h (fun _ _ hv => hv.mono hle)

end TypedAsm.U
