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

/-- The block a value is known to point into, by what is known of it: its
shape, whether it may be written through the value, and how far in. A
pointer says the shape; a pointer by kind says the kind, whose shape the
memory typing has. -/
def Ty.pointee (kinds : Nat → Option Shape) : Ty → Option (Shape × Bool × Nat)
  | .ptr Sh w off => some (Sh, w, off)
  | .ref tag w off => (kinds tag).map fun Sh => (Sh, w, off)
  | _ => none

/-- **A value known to point into a block does.** A pointer by kind is a
pointer to a block of the kind's shape. -/
theorem hasTy_pointee (hwf : Ψ.WF) {τ : Ty} {Sh : Shape} {w : Bool} {off : Nat} {v : BitVec 64}
    (hτ : τ.pointee Ψ.kinds = some (Sh, w, off)) (h : HasTy fetch sys Ψ n τ v) :
    ∃ a l, Ψ a = some l ∧ l.shape = Sh ∧ (w = true → l.writable = true) ∧
      v = a + BitVec.ofNat 64 off := by
  cases τ with
  | ptr Sh' w' off' =>
    cases hτ
    exact hasTy_ptr.mp h
  | ref tag w' off' =>
    obtain ⟨a, l, hl, htag, hlw, hv⟩ := hasTy_ref.mp h
    have hk := hwf.kinds a l hl tag htag
    simp only [Ty.pointee, hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hτ
    obtain ⟨rfl, rfl, rfl⟩ := hτ
    exact ⟨a, l, hl, rfl, hlw, hv⟩
  | _ => cases hτ

theorem hasTy_nullable {τ : Ty} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.nullable τ) v ↔ v = 0 ∨ HasTy fetch sys Ψ n τ v := by
  rw [HasTy]

theorem hasTy_orErr {τ : Ty} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.orErr τ) v ↔ SysErr v ∨ HasTy fetch sys Ψ n τ v := by
  rw [HasTy]

theorem hasTy_str {c : BitVec 64} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.str c) v ↔
      ∃ a l off, Ψ a = some l ∧ off < l.text ∧ (c ≠ 0 → off + 1 < l.text) ∧
        v = a + BitVec.ofNat 64 (l.shape.size + off) := by
  simp [HasTy]

/-- A value is code wanting a family of contexts if entering it, in any
state matching any of them, is safe for any smaller number of steps, now and
however the memory typing grows. -/
theorem hasTy_code {pre : Fam → Ctx} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.code pre) v ↔
      ∀ x : Fam, ∀ k, k < n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = v →
        WellTyped fetch sys Ψ' k (pre x) s → SafeN fetch sys k s := by
  rw [HasTy]

theorem hasTy_range {lo hi v : BitVec 64} :
    HasTy fetch sys Ψ n (.range lo hi) v ↔ v - lo ≤ hi - lo := by
  rw [HasTy]

theorem hasTy_arr {count : BitVec 64} {τ : Ty} {st : Nat} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.arr count τ st) v ↔
      ∃ a l off, Ψ a = some l ∧ v = a + BitVec.ofNat 64 off ∧
        ∀ i, i < count.toNat → (off + st * i, τ) ∈ l.shape.vals := by
  rw [HasTy]

theorem hasTy_upTo {w v : BitVec 64} {strict : Bool} :
    HasTy fetch sys Ψ n (.upTo w strict) v ↔ if strict then v < w else v ≤ w := by
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
  | range lo hi => exact hasTy_range.mpr (hasTy_range.mp h)
  | arr count τ st => exact hasTy_arr.mpr (hasTy_arr.mp h)
  | upTo w strict => exact hasTy_upTo.mpr (hasTy_upTo.mp h)
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
  | range lo hi => exact hasTy_range.mpr (hasTy_range.mp h)
  | arr count τ st =>
    obtain ⟨a, l, off, hl, h'⟩ := hasTy_arr.mp h
    exact hasTy_arr.mpr ⟨a, l, off, he.blocks a l hl, h'⟩
  | upTo w strict => exact hasTy_upTo.mpr (hasTy_upTo.mp h)
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
  | strLess v c =>
    obtain ⟨a, l, off, hl, hoff, _, hva⟩ := hasTy_str.mp hv
    exact hasTy_str.mpr ⟨a, l, off, hl, hoff, fun h => absurd rfl h, hva⟩
  | codeMap v pre f =>
    rw [hasTy_code] at hv ⊢
    exact fun x => hv (f x)
  | rangeIn lo hi lo' hi' h => exact hasTy_range.mpr (h (hasTy_range.mp hv))

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
    held := h.held
    complete := h.complete }

/-- A state well typed at a step count is well typed at every smaller one. -/
theorem WellTyped.mono {m : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (hle : m ≤ n) : WellTyped fetch sys Ψ m Γ s :=
  Matches.imp h (fun _ _ hv => hv.mono hle)

end TypedAsm.U
