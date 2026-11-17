import TypedAsm.U.Range
import TypedAsm.U.Fresh
import TypedAsm.U.Entail

/-!
# What a comparison teaches

Where a comparison is known to be so, or not so, each value it leaves
clear of zero is not null, and each it leaves clear of the error numbers is
not one. The context that knows this much more is one the context before
may be regarded as.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- Every value but zero. -/
def Range.nonZero : Range := ⟨1, -1⟩

/-- Every value but the error numbers. -/
def Range.noErr : Range := ⟨0, -4096⟩

theorem Range.nonZero_has {v : BitVec 64} (h : Range.nonZero.has v) : v ≠ 0 := by
  simp only [Range.has, Range.nonZero] at h
  bv_omega

theorem Range.noErr_has {v : BitVec 64} (h : Range.noErr.has v) : ¬ SysErr v := by
  simp only [Range.has, Range.noErr] at h
  unfold SysErr
  bv_omega

/-- What is known of a value, less what it is known not to be. -/
def TyS.strip (nz ne : Bool) : TyS → TyS
  | .nullable τ => if nz then τ.strip nz ne else .nullable (τ.strip nz ne)
  | .orErr τ => if ne then τ.strip nz ne else .orErr (τ.strip nz ne)
  | τ => τ

theorem TyS.strip_follows (ρ : Env) {nz ne : Bool} {v : BitVec 64} (hnz : nz = true → v ≠ 0)
    (hne : ne = true → ¬ SysErr v) :
    (τ : TyS) → Follows fetch sys v (τ.den ρ) ((τ.strip nz ne).den ρ)
  | .nullable τ => by
    have ih := TyS.strip_follows ρ hnz hne τ
    intro Ψ n h
    have h' := (hasTy_nullable (τ := τ.den ρ)).mp h
    unfold TyS.strip
    split
    · next hz => exact ih Ψ n (h'.resolve_left (hnz hz))
    · exact (hasTy_nullable (τ := (τ.strip nz ne).den ρ)).mpr (h'.imp id (ih Ψ n))
  | .orErr τ => by
    have ih := TyS.strip_follows ρ hnz hne τ
    intro Ψ n h
    have h' := (hasTy_orErr (τ := τ.den ρ)).mp h
    unfold TyS.strip
    split
    · next hz => exact ih Ψ n (h'.resolve_left (hne hz))
    · exact (hasTy_orErr (τ := (τ.strip nz ne).den ρ)).mpr (h'.imp id (ih Ψ n))
  | .any => Follows.refl _ _
  | .ptr _ _ _ => Follows.refl _ _
  | .ref _ _ _ => Follows.refl _ _
  | .str _ => Follows.refl _ _
  | .atom _ => Follows.refl _ _
  | .code .. => Follows.refl _ _

/-- Whether the values a comparison leaves a value lie within a range. -/
def CmpT.leaves (p : CmpT) (b : Bool) (v : Val) (R : Range) : Bool :=
  match p.range b v with
  | some r => r.within R
  | none => false

theorem CmpT.leaves_has {ρ : Env} {p : CmpT} {b : Bool} {v : Val} {R : Range}
    (h : p.leaves b v R = true) (hp : p.den ρ = b) : R.has (v.den ρ) := by
  unfold CmpT.leaves at h
  cases hr : p.range b v with
  | none => rw [hr] at h; cases h
  | some r => rw [hr] at h; exact Range.within_has h (CmpT.range_sound hr hp)

/-- **A context, knowing what a comparison teaches.** -/
def CtxS.learn (p : CmpT) (b : Bool) (Γ : CtxS) : CtxS :=
  { Γ with known := Γ.known.map fun f =>
      (f.1, f.2.strip (p.leaves b f.1 .nonZero) (p.leaves b f.1 .noErr)) }

/-- **Where the comparison is as said, the context may be regarded as the
one that has learnt it.** -/
theorem CtxS.learn_regards {ρ : Env} {p : CmpT} {b : Bool} (Γ : CtxS) (hp : p.den ρ = b) :
    Regards fetch sys Ψ (Γ.den ρ) ((Γ.learn p b).den ρ) := by
  refine Regards.follows (Γ := Γ.den ρ) _ ?_
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  exact ⟨g₀.2.den ρ, List.mem_map.mpr ⟨g₀, hg₀, rfl⟩,
    TyS.strip_follows ρ (fun h => Range.nonZero_has (CmpT.leaves_has h hp))
      (fun h => Range.noErr_has (CmpT.leaves_has h hp)) g₀.2⟩

theorem TyS.strip_under (k : Nat) (nz ne : Bool) :
    (τ : TyS) → τ.under k = true → (τ.strip nz ne).under k = true
  | .nullable τ, h => by
    have ih := TyS.strip_under k nz ne τ (by simpa only [TyS.under] using h)
    unfold TyS.strip
    split
    · exact ih
    · simpa only [TyS.under] using ih
  | .orErr τ, h => by
    have ih := TyS.strip_under k nz ne τ (by simpa only [TyS.under] using h)
    unfold TyS.strip
    split
    · exact ih
    · simpa only [TyS.under] using ih
  | .any, h => h
  | .ptr _ _ _, h => h
  | .ref _ _ _, h => h
  | .str _, h => h
  | .atom _, h => h
  | .code .., h => h

theorem CtxS.learn_under (p : CmpT) (b : Bool) (Γ : CtxS) (k : Nat) (h : Γ.under k = true) :
    (Γ.learn p b).under k = true := by
  simp only [CtxS.under, CtxS.learn, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun f hf => ?_⟩
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact ⟨(h.2 g hg).1, TyS.strip_under k _ _ g.2 (h.2 g hg).2⟩

/-- **The context on one side of a conditional jump**: knowing what the
condition's being so, or not, teaches, where the flags say what comparison
the condition comes to. -/
def CtxS.side (Γ : CtxS) (c : Cond) (b : Bool) : CtxS :=
  match Γ.flags.says c with
  | some p => Γ.learn p b
  | none => Γ

theorem CtxS.side_under (Γ : CtxS) (c : Cond) (b : Bool) (k : Nat) (h : Γ.under k = true) :
    (Γ.side c b).under k = true := by
  unfold CtxS.side
  split
  · exact CtxS.learn_under _ _ _ _ h
  · exact h

theorem CtxS.side_regards {ρ : Env} (Γ : CtxS) {c : Cond} {b : Bool}
    (h : c.eval (Γ.flags.den ρ) = some b) :
    Regards fetch sys Ψ (Γ.den ρ) ((Γ.side c b).den ρ) := by
  unfold CtxS.side
  cases hs : Γ.flags.says c with
  | none => exact Regards.refl _
  | some p =>
    have := FlagsT.says_den ρ hs
    rw [h] at this
    exact CtxS.learn_regards Γ (Option.some.inj this).symm

end TypedAsm.U
