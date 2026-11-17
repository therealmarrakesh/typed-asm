import TypedAsm.U.Range
import TypedAsm.U.Fresh
import TypedAsm.U.Entail
import TypedAsm.U.RegardS

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
  | .range _ _ => Follows.refl _ _

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

/-- The ranges a comparison leaves the values it compares: of each, that it
lies in the range. -/
def CmpT.rangeFacts (p : CmpT) (b : Bool) : List (Val × TyS) :=
  [p.a, p.b].filterMap fun o =>
    match o with
    | .val v => (p.range b v).map fun R => (v, .range R.lo R.hi)
    | _ => none

theorem CmpT.rangeFacts_hasTy {ρ : Env} {p : CmpT} {b : Bool} (hp : p.den ρ = b)
    {f : Val × TyS} (hf : f ∈ p.rangeFacts b) (Ψ' : MemTy) (n : Nat) :
    HasTy fetch sys Ψ' n (f.2.den ρ) (f.1.den ρ) := by
  obtain ⟨o, _, ho⟩ := List.mem_filterMap.mp hf
  cases o with
  | val v =>
    simp only at ho
    cases hr : p.range b v with
    | none => rw [hr] at ho; cases ho
    | some R =>
      rw [hr] at ho
      cases ho
      exact hasTy_range.mpr (CmpT.range_sound hr hp)
  | imm i => cases ho
  | zero => cases ho

/-- **A context, knowing what a comparison teaches**: the range each value
compared is left in; and of each value, less what it is then known not to
be. -/
def CtxS.learn (p : CmpT) (b : Bool) (Γ : CtxS) : CtxS :=
  { Γ with known := p.rangeFacts b ++ Γ.known.map fun f =>
      (f.1, f.2.strip (p.leaves b f.1 .nonZero) (p.leaves b f.1 .noErr)) }

/-- **Where the comparison is as said, the context may be regarded as the
one that has learnt it.** -/
theorem CtxS.learn_regards {ρ : Env} {p : CmpT} {b : Bool} (Γ : CtxS) (hp : p.den ρ = b) :
    Regards fetch sys Ψ (Γ.den ρ) ((Γ.learn p b).den ρ) := by
  refine Regards.parts (E := []) (F := (Γ.den ρ).held) (L := []) rfl rfl ?_ rfl rfl
    (fun _ hx => nomatch hx) .nil (fun i b hb => by simp at hb)
  intro f hf Ψ' n hg
  obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hf
  rcases List.mem_append.mp hg' with hr | hs
  · exact CmpT.rangeFacts_hasTy hp hr Ψ' n
  · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hs
    exact TyS.strip_follows ρ (fun h => Range.nonZero_has (CmpT.leaves_has h hp))
      (fun h => Range.noErr_has (CmpT.leaves_has h hp)) g₀.2 Ψ' n
      (hg (g₀.1.den ρ, g₀.2.den ρ) (List.mem_map.mpr ⟨g₀, hg₀, rfl⟩))

/-- **The context on one side of a conditional jump**: knowing what the
condition's being so, or not, teaches, where the flags say what comparison
the condition comes to. -/
def CtxS.side (Γ : CtxS) (c : Cond) (b : Bool) : CtxS :=
  match Γ.flags.says c with
  | some p => Γ.learn p b
  | none => Γ

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

/-! ## Contexts that nothing matches -/

/-- Whether two ranges have no value in common. -/
def Range.disjoint (r s : Range) : Bool :=
  decide (r.hi - r.lo < s.lo - r.lo) && decide (s.hi - s.lo < r.lo - s.lo)

theorem Range.disjoint_has {r s : Range} (h : r.disjoint s = true) {v : BitVec 64}
    (hr : r.has v) (hs : s.has v) : False := by
  obtain ⟨rl, rh⟩ := r
  obtain ⟨sl, sh⟩ := s
  simp only [Range.disjoint, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Range.has] at hr hs
  bv_omega

/-- Whether a context knows of a value two ranges with nothing in common,
or of a number a range it is not in: no state matches it. -/
def CtxS.impossible (Γ : CtxS) : Bool :=
  Γ.known.any fun f =>
    match f.2 with
    | .range lo hi =>
      (match f.1.lit? with
       | some x => !decide (x - lo ≤ hi - lo)
       | none => false) ||
      Γ.known.any fun g =>
        g.1.same f.1 &&
          (match g.2 with
           | .range lo' hi' => Range.disjoint ⟨lo, hi⟩ ⟨lo', hi'⟩
           | _ => false)
    | _ => false

theorem CtxS.impossible_sound {ρ : Env} {Γ : CtxS} (h : Γ.impossible = true) (Ψ' : MemTy)
    (n : Nat) (s : State) : ¬ WellTyped fetch sys Ψ' n (Γ.den ρ) s := by
  intro hw
  simp only [CtxS.impossible, List.any_eq_true] at h
  obtain ⟨f, hf, hfr⟩ := h
  have hfT := hw.known (f.1.den ρ, f.2.den ρ) (List.mem_map.mpr ⟨f, hf, rfl⟩)
  cases hτ : f.2 with
  | range lo hi =>
    rw [hτ] at hfr hfT
    have hfv : f.1.den ρ - lo ≤ hi - lo := hasTy_range.mp hfT
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at hfr
    rcases hfr with hlit | ⟨g, hg, hsame, hgr⟩
    · cases hl : f.1.lit? with
      | none => rw [hl] at hlit; cases hlit
      | some x =>
        rw [hl] at hlit
        rw [Val.lit?_den hl] at hfv
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hlit
        exact hlit hfv
    · have hgT := hw.known (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hg, rfl⟩)
      cases hσ : g.2 with
      | range lo' hi' =>
        rw [hσ] at hgr hgT
        have hgv : g.1.den ρ - lo' ≤ hi' - lo' := hasTy_range.mp hgT
        rw [Val.same_den ρ hsame] at hgv
        exact Range.disjoint_has (r := ⟨lo, hi⟩) (s := ⟨lo', hi'⟩) hgr hfv hgv
      | _ => rw [hσ] at hgr; cases hgr
  | _ => rw [hτ] at hfr; cases hfr

end TypedAsm.U
