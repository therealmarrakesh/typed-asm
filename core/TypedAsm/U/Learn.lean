import TypedAsm.U.Range
import TypedAsm.U.Bound
import TypedAsm.U.Text
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
  | .arr _ _ => Follows.refl _ _
  | .upTo _ _ => Follows.refl _ _

/-- Whether a context knows of a value a range that lies within a given
one. -/
def CtxS.knowsIn (Γ : CtxS) (v : Val) (R : Range) : Bool :=
  Γ.known.any fun g =>
    g.1.same v &&
      (match g.2 with
       | .range lo hi => Range.within ⟨lo, hi⟩ R
       | _ => false)

theorem CtxS.knowsIn_has {ρ : Env} {Γ : CtxS} {v : Val} {R : Range} (h : Γ.knowsIn v R = true)
    {Ψ' : MemTy} {n : Nat} (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    R.has (v.den ρ) := by
  simp only [CtxS.knowsIn, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨g, hgm, hsame, hin⟩ := h
  have hT := hg (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩)
  cases hτ : g.2 with
  | range lo hi =>
    rw [hτ] at hin hT
    rw [← Val.same_den ρ hsame]
    exact Range.within_has (r := ⟨lo, hi⟩) hin (hasTy_range.mp hT)
  | _ => rw [hτ] at hin; cases hin

/-- Whether a value is known to lie in a range: by the operator that gave
it, or by what the context knows of it. -/
def CtxS.fits (Γ : CtxS) (v : Val) (R : Range) : Bool := v.bound.within R || Γ.knowsIn v R

theorem CtxS.fits_has {ρ : Env} {Γ : CtxS} {v : Val} {R : Range} (h : Γ.fits v R = true)
    {Ψ' : MemTy} {n : Nat} (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    R.has (v.den ρ) := by
  unfold CtxS.fits at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Range.within_has h (Val.bound_has ρ v)
  · exact CtxS.knowsIn_has h hg

/-- What follows of the addresses one on from pointers to text: where a
pointer's byte is known not to be nought, the address one on is a pointer to
text; unless that is known already. -/
def CtxS.strNext (Γ : CtxS) : List (Val × TyS) :=
  Γ.known.filterMap fun f =>
    match f.2 with
    | .str c =>
      if Γ.fits c .nonZero &&
          !(Γ.known.any fun g => g.1.same (.add f.1 (.lit 1)) && g.2 == .str (.lit 0)) then
        some (.add f.1 (.lit 1), .str (.lit 0))
      else none
    | _ => none

/-- A thing known, made as sharp as the ranges known allow: looked into
only where it says a value may be null or an error number. -/
def CtxS.sharp (Γ : CtxS) (f : Val × TyS) : Val × TyS :=
  match f.2 with
  | .nullable _ => (f.1, f.2.strip (Γ.knowsIn f.1 .nonZero) (Γ.knowsIn f.1 .noErr))
  | .orErr _ => (f.1, f.2.strip (Γ.knowsIn f.1 .nonZero) (Γ.knowsIn f.1 .noErr))
  | _ => f

/-- **A context with each thing known made as sharp as the ranges it knows
allow**: what may be null and is known to lie clear of zero, is not null;
what may be an error number and is known to lie clear of them, is not one;
and past a byte of text known not to be nought there is text. Whenever a
range comes to be known, by a comparison or of what a call hands back, this
is done; so it does not matter in which order things were learnt. -/
def CtxS.sharpen (Γ : CtxS) : CtxS :=
  { Γ with known := Γ.strNext ++ Γ.known.map Γ.sharp }

theorem CtxS.sharpen_regards (ρ : Env) (Γ : CtxS) :
    Regards fetch sys Ψ (Γ.den ρ) (Γ.sharpen.den ρ) := by
  refine Regards.parts (E := []) (F := (Γ.den ρ).held) (L := []) rfl rfl ?_ rfl rfl
    (fun _ hx => nomatch hx) .nil (fun i b hb => by simp at hb)
  intro f hf Ψ' n hg
  obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hf
  rcases List.mem_append.mp hg' with hn | hs
  · obtain ⟨g₀, hg₀, hsome⟩ := List.mem_filterMap.mp hn
    cases hτ : g₀.2 with
    | str c =>
      rw [hτ] at hsome
      simp only at hsome
      split at hsome
      · next hc =>
        cases hsome
        rw [Bool.and_eq_true] at hc
        have hsrc := hg (g₀.1.den ρ, g₀.2.den ρ) (List.mem_map.mpr ⟨g₀, hg₀, rfl⟩)
        rw [hτ] at hsrc
        exact hasTy_str_succ hsrc (Range.nonZero_has (CtxS.fits_has hc.1 hg))
      · cases hsome
    | _ => rw [hτ] at hsome; cases hsome
  · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hs
    have hsrc := hg (g₀.1.den ρ, g₀.2.den ρ) (List.mem_map.mpr ⟨g₀, hg₀, rfl⟩)
    have key := TyS.strip_follows (fetch := fetch) (sys := sys) ρ
      (fun h => Range.nonZero_has (CtxS.knowsIn_has h hg))
      (fun h => Range.noErr_has (CtxS.knowsIn_has h hg)) g₀.2 Ψ' n hsrc
    unfold CtxS.sharp
    split
    · exact key
    · exact key
    · exact hsrc

/-- The ranges a comparison leaves the values it compares: of each, that it
lies in the range. -/
def CmpT.rangeFacts (p : CmpT) (b : Bool) : List (Val × TyS) :=
  [p.a, p.b].filterMap fun v => (p.range b v).map fun R => (v, .range R.lo R.hi)

theorem CmpT.rangeFacts_hasTy {ρ : Env} {p : CmpT} {b : Bool} (hp : p.den ρ = b)
    {f : Val × TyS} (hf : f ∈ p.rangeFacts b) (Ψ' : MemTy) (n : Nat) :
    HasTy fetch sys Ψ' n (f.2.den ρ) (f.1.den ρ) := by
  obtain ⟨v, _, ho⟩ := List.mem_filterMap.mp hf
  cases hr : p.range b v with
  | none => rw [hr] at ho; cases ho
  | some R =>
    rw [hr] at ho
    cases ho
    exact hasTy_range.mpr (CmpT.range_sound hr hp)

/-- What a comparison of two values for which is below teaches of the one
against the other: that the one is less, or that the other is at most it. -/
def CmpT.orderFacts (p : CmpT) (b : Bool) : List (Val × TyS) :=
  match p.w, p.form.rel with
  | .w64, .ult =>
    if b != p.form.neg then
      [(if p.form.swap then p.b else p.a, .upTo (if p.form.swap then p.a else p.b) true)]
    else
      [(if p.form.swap then p.a else p.b, .upTo (if p.form.swap then p.b else p.a) false)]
  | _, _ => []

theorem CmpT.orderFacts_hasTy {ρ : Env} {p : CmpT} {b : Bool} (hp : p.den ρ = b)
    {f : Val × TyS} (hf : f ∈ p.orderFacts b) (Ψ' : MemTy) (n : Nat) :
    HasTy fetch sys Ψ' n (f.2.den ρ) (f.1.den ρ) := by
  obtain ⟨⟨neg, rel, swap⟩, w, x, y⟩ := p
  cases w with
  | w32 => cases hf
  | w64 =>
    cases rel with
    | ult =>
      simp only [CmpT.den, Form.eval, Rel.eval, Val.denW, Width.bits, BitVec.setWidth_eq] at hp
      simp only [CmpT.orderFacts] at hf
      cases neg <;> cases swap <;> cases b <;>
        simp only [bne_iff_ne, ne_eq, Bool.false_eq_true, not_false_eq_true, not_true_eq_false,
          ↓reduceIte, List.mem_singleton, Bool.true_eq_false, Bool.not_eq_true',
          Bool.not_eq_false'] at hf hp <;>
        subst hf <;>
        refine hasTy_upTo.mpr ?_ <;>
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.ult_eq_decide, decide_eq_true_eq,
          decide_eq_false_iff_not] at hp ⊢ <;>
        first
          | exact hp
          | exact BitVec.le_def.mpr (Nat.le_of_not_lt hp)
    | _ => cases hf

/-- What a relation says of a value against itself, where that is the same
whatever the value. -/
def Rel.self : Rel → Option Bool
  | .eq => some true
  | .ult => some false
  | .slt => some false
  | .never => some false
  | _ => none

theorem Rel.self_eval {n : Nat} {r : Rel} {c : Bool} (h : r.self = some c) (x : BitVec n) :
    r.eval x x = c := by
  cases r <;> cases h
  · exact beq_self_eq_true x
  · simp [Rel.eval, BitVec.ult]
  · simp [Rel.eval, BitVec.slt]
  · rfl

/-- Whether a comparison comes out one way whatever its values are, and
which: the two are the same value, and the relation says one thing of a
value against itself; or it asks whether they are equal, and they differ by
a number written out that is not nought. -/
def CmpT.fixed (p : CmpT) : Option Bool :=
  if p.a.same p.b then p.form.rel.self.map (· != p.form.neg)
  else
    match p.w, p.form.rel, (p.a.less p.b).lin with
    | .w64, .eq, ⟨[], k⟩ => if k = 0 then none else some p.form.neg
    | _, _, _ => none

theorem CmpT.fixed_den {ρ : Env} {p : CmpT} {c : Bool} (h : p.fixed = some c) : p.den ρ = c := by
  obtain ⟨⟨neg, rel, swap⟩, w, a, b⟩ := p
  unfold CmpT.fixed at h
  simp only at h
  split at h
  · next hs =>
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    have e : a.denW ρ w = b.denW ρ w := by
      show (a.den ρ).setWidth _ = (b.den ρ).setWidth _
      rw [Val.same_den ρ hs]
    show Form.eval ⟨neg, rel, swap⟩ (a.denW ρ w) (b.denW ρ w) = _
    rw [e]
    simp only [Form.eval, ite_self, Rel.self_eval hr]
    cases neg <;> cases r <;> rfl
  · split at h
    · next k hl =>
      split at h
      · cases h
      · next hk =>
        cases h
        have hd : a.den ρ - b.den ρ = k := by
          rw [← Val.less_den, ← Val.lin_den ρ (a.less b), hl]
          simp [Lin.den, multDen]
        have hne : a.den ρ ≠ b.den ρ := fun e => hk (by rw [← hd, e, BitVec.sub_self]; rfl)
        show Form.eval ⟨c, .eq, swap⟩ ((a.den ρ).setWidth 64) ((b.den ρ).setWidth 64) = c
        rw [BitVec.setWidth_eq, BitVec.setWidth_eq]
        simp only [Form.eval, Rel.eval]
        have h1 : (a.den ρ == b.den ρ) = false := beq_eq_false_iff_ne.mpr hne
        have h2 : (b.den ρ == a.den ρ) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
        cases c <;> cases swap <;> simp [h1, h2]
    · cases h

/-- What a comparison teaches where it comes out as it cannot: something
that is so of no value. -/
def CmpT.fixedFacts (p : CmpT) (b : Bool) : List (Val × TyS) :=
  match p.fixed with
  | some c => if b = c then [] else [(.lit 0, .range 1 1)]
  | none => []

theorem CmpT.fixedFacts_hasTy {ρ : Env} {p : CmpT} {b : Bool} (hp : p.den ρ = b)
    {f : Val × TyS} (hf : f ∈ p.fixedFacts b) (Ψ' : MemTy) (n : Nat) :
    HasTy fetch sys Ψ' n (f.2.den ρ) (f.1.den ρ) := by
  unfold CmpT.fixedFacts at hf
  split at hf
  · next c hc =>
    split at hf
    · cases hf
    · next hne => exact absurd ((CmpT.fixed_den hc).symm.trans hp).symm hne
  · cases hf

/-- **A comparison at 32 bits, as the comparison at 64**, where both values
are known to fit: it says the same of them. -/
def CmpT.widen (Γ : CtxS) (p : CmpT) : CmpT :=
  match p.w with
  | .w64 => p
  | .w32 =>
    if Γ.fits p.a p.form.rel.fitRange && Γ.fits p.b p.form.rel.fitRange then { p with w := .w64 }
    else p

theorem CmpT.widen_den {ρ : Env} {Γ : CtxS} (p : CmpT) {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    (p.widen Γ).den ρ = p.den ρ := by
  obtain ⟨f, w, a, b⟩ := p
  cases w with
  | w64 => rfl
  | w32 =>
    simp only [CmpT.widen]
    split
    · next h =>
      rw [Bool.and_eq_true] at h
      show f.eval (BitVec.setWidth 64 (a.den ρ)) (BitVec.setWidth 64 (b.den ρ))
        = f.eval (BitVec.setWidth 32 (a.den ρ)) (BitVec.setWidth 32 (b.den ρ))
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq]
      exact (Form.eval_low (CtxS.fits_has h.1 hg) (CtxS.fits_has h.2 hg)).symm
    · rfl

/-- Whether a thing learnt is news: not that a number written out lies in a
range it does lie in, and not known already. -/
def CtxS.news (Γ : CtxS) (f : Val × TyS) : Bool :=
  (match f.1.lit?, f.2 with
   | some x, .range lo hi => !decide (x - lo ≤ hi - lo)
   | _, _ => true) && !Γ.known.contains f

/-- **A context, knowing what a comparison teaches**: the range each value
compared is left in, which of the two is the less where that is what was
asked, that it cannot be where it comes out the other way than it must, and
everything known made as sharp as that allows. -/
def CtxS.learn (p : CmpT) (b : Bool) (Γ : CtxS) : CtxS :=
  (Γ.addKnown (((p.widen Γ).rangeFacts b ++ (p.widen Γ).orderFacts b ++
    (p.widen Γ).fixedFacts b).filter Γ.news)).sharpen

/-- **Where the comparison is as said, the context may be regarded as the
one that has learnt it.** -/
theorem CtxS.learn_regards {ρ : Env} {p : CmpT} {b : Bool} (Γ : CtxS) (hp : p.den ρ = b) :
    Regards fetch sys Ψ (Γ.den ρ) ((Γ.learn p b).den ρ) := by
  refine Regards.trans ?_ (CtxS.sharpen_regards ρ _)
  refine Regards.parts (E := []) (F := (Γ.den ρ).held) (L := []) rfl rfl ?_ rfl rfl
    (fun _ hx => nomatch hx) .nil (fun i b hb => by simp at hb)
  intro f hf Ψ' n hg
  obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hf
  rcases List.mem_append.mp hg' with hr | hs
  · rcases List.mem_append.mp (List.mem_filter.mp hr).1 with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact CmpT.rangeFacts_hasTy ((CmpT.widen_den p hg).trans hp) hr Ψ' n
      · exact CmpT.orderFacts_hasTy ((CmpT.widen_den p hg).trans hp) hr Ψ' n
    · exact CmpT.fixedFacts_hasTy ((CmpT.widen_den p hg).trans hp) hr Ψ' n
  · exact hg _ (List.mem_map.mpr ⟨g, hs, rfl⟩)

/-- **The context on one side of a choice made on a condition**: knowing
what the condition's being so, or not, teaches, where the flags it is a
condition on say what comparison it comes to. -/
def CtxS.side (Γ : CtxS) (fl : FlagsT) (c : Cond) (b : Bool) : CtxS :=
  match fl.says c with
  | some p => Γ.learn p b
  | none => Γ

theorem CtxS.side_regards {ρ : Env} (Γ : CtxS) {fl : FlagsT} {c : Cond} {b : Bool}
    (h : c.eval (fl.den ρ) = some b) :
    Regards fetch sys Ψ (Γ.den ρ) ((Γ.side fl c b).den ρ) := by
  unfold CtxS.side
  cases hs : fl.says c with
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
