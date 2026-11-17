import TypedAsm.U.Says
import TypedAsm.U.Simp

/-!
# The values a comparison leaves

A comparison of a value with a number, being so or not so, leaves the value
within a range: from one number round to another, going up and wrapping.
Whether one range lies within another is decided. What is wanted of a value,
that it is not null or not an error number, is such a range too.
-/

namespace TypedAsm.U

open TypedAsm

/-- The values from `lo` round to `hi`, going up and wrapping. -/
structure Range where
  lo : BitVec 64
  hi : BitVec 64
  deriving DecidableEq

def Range.has (r : Range) (v : BitVec 64) : Prop := v - r.lo ≤ r.hi - r.lo

/-- Whether every value of the first is one of the second. -/
def Range.within (r s : Range) : Bool :=
  r.lo - s.lo ≤ r.hi - s.lo && r.hi - s.lo ≤ s.hi - s.lo

theorem Range.within_has {r s : Range} (h : r.within s = true) {v : BitVec 64} (hv : r.has v) :
    s.has v := by
  obtain ⟨rl, rh⟩ := r
  obtain ⟨sl, sh⟩ := s
  simp only [Range.within, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Range.has] at hv ⊢
  bv_omega

/-- Less with sign is below without, once both are moved up by half the range. -/
theorem slt64 (a b : BitVec 64) :
    a.slt b = (a + 0x8000000000000000#64).ult (b + 0x8000000000000000#64) := by
  rw [BitVec.slt_eq_ult, Bool.eq_iff_iff]
  simp only [BitVec.msb_eq_decide, BitVec.ult, decide_eq_true_eq]
  by_cases h1 : 2 ^ (64 - 1) ≤ a.toNat <;> by_cases h2 : 2 ^ (64 - 1) ≤ b.toNat <;>
    simp only [h1, h2, decide_true, decide_false, bne_self_eq_false, Bool.false_xor,
      Bool.true_xor, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      show (true != false) = true from rfl, show (false != true) = true from rfl] <;>
    bv_omega

/-- The values a comparison with a number leaves: of `v` against `k` where
`vLeft`, of `k` against `v` otherwise, the comparison being as `t` says. -/
def confine (r : Rel) (t vLeft : Bool) (k : BitVec 64) : Option Range :=
  match r, t, vLeft with
  | .eq, true, _ => some ⟨k, k⟩
  | .eq, false, _ => some ⟨k + 1, k - 1⟩
  | .ult, true, true => if k = 0 then none else some ⟨0, k - 1⟩
  | .ult, false, true => some ⟨k, -1⟩
  | .ult, true, false => if k = -1 then none else some ⟨k + 1, -1⟩
  | .ult, false, false => some ⟨0, k⟩
  | .slt, true, true => if k = BitVec.intMin 64 then none else some ⟨BitVec.intMin 64, k - 1⟩
  | .slt, false, true => some ⟨k, BitVec.intMax 64⟩
  | .slt, true, false => if k = BitVec.intMax 64 then none else some ⟨k + 1, BitVec.intMax 64⟩
  | .slt, false, false => some ⟨BitVec.intMin 64, k⟩
  | _, _, _ => none

theorem confine_sound {r : Rel} {t vLeft : Bool} {k v : BitVec 64} {R : Range}
    (h : confine r t vLeft k = some R)
    (hv : (if vLeft then r.eval v k else r.eval k v) = t) : R.has v := by
  cases r <;> cases t <;> cases vLeft <;> simp only [confine] at h <;>
    (try split at h) <;> cases h <;>
    simp only [Rel.eval, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
      slt64, BitVec.ult, decide_eq_true_eq, decide_eq_false_iff_not] at hv <;>
    simp only [Range.has, BitVec.intMin, BitVec.intMax] at * <;> bv_omega

/-- An operand that is a number, at the full width. -/
def OpT.lit64? : OpT → Option (BitVec 64)
  | .val v => v.lit?
  | .imm i => some (i.signExtend 64)
  | .zero => some 0

theorem OpT.lit64?_den {ρ : Env} {o : OpT} {k : BitVec 64} (h : o.lit64? = some k) :
    o.den ρ .w64 = k := by
  cases o with
  | val v =>
    show (v.den ρ).setWidth 64 = k
    rw [Val.lit?_den h, BitVec.setWidth_eq]
  | imm i => cases h; rfl
  | zero => cases h; rfl

theorem OpT.val_den (ρ : Env) (v : Val) : (OpT.val v).den ρ .w64 = v.den ρ :=
  BitVec.setWidth_eq _

/-- A comparison of a value with a number, either way round. -/
def cmpRange (r : Rel) (t : Bool) (x y : OpT) (v : Val) : Option Range :=
  if x = .val v then y.lit64?.bind (confine r t true)
  else if y = .val v then x.lit64?.bind (confine r t false)
  else none

theorem cmpRange_sound {ρ : Env} {r : Rel} {t : Bool} {x y : OpT} {v : Val} {R : Range}
    (h : cmpRange r t x y v = some R) (hv : r.eval (x.den ρ .w64) (y.den ρ .w64) = t) :
    R.has (v.den ρ) := by
  unfold cmpRange at h
  split at h
  · next hx =>
    subst hx
    cases hy : y.lit64? with
    | none => rw [hy] at h; cases h
    | some k =>
      rw [hy] at h
      rw [OpT.lit64?_den hy, OpT.val_den] at hv
      exact confine_sound h hv
  · split at h
    · next hy =>
      subst hy
      cases hx : x.lit64? with
      | none => rw [hx] at h; cases h
      | some k =>
        rw [hx] at h
        rw [OpT.lit64?_den hx, OpT.val_den] at hv
        exact confine_sound h hv
    · cases h

/-- The values a relation between two operands leaves a value, the relation
being as `t` says. A test of a value against itself is a comparison of it
with zero. -/
def relRange (r : Rel) (t : Bool) (x y : OpT) (v : Val) : Option Range :=
  match r with
  | .tstz => if x = .val v ∧ y = .val v then confine .eq t true 0 else none
  | .tstneg => if x = .val v ∧ y = .val v then confine .slt t true 0 else none
  | .tstpos => if x = .val v ∧ y = .val v then confine .slt t false 0 else none
  | r => cmpRange r t x y v

theorem relRange_sound {ρ : Env} {r : Rel} {t : Bool} {x y : OpT} {v : Val} {R : Range}
    (h : relRange r t x y v = some R) (hv : r.eval (x.den ρ .w64) (y.den ρ .w64) = t) :
    R.has (v.den ρ) := by
  have self : ∀ z : BitVec 64, z &&& z = z := fun _ => BitVec.and_self
  cases r with
  | eq => exact cmpRange_sound h hv
  | ult => exact cmpRange_sound h hv
  | slt => exact cmpRange_sound h hv
  | never => exact cmpRange_sound h hv
  | tstz =>
    simp only [relRange] at h
    split at h
    · next hxy =>
      obtain ⟨rfl, rfl⟩ := hxy
      rw [OpT.val_den] at hv
      refine confine_sound h ?_
      show (v.den ρ == 0) = t
      rw [← hv]; show _ = (v.den ρ &&& v.den ρ == 0); rw [self]
    · cases h
  | tstneg =>
    simp only [relRange] at h
    split at h
    · next hxy =>
      obtain ⟨rfl, rfl⟩ := hxy
      rw [OpT.val_den] at hv
      refine confine_sound h ?_
      show (v.den ρ).slt 0 = t
      rw [← hv]; show _ = (v.den ρ &&& v.den ρ).msb; rw [self]; exact BitVec.slt_zero_eq_msb
    · cases h
  | tstpos =>
    simp only [relRange] at h
    split at h
    · next hxy =>
      obtain ⟨rfl, rfl⟩ := hxy
      rw [OpT.val_den] at hv
      refine confine_sound h ?_
      show (0 : BitVec 64).slt (v.den ρ) = t
      rw [← hv]; show _ = (0 : BitVec 64).slt (v.den ρ &&& v.den ρ); rw [self]
    · cases h

/-- **The values a comparison leaves a value**, the comparison being as `b`
says. -/
def CmpT.range (p : CmpT) (b : Bool) (v : Val) : Option Range :=
  match p.w with
  | .w64 =>
    if p.form.swap then relRange p.form.rel (b != p.form.neg) p.b p.a v
    else relRange p.form.rel (b != p.form.neg) p.a p.b v
  | .w32 => none

theorem CmpT.range_sound {ρ : Env} {p : CmpT} {b : Bool} {v : Val} {R : Range}
    (h : p.range b v = some R) (hp : p.den ρ = b) : R.has (v.den ρ) := by
  obtain ⟨⟨neg, rel, swap⟩, w, x, y⟩ := p
  cases w with
  | w32 => cases h
  | w64 =>
    simp only [CmpT.range] at h
    have hp' : (if neg then !(if swap then rel.eval (y.den ρ .w64) (x.den ρ .w64)
        else rel.eval (x.den ρ .w64) (y.den ρ .w64))
        else (if swap then rel.eval (y.den ρ .w64) (x.den ρ .w64)
        else rel.eval (x.den ρ .w64) (y.den ρ .w64))) = b := hp
    cases swap
    · simp only [Bool.false_eq_true, ↓reduceIte] at h hp'
      refine relRange_sound h ?_
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp' <;> rw [← hp'] <;>
        cases rel.eval (x.den ρ .w64) (y.den ρ .w64) <;> rfl
    · simp only [↓reduceIte] at h hp'
      refine relRange_sound h ?_
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp' <;> rw [← hp'] <;>
        cases rel.eval (y.den ρ .w64) (x.den ρ .w64) <;> rfl

end TypedAsm.U
