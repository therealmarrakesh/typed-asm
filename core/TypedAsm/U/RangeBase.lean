import TypedAsm.U.Ival

/-!
# Ranges, and the range an operator's result lies in

A range is the values from one number round to another, going up and
wrapping. What an operator gives lies in a range that can be read off the
operator: a result at 32 bits is below two to the thirty-second, a byte
widened is below 256, one or nought is one or nought. An operator that only
cuts a value to a width does nothing to a value already in its range.
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

/-- Every value. -/
def Range.all : Range := ⟨0, -1⟩

theorem Range.all_has (v : BitVec 64) : Range.all.has v := by
  simp only [Range.has, Range.all]
  bv_omega

/-- The values a register written at a width may hold. -/
def _root_.TypedAsm.Width.range : Width → Range
  | .w32 => ⟨0, 0xffffffff⟩
  | .w64 => .all

theorem wide_has (w : Width) (r : BitVec w.bits) : w.range.has (wide r) := by
  cases w with
  | w64 => exact Range.all_has _
  | w32 =>
    have h : r.toNat < 2 ^ 32 := r.isLt
    show (BitVec.setWidth 64 r) - 0 ≤ 0xffffffff#64 - 0
    bv_omega

def Un.bound : Un → Range
  | .neg w | .not w | .popcnt w | .bswap w | .signFill w | .trunc w | .sx w _ => w.range
  | .zx _ .w8 => ⟨0, 0xff⟩
  | .zx _ .w16 => ⟨0, 0xffff⟩
  | .low8 => ⟨0, 0xff⟩
  | .low16 => ⟨0, 0xffff⟩
  | .sxd | .shl _ => .all

theorem Un.bound_has (o : Un) (a : BitVec 64) : o.bound.has (o.eval a) := by
  cases o with
  | neg w => exact wide_has w _
  | not w => exact wide_has w _
  | popcnt w => exact wide_has w _
  | bswap w => exact wide_has w _
  | signFill w => exact wide_has w _
  | trunc w => exact wide_has w _
  | zx w sw =>
    cases w <;> cases sw <;>
      simp only [Un.bound, Un.eval, wide, Range.has, Width.bits, NarrowW.bits] <;> bv_omega
  | sx w sw => exact wide_has w _
  | low8 =>
    show (BitVec.setWidth 64 (BitVec.setWidth 8 a)) - 0 ≤ 0xff#64 - 0
    bv_omega
  | low16 =>
    show (BitVec.setWidth 64 (BitVec.setWidth 16 a)) - 0 ≤ 0xffff#64 - 0
    bv_omega
  | sxd => exact Range.all_has _
  | shl k => exact Range.all_has _

/-- A range of numbers without sign, as a range of values. -/
def Ival.toRange (I : Ival) : Range :=
  if I.lo ≤ I.hi ∧ I.hi < 2 ^ 64 then ⟨BitVec.ofNat 64 I.lo, BitVec.ofNat 64 I.hi⟩ else .all

theorem Ival.toRange_has {I : Ival} {v : BitVec 64} (h : I.has v.toNat) : I.toRange.has v := by
  unfold Ival.toRange
  split
  · next hc =>
    obtain ⟨h1, h2⟩ := h
    have hlo : I.lo < 2 ^ 64 := by omega
    simp only [Range.has, BitVec.le_def, BitVec.toNat_sub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hc.2]
    have := v.isLt
    omega
  · exact Range.all_has _

/-- **The range a value lies in, by what it is made of**: what each operator
does to the range of its operands (`Val.ival`), as a range of values. -/
def Val.bound (v : Val) : Range := (v.ival []).toRange

theorem Val.bound_has (ρ : Env) (v : Val) : v.bound.has (v.den ρ) :=
  Ival.toRange_has (Val.ival_has (rangesHold_nil ρ) v)

/-- The same, by what is known besides of the terms it is made of. -/
def Val.boundIn (K : List (Val × TyS)) (v : Val) : Range := (v.ival K).toRange

theorem Val.boundIn_has {ρ : Env} {K : List (Val × TyS)} (hK : RangesHold ρ K) (v : Val) :
    (v.boundIn K).has (v.den ρ) :=
  Ival.toRange_has (Val.ival_has hK v)

/-- Whether an operator only cuts a value down to its own range. -/
def Un.cuts : Un → Bool
  | .trunc _ | .zx _ _ | .low8 | .low16 => true
  | _ => false

/-- **An operator that only cuts does nothing to a value already in its
range.** -/
theorem Un.cut_eval {o : Un} (hc : o.cuts = true) {v : BitVec 64} (h : o.bound.has v) :
    o.eval v = v := by
  cases o with
  | trunc w =>
    cases w <;> simp only [Un.bound, Width.range, Range.all, Range.has] at h <;>
      simp only [Un.eval, wide, Width.bits] <;> bv_omega
  | zx w sw =>
    cases w <;> cases sw <;> simp only [Un.bound, Range.has] at h <;>
      simp only [Un.eval, wide, Width.bits, NarrowW.bits] <;> bv_omega
  | low8 =>
    simp only [Un.bound, Range.has] at h
    simp only [Un.eval]
    bv_omega
  | low16 =>
    simp only [Un.bound, Range.has] at h
    simp only [Un.eval]
    bv_omega
  | _ => cases hc

end TypedAsm.U
