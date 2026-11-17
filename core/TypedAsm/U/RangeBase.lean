import TypedAsm.U.Term

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

def Bin.bound : Bin → Range
  | .add => .all
  | .shift _ w | .imul w => w.range

theorem Bin.bound_has (o : Bin) (a b : BitVec 64) : o.bound.has (o.eval a b) := by
  cases o with
  | add => exact Range.all_has _
  | shift op w => exact wide_has w _
  | imul w => exact wide_has w _

def FOp.bound : FOp → Range
  | .alu _ w | .cmov _ w => w.range
  | .setcc _ => .all
  | .condByte _ => ⟨0, 1⟩

theorem FOp.bound_has (o : FOp) (fl : Flags) (a b : BitVec 64) : o.bound.has (o.eval fl a b) := by
  cases o with
  | alu op w => exact wide_has w _
  | cmov c w => exact wide_has w _
  | setcc c => exact Range.all_has _
  | condByte c =>
    show (BitVec.setWidth 64 (condBit c fl)) - 0 ≤ 1#64 - 0
    unfold condBit
    split <;> decide

/-- **The range a value lies in, by the operator that gave it.** -/
def Val.bound : Val → Range
  | .lit v => ⟨v, v⟩
  | .un o _ => o.bound
  | .bin o _ _ => o.bound
  | .fop o _ _ _ => o.bound
  | _ => .all

theorem Val.bound_has (ρ : Env) (v : Val) : v.bound.has (v.den ρ) := by
  cases v with
  | lit v => simp only [Val.bound, Range.has, Val.den, BitVec.sub_self, BitVec.le_refl]
  | un o a => exact o.bound_has _
  | bin o a b => exact o.bound_has _ _
  | fop o fl a b => exact o.bound_has _ _ _
  | _ => exact Range.all_has _

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
