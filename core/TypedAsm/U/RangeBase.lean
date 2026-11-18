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

/-- The most a value of a range can be, as a number without sign. -/
def Range.top (r : Range) : BitVec 64 := if r.lo ≤ r.hi then r.hi else -1

theorem Range.le_top {r : Range} {v : BitVec 64} (h : r.has v) : v ≤ r.top := by
  obtain ⟨lo, hi⟩ := r
  simp only [Range.has] at h
  simp only [Range.top]
  split <;> bv_omega

/-- **What both of two values have set is no more than either**, nor than
the width it is taken at holds. -/
theorem and_le (w : Width) (a b : BitVec 64) :
    wide (a.setWidth w.bits &&& b.setWidth w.bits) ≤ a ∧
      wide (a.setWidth w.bits &&& b.setWidth w.bits) ≤ b ∧
      wide (a.setWidth w.bits &&& b.setWidth w.bits) ≤ w.range.top := by
  have ha : (a.setWidth w.bits).toNat ≤ a.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _
  have hb : (b.setWidth w.bits).toNat ≤ b.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _
  have hl : (a.setWidth w.bits &&& b.setWidth w.bits).toNat ≤ (a.setWidth w.bits).toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_left
  have hr : (a.setWidth w.bits &&& b.setWidth w.bits).toNat ≤ (b.setWidth w.bits).toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  have hw : (wide (a.setWidth w.bits &&& b.setWidth w.bits)).toNat
      = (a.setWidth w.bits &&& b.setWidth w.bits).toNat := by
    cases w <;> simp only [wide, BitVec.toNat_setWidth, Width.bits] <;> omega
  refine ⟨?_, ?_, Range.le_top (wide_has w _)⟩ <;> rw [BitVec.le_def, hw] <;> omega

/-- The lesser of two values, as numbers without sign. -/
def least (a b : BitVec 64) : BitVec 64 := if a ≤ b then a else b

/-- **The range a value lies in, by the operator that gave it**: and where
it is what two values both have set, no more than either can be. So a value
masked is at most the mask. -/
def Val.bound : Val → Range
  | .lit v => ⟨v, v⟩
  | .un o _ => o.bound
  | .bin o _ _ => o.bound
  | .fop (.alu .and w) _ a b => ⟨0, least (least a.bound.top b.bound.top) w.range.top⟩
  | .fop o _ _ _ => o.bound
  | _ => .all

theorem Val.bound_has (ρ : Env) : (v : Val) → v.bound.has (v.den ρ)
  | .lit v => by simp only [Val.bound, Range.has, Val.den, BitVec.sub_self, BitVec.le_refl]
  | .un o a => o.bound_has _
  | .bin o a b => o.bound_has _ _
  | .fop (.alu .and w) fl a b => by
    have ha := Range.le_top (Val.bound_has ρ a)
    have hb := Range.le_top (Val.bound_has ρ b)
    obtain ⟨h1, h2, h3⟩ := and_le w (a.den ρ) (b.den ρ)
    show (wide (BitVec.setWidth w.bits (a.den ρ) &&& BitVec.setWidth w.bits (b.den ρ))) - 0
      ≤ least (least a.bound.top b.bound.top) w.range.top - 0
    simp only [least]
    split <;> split <;> bv_omega
  | .fop (.alu .add w) fl a b => FOp.bound_has _ _ _ _
  | .fop (.alu .or w) fl a b => FOp.bound_has _ _ _ _
  | .fop (.alu .adc w) fl a b => FOp.bound_has _ _ _ _
  | .fop (.alu .sbb w) fl a b => FOp.bound_has _ _ _ _
  | .fop (.alu .sub w) fl a b => FOp.bound_has _ _ _ _
  | .fop (.alu .xor w) fl a b => FOp.bound_has _ _ _ _
  | .fop (.alu .cmp w) fl a b => FOp.bound_has _ _ _ _
  | .fop (.cmov _ _) fl a b => FOp.bound_has _ _ _ _
  | .fop (.setcc _) fl a b => FOp.bound_has _ _ _ _
  | .fop (.condByte _) fl a b => FOp.bound_has _ _ _ _
  | .var _ | .bvar _ _ | .slot _ | .tri _ _ _ _ | .app _ _ _ => Range.all_has _

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
