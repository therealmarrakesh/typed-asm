import TypedAsm.U.Range

/-!
# The range an operator's result lies in

What an operator gives lies in a range that can be read off the operator:
a result at 32 bits is below two to the thirty-second, a byte widened is
below 256, one or nought is one or nought. And a comparison at 32 bits, of
two values that fit, says of them what the comparison at 64 bits says: so
what a 32-bit comparison teaches is what the 64-bit one does.
-/

namespace TypedAsm.U

open TypedAsm

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
  | .neg w | .not w | .popcnt w | .bswap w | .signFill w | .trunc w | .zx w _ | .sx w _ => w.range
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
  | zx w sw => exact wide_has w _
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

/-! ## A comparison at 32 bits, of values that fit -/

/-- The range two values must lie in for a relation between their low
halves to be the relation between them: below two to the thirty-second;
and, where the relation turns on the sign, below two to the thirty-first. -/
def Rel.fitRange : Rel → Range
  | .slt | .tstneg | .tstpos => ⟨0, 0x7fffffff⟩
  | _ => ⟨0, 0xffffffff⟩

theorem lt32_of_has {x : BitVec 64} (h : Range.has ⟨0, 0xffffffff⟩ x) : x.toNat < 2 ^ 32 := by
  simp only [Range.has] at h
  bv_omega

theorem lt31_of_has {x : BitVec 64} (h : Range.has ⟨0, 0x7fffffff⟩ x) : x.toNat < 2 ^ 31 := by
  simp only [Range.has] at h
  bv_omega

theorem ult_low {x y : BitVec 64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    (x.setWidth 32).ult (y.setWidth 32) = x.ult y := by
  simp only [BitVec.ult, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem msb_low {x : BitVec 64} (hx : x.toNat < 2 ^ 31) :
    (x.setWidth 32).msb = false ∧ x.msb = false := by
  refine ⟨BitVec.msb_eq_false_iff_two_mul_lt.mpr ?_, BitVec.msb_eq_false_iff_two_mul_lt.mpr ?_⟩
  · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    omega
  · omega

theorem slt_low {x y : BitVec 64} (hx : x.toNat < 2 ^ 31) (hy : y.toNat < 2 ^ 31) :
    (x.setWidth 32).slt (y.setWidth 32) = x.slt y := by
  rw [BitVec.slt_eq_ult, BitVec.slt_eq_ult, (msb_low hx).1, (msb_low hx).2, (msb_low hy).1,
    (msb_low hy).2, ult_low (by omega) (by omega)]

theorem and_le_left (x y : BitVec 64) : (x &&& y).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]
  exact Nat.and_le_left

/-- **A relation between the low halves of two values that fit is the
relation between them.** -/
theorem Rel.eval_low {r : Rel} {x y : BitVec 64} (hx : r.fitRange.has x) (hy : r.fitRange.has y) :
    r.eval (x.setWidth 32) (y.setWidth 32) = r.eval x y := by
  cases r with
  | eq =>
    have hx := lt32_of_has hx
    have hy := lt32_of_has hy
    show (x.setWidth 32 == y.setWidth 32) = (x == y)
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    constructor <;> intro h <;> bv_omega
  | ult => exact ult_low (lt32_of_has hx) (lt32_of_has hy)
  | slt => exact slt_low (lt31_of_has hx) (lt31_of_has hy)
  | tstz =>
    have hz : (x &&& y).toNat < 2 ^ 32 := Nat.lt_of_le_of_lt (and_le_left x y) (lt32_of_has hx)
    show (x.setWidth 32 &&& y.setWidth 32 == 0) = (x &&& y == 0)
    rw [← BitVec.setWidth_and, Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    generalize x &&& y = z at hz
    constructor <;> intro h <;> bv_omega
  | tstneg =>
    have hz : (x &&& y).toNat < 2 ^ 31 := Nat.lt_of_le_of_lt (and_le_left x y) (lt31_of_has hx)
    show (x.setWidth 32 &&& y.setWidth 32).msb = (x &&& y).msb
    rw [← BitVec.setWidth_and, (msb_low hz).1, (msb_low hz).2]
  | tstpos =>
    have hz : (x &&& y).toNat < 2 ^ 31 := Nat.lt_of_le_of_lt (and_le_left x y) (lt31_of_has hx)
    show (0 : BitVec 32).slt (x.setWidth 32 &&& y.setWidth 32) = (0 : BitVec 64).slt (x &&& y)
    rw [← BitVec.setWidth_and]
    exact slt_low (x := 0) (by decide) hz
  | never => rfl

theorem Form.eval_low {f : Form} {x y : BitVec 64} (hx : f.rel.fitRange.has x)
    (hy : f.rel.fitRange.has y) : f.eval (x.setWidth 32) (y.setWidth 32) = f.eval x y := by
  unfold Form.eval
  rw [Rel.eval_low hx hy, Rel.eval_low hy hx]

end TypedAsm.U
