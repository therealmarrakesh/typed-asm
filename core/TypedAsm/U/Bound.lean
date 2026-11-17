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
