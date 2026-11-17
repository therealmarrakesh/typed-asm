import TypedAsm.U.Term
import TypedAsm.U.CondRel
import TypedAsm.U.Norm

/-!
# How flags come of two values

Flags are those of one value less another, or of a test of one against
another, or say at least whether a result is nought and whether it is
negative, or say only whether a value is nought. Here are those four, and
what each means of the flags.
-/

namespace TypedAsm.U

open TypedAsm

/-- How flags come of two operands. -/
inductive FlagKind
  /-- As of the first less the second. -/
  | sub
  /-- As of a test of the first against the second. -/
  | tst
  /-- The zero and sign flags are the first's; of the others nothing is said. -/
  | res
  /-- The zero flag says whether the first is zero; the others are clear. -/
  | zero
  deriving DecidableEq

def FlagKind.Holds {n : Nat} : FlagKind → BitVec n → BitVec n → Flags → Prop
  | .sub, x, y, F => F = (subBorrow x y false).2
  | .tst, x, y, F => F = Flags.ofResult (x &&& y) false false
  | .res, x, _, F => F.zf = some (x == 0) ∧ F.sf = some x.msb
  | .zero, x, _, F => F = ⟨some false, some (x == 0), some false, some false⟩

/-- A shift by a count that is not nought leaves the zero and sign flags
those of its result. -/
theorem shift_res {n : Nat} {op : ShiftOp} (hop : op = .shl ∨ op = .shr ∨ op = .sar) (fl : Flags)
    (a : BitVec n) {c : Nat} (hc : c ≠ 0) :
    (op.eval fl a c).2.zf = some ((op.eval fl a c).1 == 0) ∧
      (op.eval fl a c).2.sf = some (op.eval fl a c).1.msb := by
  unfold ShiftOp.eval
  simp only [hc, ↓reduceIte]
  rcases hop with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

end TypedAsm.U
