import TypedAsm.Step

/-!
# What a decided condition says of the values compared

After a subtraction or a comparison, each condition on the flags is a
relation between the two operands: equal, below, less than. After a test,
it is one of their conjunction. Here is which, as two tables, and that the
flags say so. Nothing here is of any one instruction.
-/

namespace TypedAsm.U

open TypedAsm

theorem sub_res (w : Width) (a b : BitVec w.bits) : (subBorrow a b false).1 = a - b := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    (apply BitVec.eq_of_toNat_eq
     have := a.isLt; have := b.isLt
     simp [subBorrow, BitVec.toNat_sub, BitVec.toNat_setWidth]
     omega)

theorem sub_eq0 {n : Nat} (a b : BitVec n) : (a - b == 0) = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  constructor
  · intro h
    have := congrArg (· + b) h
    simpa [BitVec.sub_add_cancel] using this
  · rintro rfl
    exact BitVec.sub_self a

theorem ult_cf {n : Nat} (a b : BitVec n) : BitVec.usubOverflow a b = a.ult b := rfl

theorem ule_not {n : Nat} (a b : BitVec n) : (a.ult b || a == b) = !(b.ult a) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.ult, BitVec.toNat_eq]
  omega

theorem bool_ne_iff (x y : Bool) : (¬ x = y) = ((x = true) ↔ ¬ (y = true)) := by
  cases x <;> cases y <;> decide

theorem slt_sub32 (a b : BitVec 32) :
    ((a - b).msb != BitVec.ssubOverflow a b) = a.slt b := by
  have := a.isLt; have := b.isLt
  rw [Bool.eq_iff_iff]
  by_cases ha : 2 * a.toNat < 4294967296 <;> by_cases hb : 2 * b.toNat < 4294967296 <;>
    simp [BitVec.slt, BitVec.ssubOverflow, BitVec.msb_eq_decide, BitVec.toNat_sub,
      BitVec.toInt_eq_toNat_cond, ha, hb] <;>
    simp only [bool_ne_iff, Bool.or_eq_true, decide_eq_true_eq] <;> omega

theorem slt_sub64 (a b : BitVec 64) :
    ((a - b).msb != BitVec.ssubOverflow a b) = a.slt b := by
  have := a.isLt; have := b.isLt
  rw [Bool.eq_iff_iff]
  by_cases ha : 2 * a.toNat < 18446744073709551616 <;> by_cases hb : 2 * b.toNat < 18446744073709551616 <;>
    simp [BitVec.slt, BitVec.ssubOverflow, BitVec.msb_eq_decide, BitVec.toNat_sub,
      BitVec.toInt_eq_toNat_cond, ha, hb] <;>
    simp only [bool_ne_iff, Bool.or_eq_true, decide_eq_true_eq] <;> omega

theorem slt_sub (w : Width) (a b : BitVec w.bits) :
    ((a - b).msb != BitVec.ssubOverflow a b) = a.slt b := by
  cases w
  · exact slt_sub32 a b
  · exact slt_sub64 a b

theorem sle_not {n : Nat} (a b : BitVec n) : (a == b || a.slt b) = !(b.slt a) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.slt, ← BitVec.toInt_inj]
  omega

theorem pos_iff {n : Nat} (r : BitVec n) : ((0 : BitVec n).slt r) = (!(r == 0) && !r.msb) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.slt, BitVec.msb_eq_toInt, ← BitVec.toInt_inj]
  omega

/-- A relation between two numbers of a width. -/
inductive Rel
  /-- Equal. -/
  | eq
  /-- Below, as numbers without sign. -/
  | ult
  /-- Less, as numbers with sign. -/
  | slt
  /-- No bit in common. -/
  | tstz
  /-- The top bit in common. -/
  | tstneg
  /-- What they have in common is, with sign, more than nothing. -/
  | tstpos
  /-- Never. -/
  | never
  deriving DecidableEq

def Rel.eval {n : Nat} : Rel → BitVec n → BitVec n → Bool
  | .eq, a, b => a == b
  | .ult, a, b => a.ult b
  | .slt, a, b => a.slt b
  | .tstz, a, b => a &&& b == 0
  | .tstneg, a, b => (a &&& b).msb
  | .tstpos, a, b => (0 : BitVec n).slt (a &&& b)
  | .never, _, _ => false

/-- A relation, perhaps with the operands the other way round, perhaps
denied. -/
structure Form where
  neg : Bool
  rel : Rel
  swap : Bool
  deriving DecidableEq

def Form.eval {n : Nat} (f : Form) (a b : BitVec n) : Bool :=
  let r := if f.swap then f.rel.eval b a else f.rel.eval a b
  if f.neg then !r else r

/-- What each condition says after `a - b`. The conditions on the sign or
the overflow of the difference alone say nothing of `a` against `b`. -/
def condSub : Cond → Option Form
  | .e => some ⟨false, .eq, false⟩
  | .ne => some ⟨true, .eq, false⟩
  | .b => some ⟨false, .ult, false⟩
  | .ae => some ⟨true, .ult, false⟩
  | .be => some ⟨true, .ult, true⟩
  | .a => some ⟨false, .ult, true⟩
  | .l => some ⟨false, .slt, false⟩
  | .ge => some ⟨true, .slt, false⟩
  | .le => some ⟨true, .slt, true⟩
  | .g => some ⟨false, .slt, true⟩
  | _ => none

/-- What each condition says after a test of `a` against `b`. -/
def condTst : Cond → Form
  | .e | .be => ⟨false, .tstz, false⟩
  | .ne | .a => ⟨true, .tstz, false⟩
  | .s | .l => ⟨false, .tstneg, false⟩
  | .ns | .ge => ⟨true, .tstneg, false⟩
  | .le => ⟨true, .tstpos, false⟩
  | .g => ⟨false, .tstpos, false⟩
  | .b | .o => ⟨false, .never, false⟩
  | .ae | .no => ⟨true, .never, false⟩

theorem subBorrow_flags (w : Width) (a b : BitVec w.bits) :
    (subBorrow a b false).2
      = ⟨some (a.ult b), some (a == b), some (a - b).msb, some (BitVec.ssubOverflow a b)⟩ := by
  have hcf := subBorrow_cf w a b
  have hof := subBorrow_of w a b
  have hzf : (subBorrow a b false).2.zf = some (a == b) := by
    show some ((subBorrow a b false).1 == 0) = _
    rw [sub_res, sub_eq0]
  have hsf : (subBorrow a b false).2.sf = some (a - b).msb := by
    show some (subBorrow a b false).1.msb = _
    rw [sub_res]
  generalize (subBorrow a b false).2 = F at hcf hof hzf hsf
  cases F
  cases hcf; cases hof; cases hzf; cases hsf
  rfl

/-- **After a subtraction, a condition is the relation the table gives.** -/
theorem condSub_eval (w : Width) (a b : BitVec w.bits) {c : Cond} {f : Form}
    (h : condSub c = some f) : c.eval (subBorrow a b false).2 = some (f.eval a b) := by
  rw [subBorrow_flags]
  have hl := slt_sub w a b
  cases c <;> cases h
  case b => rfl
  case ae => rfl
  case e => rfl
  case ne => rfl
  case be => exact congrArg some (ule_not a b)
  case a => exact congrArg some (show (!(a.ult b || a == b)) = b.ult a by rw [ule_not, Bool.not_not])
  case l => exact congrArg some hl
  case ge =>
    exact congrArg some (show ((a - b).msb == BitVec.ssubOverflow a b) = !(a.slt b) by
      rw [← hl]; cases (a - b).msb <;> cases BitVec.ssubOverflow a b <;> rfl)
  case le =>
    exact congrArg some (show (a == b || ((a - b).msb != BitVec.ssubOverflow a b)) = !(b.slt a) by
      rw [hl, sle_not])
  case g =>
    exact congrArg some (show (!(a == b) && ((a - b).msb == BitVec.ssubOverflow a b)) = b.slt a by
      have h2 := sle_not a b
      rw [← hl] at h2
      cases hx : (a - b).msb <;> cases hy : BitVec.ssubOverflow a b <;>
        cases hz : (a == b) <;> rw [hx, hy, hz] at h2 <;> simpa using h2.symm)

/-- **After a test, likewise.** -/
theorem condTst_eval {n : Nat} (a b : BitVec n) (c : Cond) :
    c.eval (Flags.ofResult (a &&& b) false false) = some ((condTst c).eval a b) := by
  show _ = some (if (condTst c).neg then !(if (condTst c).swap then (condTst c).rel.eval b a
    else (condTst c).rel.eval a b) else (if (condTst c).swap then (condTst c).rel.eval b a
    else (condTst c).rel.eval a b))
  have hz : Rel.eval .tstz a b = (a &&& b == 0) := rfl
  have hn : Rel.eval .tstneg a b = (a &&& b).msb := rfl
  have hp : Rel.eval .tstpos a b = (0 : BitVec n).slt (a &&& b) := rfl
  have hv : Rel.eval .never a b = false := rfl
  revert hz hn hp hv
  generalize a &&& b = r
  intro hz hn hp hv
  cases c <;> simp only [condTst, Bool.false_eq_true, ↓reduceIte, hz, hn, hp, hv] <;> first
    | rfl
    | exact congrArg some (by
        try rw [pos_iff]
        generalize (r == 0) = x; generalize r.msb = y; cases x <;> cases y <;> rfl)

end TypedAsm.U
