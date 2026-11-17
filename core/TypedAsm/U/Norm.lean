import TypedAsm.U.Fill
import TypedAsm.U.CondRel

/-!
# Terms built as plainly as they can be

An operator applied to terms is itself a term. Here each kind of operator
is applied so that the term is as plain as it can be: worked out, where
every operand is a number written out; a sum, where it is one, so that an
address moved about and stepped is still seen to be so many bytes from
where it started; nought, where a value is taken from itself; the operand
itself, where the operator does nothing to it.

This is said of operators, once each. It is not said of instructions: an
instruction's description is built of operators, and is made plain as it is
filled in.
-/

namespace TypedAsm.U

open TypedAsm

theorem wide_low (w : Width) (r : BitVec w.bits) : (wide r).setWidth w.bits = r := by
  cases w <;> simp [wide, Width.bits]

/-! ## One operand -/

def mkUn (o : Un) (a : Val) : Val :=
  match o, a with
  | .trunc .w64, a => a
  | o, .lit v => .lit (o.eval v)
  | o, a => .un o a

theorem mkUn_den (ρ : Env) (o : Un) (a : Val) : (mkUn o a).den ρ = o.eval (a.den ρ) := by
  unfold mkUn
  split
  · show a.den ρ = BitVec.setWidth 64 (BitVec.setWidth 64 (a.den ρ))
    simp
  · rfl
  · rfl

/-! ## Two operands -/

def mkBin (o : Bin) (a b : Val) : Val :=
  match a.lit?, b.lit? with
  | some x, some y => .lit (o.eval x y)
  | _, some n =>
    match o with
    | .shift .shl .w64 => .shl a (n.toNat % 64)
    | o => .bin o a b
  | _, none => .bin o a b

theorem shl64 (fl : Flags) (a : BitVec 64) (n : Nat) : (ShiftOp.eval .shl fl a n).1 = a <<< n := by
  unfold ShiftOp.eval
  split
  · next h0 => rw [h0]; simp
  · rfl

theorem mkBin_den (ρ : Env) (o : Bin) (a b : Val) :
    (mkBin o a b).den ρ = o.eval (a.den ρ) (b.den ρ) := by
  unfold mkBin
  split
  · next x y ha hb =>
    show o.eval x y = _
    rw [Val.lit?_den ha, Val.lit?_den hb]
  · next n hb _ =>
    split
    · show a.den ρ <<< (n.toNat % 64)
        = BitVec.setWidth 64 (ShiftOp.eval .shl Flags.unknown (BitVec.setWidth 64 (a.den ρ))
            ((b.den ρ).toNat % 64)).1
      rw [shl64, Val.lit?_den hb]
      simp
    · rfl
  · rfl

/-! ## Three operands -/

def mkTri (o : Tri) (a b c : Val) : Val :=
  match a, b, c with
  | .lit x, .lit y, .lit z => .lit (o.eval x y z)
  | a, b, c => .tri o a b c

theorem mkTri_den (ρ : Env) (o : Tri) (a b c : Val) :
    (mkTri o a b c).den ρ = o.eval (a.den ρ) (b.den ρ) (c.den ρ) := by
  unfold mkTri
  split <;> rfl

/-! ## Two operands and the flags -/

/-- Whether an operation takes the carry flag in. -/
def _root_.TypedAsm.AluOp.carryIn : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

/-- What an operation that takes no carry in gives does not turn on the
flags before it. -/
theorem alu_noCarry {op : AluOp} (h : op.carryIn = false) (w : Width) (f g : Flags)
    (a b : BitVec 64) : FOp.eval (.alu op w) f a b = FOp.eval (.alu op w) g a b := by
  cases op <;> first | rfl | cases h

theorem add_res64 (a b : BitVec 64) : (addCarry a b false).1 = a + b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt
  simp [addCarry, BitVec.toNat_add, BitVec.toNat_setWidth]

theorem sub_res64 (a b : BitVec 64) : (subBorrow a b false).1 = a - b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt
  simp [subBorrow, BitVec.toNat_sub, BitVec.toNat_setWidth]
  omega

theorem alu_add64 (f : Flags) (a b : BitVec 64) : FOp.eval (.alu .add .w64) f a b = a + b := by
  show BitVec.setWidth 64 (addCarry (BitVec.setWidth 64 a) (BitVec.setWidth 64 b) false).1 = _
  rw [add_res64]
  simp

theorem alu_sub64 (f : Flags) (a b : BitVec 64) : FOp.eval (.alu .sub .w64) f a b = a + -b := by
  show BitVec.setWidth 64 (subBorrow (BitVec.setWidth 64 a) (BitVec.setWidth 64 b) false).1 = _
  rw [sub_res64]
  simp only [BitVec.setWidth_eq, BitVec.sub_eq_add_neg]

theorem alu_xorSelf (w : Width) (f : Flags) (a : BitVec 64) : FOp.eval (.alu .xor w) f a a = 0 := by
  show wide (BitVec.setWidth w.bits a ^^^ BitVec.setWidth w.bits a) = 0
  rw [BitVec.xor_self]
  cases w <;> rfl

theorem alu_subSelf (w : Width) (f : Flags) (a : BitVec 64) : FOp.eval (.alu .sub w) f a a = 0 := by
  show wide (subBorrow (BitVec.setWidth w.bits a) (BitVec.setWidth w.bits a) false).1 = 0
  rw [sub_res, BitVec.sub_self]
  cases w <;> rfl

/-- Whether an operation, of a value and itself, gives nought. -/
def _root_.TypedAsm.AluOp.selfZero : AluOp → Bool
  | .xor | .sub => true
  | _ => false

def mkAlu (op : AluOp) (w : Width) (fl : FlagsT) (a b : Val) : Val :=
  if op.carryIn then .fop (.alu op w) fl a b
  else if op.selfZero && a == b then .lit 0
  else
    match a.lit?, b.lit? with
    | some x, some y => .lit (FOp.eval (.alu op w) Flags.unknown x y)
    | _, yb =>
      match op, w with
      | .add, .w64 => .add a b
      | .sub, .w64 =>
        match yb with
        | some y => .add a (.lit (-y))
        | none => .fop (.alu op w) fl a b
      | _, _ => .fop (.alu op w) fl a b

theorem mkAlu_den (ρ : Env) (op : AluOp) (w : Width) (fl : FlagsT) (a b : Val) :
    (mkAlu op w fl a b).den ρ = FOp.eval (.alu op w) (fl.den ρ) (a.den ρ) (b.den ρ) := by
  unfold mkAlu
  split
  · rfl
  · next hc =>
    have hc : op.carryIn = false := by simpa using hc
    split
    · next hz =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hz
      obtain ⟨hz, rfl⟩ := hz
      cases op with
      | xor => exact (alu_xorSelf w (fl.den ρ) (a.den ρ)).symm
      | sub => exact (alu_subSelf w (fl.den ρ) (a.den ρ)).symm
      | _ => exact Bool.noConfusion hz
    · split
      · next x y ha hb =>
        show FOp.eval (.alu op w) Flags.unknown x y = _
        rw [Val.lit?_den ha, Val.lit?_den hb]
        exact alu_noCarry hc w _ _ _ _
      · next yb _ =>
        split
        · exact (alu_add64 (fl.den ρ) (a.den ρ) (b.den ρ)).symm
        · split
          · next y hy =>
            show a.den ρ + -y = _
            rw [alu_sub64, Val.lit?_den hy]
          · rfl
        · rfl

def mkFop (o : FOp) (fl : FlagsT) (a b : Val) : Val :=
  match o with
  | .alu op w => mkAlu op w fl a b
  | o => .fop o fl a b

theorem mkFop_den (ρ : Env) (o : FOp) (fl : FlagsT) (a b : Val) :
    (mkFop o fl a b).den ρ = o.eval (fl.den ρ) (a.den ρ) (b.den ρ) := by
  unfold mkFop
  split
  · exact mkAlu_den ρ _ _ fl a b
  · rfl

/-! ## An instruction's term, filled in and made plain -/

/-- A term of an instruction's description, with what the instruction
computes with put in, built as plainly as it can be. -/
def Val.fillN (σ : Filling) : Val → Val
  | .slot s => σ.slot s
  | .un o a => mkUn o (a.fillN σ)
  | .bin o a b => mkBin o (a.fillN σ) (b.fillN σ)
  | .tri o a b c => mkTri o (a.fillN σ) (b.fillN σ) (c.fillN σ)
  | .fop o fl a b => mkFop o (fl.fill σ) (a.fillN σ) (b.fillN σ)
  | t => t.fill σ

theorem Val.den_fillN (ρ : Env) (σ : Filling) : (a : Val) → (a.fillN σ).den ρ = a.den (ρ.filled σ)
  | .slot s => rfl
  | .un o a => by
    simp only [Val.fillN, mkUn_den, Val.den, Val.den_fillN ρ σ a]
  | .bin o a b => by
    simp only [Val.fillN, mkBin_den, Val.den, Val.den_fillN ρ σ a, Val.den_fillN ρ σ b]
  | .tri o a b c => by
    simp only [Val.fillN, mkTri_den, Val.den, Val.den_fillN ρ σ a, Val.den_fillN ρ σ b,
      Val.den_fillN ρ σ c]
  | .fop o fl a b => by
    simp only [Val.fillN, mkFop_den, Val.den, Val.den_fillN ρ σ a, Val.den_fillN ρ σ b,
      FlagsT.den_fill]
  | .lit v => Val.den_fill ρ σ (.lit v)
  | .var j => Val.den_fill ρ σ (.var j)
  | .bvar d j => Val.den_fill ρ σ (.bvar d j)

end TypedAsm.U
