import TypedAsm.Step

/-!
# What a divide computes

Where the divisor is not nought and the quotient fits, a divide raises no
error and gives the quotient and the remainder. Facts of the machine's
arithmetic.
-/

namespace TypedAsm

/-- An unsigned divide of a dividend whose upper half is zero, by a divisor
that is not zero, raises no divide error. -/
theorem MulDivOp.eval_div {n : Nat} (a b : BitVec n) (hb : b ≠ 0) :
    MulDivOp.eval .div 0 a b = .next (a / b, a % b, .unknown) := by
  have hbn : b.toNat ≠ 0 := fun h0 => hb (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hbpos : 0 < b.toNat := Nat.pos_of_ne_zero hbn
  have ha := a.isLt
  have hb' := b.isLt
  have hpow : 2 ^ n ≤ 2 ^ (n + n) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right n n)
  have hdiv : a.toNat / b.toNat < 2 ^ n := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  have hmod : a.toNat % b.toNat < 2 ^ n := Nat.lt_of_lt_of_le (Nat.mod_lt _ hbpos) (Nat.le_of_lt hb')
  have hdvd : ((0 : BitVec n) ++ a).toNat = a.toNat := by
    simp [BitVec.toNat_append]
  have hbw : (b.setWidth (n + n)).toNat = b.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hq : (((0 : BitVec n) ++ a) / b.setWidth (n + n)).toNat = a.toNat / b.toNat := by
    rw [BitVec.toNat_udiv, hdvd, hbw]
  have hr : (((0 : BitVec n) ++ a) % b.setWidth (n + n)).toNat = a.toNat % b.toNat := by
    rw [BitVec.toNat_umod, hdvd, hbw]
  have hb0 : (b == 0) = false := by simpa using hb
  have hfit : ((((0 : BitVec n) ++ a) / b.setWidth (n + n)).setWidth n).setWidth (n + n)
      = ((0 : BitVec n) ++ a) / b.setWidth (n + n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hq]
    rw [Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt (by omega)]
  have hlo : (((0 : BitVec n) ++ a) / b.setWidth (n + n)).setWidth n = a / b := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hq, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt hdiv
  have hhi : (((0 : BitVec n) ++ a) % b.setWidth (n + n)).setWidth n = a % b := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, hr, BitVec.toNat_umod]
    exact Nat.mod_eq_of_lt hmod
  rw [hlo] at hfit
  simp only [MulDivOp.eval, hb0, hlo, hhi, hfit, bne_self_eq_false, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]

/-- A value with its sign bit copied across the upper half is its sign extension. -/
theorem signFill_append {n : Nat} (a : BitVec n) : signFill a ++ a = a.signExtend (n + n) := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_signExtend, signFill]
  by_cases h : i < n
  · simp [h]
  · simp only [h, ↓reduceDIte]
    by_cases hm : a.msb = true <;> simp [hm]

/-- A signed divide of a sign-extended dividend, by a divisor that is not
zero, raises no divide error unless it is the one quotient that does not
fit: the most negative number divided by minus one. -/
theorem MulDivOp.eval_idiv {n : Nat} (a b : BitVec n) (hb : b ≠ 0)
    (hov : a ≠ BitVec.intMin n ∨ b ≠ -1#n) :
    MulDivOp.eval .idiv (signFill a) a b = .next (a.sdiv b, a.srem b, .unknown) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim b 0) hb
    · exact h
  have hle : n ≤ n + n := Nat.le_add_right n n
  have hAi : (a.signExtend (n + n)).toInt = a.toInt := BitVec.toInt_signExtend_of_le hle
  have hDi : (b.signExtend (n + n)).toInt = b.toInt := BitVec.toInt_signExtend_of_le hle
  have hne : a.signExtend (n + n) ≠ BitVec.intMin (n + n) := by
    intro h
    have ht := congrArg BitVec.toInt h
    rw [hAi, BitVec.toInt_intMin] at ht
    have hlow := BitVec.le_toInt a
    have hpow : (2 : Nat) ^ (n - 1) < 2 ^ (n + n - 1) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hmod : (2 : Nat) ^ (n + n - 1) % 2 ^ (n + n) = 2 ^ (n + n - 1) :=
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    rw [hmod] at ht
    have hcast : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by norm_cast
    rw [hcast] at hlow
    omega
  have hq : (a.signExtend (n + n)).sdiv (b.signExtend (n + n)) = (a.sdiv b).signExtend (n + n) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (.inl hne), hAi, hDi,
      BitVec.toInt_signExtend_of_le hle, BitVec.toInt_sdiv_of_ne_or_ne _ _ hov]
  have hr : (a.signExtend (n + n)).srem (b.signExtend (n + n)) = (a.srem b).signExtend (n + n) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_srem, hAi, hDi, BitVec.toInt_signExtend_of_le hle, BitVec.toInt_srem]
  have htr : ∀ x : BitVec n, (x.signExtend (n + n)).setWidth n = x := by
    intro x
    ext i hi
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, hi, ↓reduceIte,
      BitVec.getLsbD_eq_getElem hi]
    have hi' : i < n + n := by omega
    simp [hi']
  have hb0 : (b == 0) = false := by simpa using hb
  simp only [MulDivOp.eval, signFill_append, hq, hr, htr, hb0, bne_self_eq_false, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]

end TypedAsm
