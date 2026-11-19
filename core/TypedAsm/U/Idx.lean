import TypedAsm.U.Know

namespace TypedAsm.U
open TypedAsm

theorem ofNat_mul_toNat (a b : BitVec 64) : BitVec.ofNat 64 (a.toNat * b.toNat) = a * b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]

theorem ofNat_times (s n : Nat) : BitVec.ofNat 64 (s * n) = BitVec.ofNat 64 s * BitVec.ofNat 64 n :=
  BitVec.ofNat_mul ..

/-- Multiples of a stride, as so many strides each, counted in whole
numbers: nothing unless each is so many strides. -/
def idxMs (s : Nat) : Multiples (BitVec 64) → Option (Multiples Int)
  | [] => some []
  | p :: ps =>
    if p.1 = BitVec.ofNat 64 s * (p.1 / BitVec.ofNat 64 s) then
      (idxMs s ps).map fun r => (((p.1 / BitVec.ofNat 64 s).toNat : Int), p.2) :: r
    else none

theorem idxMs_den (ρ : Env) (s : Nat) : (l : Multiples (BitVec 64)) → {r : Multiples Int} →
    idxMs s l = some r →
    ∃ i : Nat, multDen (natOf ρ) r = i ∧ multDen (Val.den ρ) l = BitVec.ofNat 64 (s * i)
  | [], r, h => by
    cases h
    exact ⟨0, rfl, by simp [multDen]⟩
  | p :: ps, r, h => by
    simp only [idxMs] at h
    split at h
    · next h8 =>
      cases hr : idxMs s ps with
      | none => rw [hr] at h; cases h
      | some r' =>
        rw [hr] at h
        cases h
        obtain ⟨i, hi, hd⟩ := idxMs_den ρ s ps hr
        refine ⟨(p.1 / BitVec.ofNat 64 s).toNat * (p.2.den ρ).toNat + i, ?_, ?_⟩
        · show ((p.1 / BitVec.ofNat 64 s).toNat : Int) * natOf ρ p.2 + multDen (natOf ρ) r' = _
          rw [hi]
          simp only [natOf]
          omega
        · show p.1 * p.2.den ρ + multDen (Val.den ρ) ps = _
          rw [hd, Nat.mul_add, BitVec.ofNat_add,
            ofNat_times s ((p.1 / BitVec.ofNat 64 s).toNat * _), ofNat_mul_toNat,
            ← BitVec.mul_assoc, ← h8, ofNat_times]
    · cases h

/-- **How many strides along an address is**, where taking one address from
another leaves only whole strides: the count, in whole numbers. -/
def idxOf (s : Nat) (D : Lin (BitVec 64)) : Option (Lin Int) :=
  if D.k = BitVec.ofNat 64 s * (D.k / BitVec.ofNat 64 s) then
    (idxMs s D.ms).map fun r => ⟨r, ((D.k / BitVec.ofNat 64 s).toNat : Int)⟩
  else none

theorem idxOf_den (ρ : Env) {s : Nat} {D : Lin (BitVec 64)} {P : Lin Int} (h : idxOf s D = some P) :
    ∃ i : Nat, P.den (natOf ρ) = i ∧ D.den (Val.den ρ) = BitVec.ofNat 64 (s * i) := by
  unfold idxOf at h
  split at h
  · next h8 =>
    cases hr : idxMs s D.ms with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      cases h
      obtain ⟨i, hi, hd⟩ := idxMs_den ρ s D.ms hr
      refine ⟨i + (D.k / BitVec.ofNat 64 s).toNat, ?_, ?_⟩
      · show multDen (natOf ρ) r + ((D.k / BitVec.ofNat 64 s).toNat : Int) = _
        rw [hi]
        omega
      · show multDen (Val.den ρ) D.ms + D.k = _
        rw [hd, Nat.mul_add, BitVec.ofNat_add, ofNat_times s (D.k / BitVec.ofNat 64 s).toNat,
          BitVec.ofNat_toNat, BitVec.setWidth_eq, ← h8]
  · cases h

/-- A term times a written-out number, bit by bit of the number's lowest
so many. -/
def Val.bitsTimes (c : BitVec 64) (t : Val) : Nat → Val
  | 0 => .lit 0
  | n + 1 => if c.getLsbD n then .bin .add (Val.bitsTimes c t n) (.un (.shl n) t)
      else Val.bitsTimes c t n

theorem Val.bitsTimes_den (ρ : Env) (c : BitVec 64) (t : Val) : (n : Nat) →
    (Val.bitsTimes c t n).den ρ = BitVec.ofNat 64 (c.toNat % 2 ^ n) * t.den ρ
  | 0 => by
    show (0 : BitVec 64) = _
    rw [Nat.pow_zero, Nat.mod_one]
    exact (BitVec.zero_mul).symm
  | n + 1 => by
    have ih := Val.bitsTimes_den ρ c t n
    have hbit : c.getLsbD n = decide (c.toNat / 2 ^ n % 2 = 1) := by
      rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
    have htp : BitVec.twoPow 64 n = BitVec.ofNat 64 (2 ^ n) :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_twoPow, BitVec.toNat_ofNat])
    rw [Nat.mod_pow_succ]
    unfold Val.bitsTimes
    by_cases hb : c.toNat / 2 ^ n % 2 = 1
    · rw [hbit, decide_eq_true hb]
      show (Val.bitsTimes c t n).den ρ + t.den ρ <<< n = _
      rw [ih, hb, Nat.mul_one, BitVec.ofNat_add, BitVec.add_mul, BitVec.shiftLeft_eq_mul_twoPow,
        BitVec.mul_comm (t.den ρ), htp]
    · have h0 : c.toNat / 2 ^ n % 2 = 0 := by omega
      rw [hbit, decide_eq_false hb]
      show (Val.bitsTimes c t n).den ρ = _
      rw [ih, h0, Nat.mul_zero, Nat.add_zero]

/-- A term times a written-out number. -/
def Val.mulLit (c : BitVec 64) (t : Val) : Val :=
  if c = 1 then t else if c = -1 then .un (.neg .w64) t else Val.bitsTimes c t 64

theorem Val.mulLit_den (ρ : Env) (c : BitVec 64) (t : Val) :
    (Val.mulLit c t).den ρ = c * t.den ρ := by
  unfold Val.mulLit
  split
  · next h => rw [h]; exact (BitVec.one_mul _).symm
  · split
    · next h =>
      show Un.eval (.neg .w64) (t.den ρ) = _
      rw [neg64, h]
    · rw [Val.bitsTimes_den, Nat.mod_eq_of_lt c.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Multiples of terms, as one term. -/
def multVal : Multiples (BitVec 64) → Val → Val
  | [], acc => acc
  | p :: ps, acc => multVal ps (.bin .add acc (Val.mulLit p.1 p.2))

theorem multVal_den (ρ : Env) : (l : Multiples (BitVec 64)) → (acc : Val) →
    (multVal l acc).den ρ = acc.den ρ + multDen (Val.den ρ) l
  | [], acc => by simp [multVal, multDen]
  | p :: ps, acc => by
    rw [multVal, multVal_den ρ ps]
    show acc.den ρ + (Val.mulLit p.1 p.2).den ρ + _ = acc.den ρ + (p.1 * p.2.den ρ + _)
    rw [Val.mulLit_den, BitVec.add_assoc]

/-- **A sum of multiples of terms and a number, as one term.** -/
def Lin.val (L : Lin (BitVec 64)) : Val :=
  match L.ms with
  | [] => .lit L.k
  | p :: ps =>
    if L.k = 0 then multVal ps (Val.mulLit p.1 p.2)
    else .bin .add (multVal ps (Val.mulLit p.1 p.2)) (.lit L.k)

theorem Lin.val_den (ρ : Env) (L : Lin (BitVec 64)) : L.val.den ρ = L.den (Val.den ρ) := by
  obtain ⟨ms, k⟩ := L
  unfold Lin.val Lin.den
  cases ms with
  | nil => simp [multDen, Val.den]
  | cons p ps =>
    show (if k = 0 then _ else _ : Val).den ρ = (p.1 * p.2.den ρ + multDen (Val.den ρ) ps) + k
    split
    · next h => rw [multVal_den, Val.mulLit_den, h]; exact (BitVec.add_zero _).symm
    · show (multVal ps (Val.mulLit p.1 p.2)).den ρ + k = _
      rw [multVal_den, Val.mulLit_den]

/-- A sum of multiples of a stride, as so many strides. -/
def idxLin (s : Nat) (D : Lin (BitVec 64)) : Lin (BitVec 64) :=
  ⟨D.ms.map fun p => (p.1 / BitVec.ofNat 64 s, p.2), D.k / BitVec.ofNat 64 s⟩

theorem idxMs_val (ρ : Env) (s : Nat) : (l : Multiples (BitVec 64)) → {r : Multiples Int} →
    idxMs s l = some r →
    multDen (Val.den ρ) (l.map fun p => (p.1 / BitVec.ofNat 64 s, p.2))
      = BitVec.ofNat 64 (multDen (natOf ρ) r).toNat
  | [], r, h => by
    cases h
    simp [multDen]
  | p :: ps, r, h => by
    simp only [idxMs] at h
    split at h
    · cases hr : idxMs s ps with
      | none => rw [hr] at h; cases h
      | some r' =>
        rw [hr] at h
        cases h
        have ih := idxMs_val ρ s ps hr
        obtain ⟨i, hi, -⟩ := idxMs_den ρ s ps hr
        show p.1 / BitVec.ofNat 64 s * p.2.den ρ + multDen (Val.den ρ) (ps.map _) = BitVec.ofNat 64
          (((p.1 / BitVec.ofNat 64 s).toNat : Int) * natOf ρ p.2 + multDen (natOf ρ) r').toNat
        rw [ih, hi]
        have e : (((p.1 / BitVec.ofNat 64 s).toNat : Int) * natOf ρ p.2 + (i : Int)).toNat
            = (p.1 / BitVec.ofNat 64 s).toNat * (p.2.den ρ).toNat + i := by
          simp only [natOf]
          omega
        rw [e, BitVec.ofNat_add, ofNat_mul_toNat]
        simp
    · cases h

/-- **How many strides along, as a term**: it stands for the count. -/
theorem idxLin_den (ρ : Env) {s : Nat} {D : Lin (BitVec 64)} {P : Lin Int} (h : idxOf s D = some P) :
    (idxLin s D).val.den ρ = BitVec.ofNat 64 (P.den (natOf ρ)).toNat := by
  unfold idxOf at h
  split at h
  · cases hr : idxMs s D.ms with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      cases h
      obtain ⟨i, hi, -⟩ := idxMs_den ρ s D.ms hr
      rw [Lin.val_den]
      show multDen (Val.den ρ) (D.ms.map _) + D.k / BitVec.ofNat 64 s
        = BitVec.ofNat 64 (multDen (natOf ρ) r + ((D.k / BitVec.ofNat 64 s).toNat : Int)).toNat
      rw [idxMs_val ρ s D.ms hr, hi]
      have e : ((i : Int) + ((D.k / BitVec.ofNat 64 s).toNat : Int)).toNat
          = i + (D.k / BitVec.ofNat 64 s).toNat := by omega
      rw [e, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, Int.toNat_natCast]
  · cases h

end TypedAsm.U
