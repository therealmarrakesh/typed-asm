import TypedAsm.U.Know

namespace TypedAsm.U
open TypedAsm

theorem ofNat_mul_toNat (a b : BitVec 64) : BitVec.ofNat 64 (a.toNat * b.toNat) = a * b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]

theorem ofNat_times (s n : Nat) : BitVec.ofNat 64 (s * n) = BitVec.ofNat 64 s * BitVec.ofNat 64 n :=
  BitVec.ofNat_mul ..

/-- Multiples of a stride, as so many strides each, counted in whole
numbers, a multiple past half of all there are read as below nought:
nothing unless each is so many strides. -/
def idxMs (s : Nat) : Multiples (BitVec 64) → Option (Multiples Int)
  | [] => some []
  | p :: ps =>
    if p.1.toInt = s * (p.1.toInt / s) then
      (idxMs s ps).map fun r => (p.1.toInt / s, p.2) :: r
    else none

theorem idxMs_den (ρ : Env) (s : Nat) : (l : Multiples (BitVec 64)) → {r : Multiples Int} →
    idxMs s l = some r →
    multDen (Val.den ρ) l = BitVec.ofInt 64 (s * multDen (natOf ρ) r)
  | [], r, h => by
    cases h
    simp [multDen]
  | p :: ps, r, h => by
    simp only [idxMs] at h
    split at h
    · next h8 =>
      cases hr : idxMs s ps with
      | none => rw [hr] at h; cases h
      | some r' =>
        rw [hr] at h
        cases h
        have ih := idxMs_den ρ s ps hr
        show p.1 * p.2.den ρ + multDen (Val.den ρ) ps
          = BitVec.ofInt 64 (s * (p.1.toInt / s * natOf ρ p.2 + multDen (natOf ρ) r'))
        have e : (s : Int) * (p.1.toInt / s * natOf ρ p.2 + multDen (natOf ρ) r')
            = p.1.toInt * ((p.2.den ρ).toNat : Int) + s * multDen (natOf ρ) r' := by
          rw [Int.mul_add, ← Int.mul_assoc, ← h8]
          rfl
        rw [e, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_natCast,
          BitVec.ofNat_toNat, BitVec.setWidth_eq, ih]
    · cases h

/-- **How many strides along an address is**, where taking one address from
another leaves only whole strides: the count, in whole numbers, which may
be below nought. -/
def idxOf (s : Nat) (D : Lin (BitVec 64)) : Option (Lin Int) :=
  if D.k.toInt = s * (D.k.toInt / s) then
    (idxMs s D.ms).map fun r => ⟨r, D.k.toInt / s⟩
  else none

theorem idxOf_int (ρ : Env) {s : Nat} {D : Lin (BitVec 64)} {P : Lin Int}
    (h : idxOf s D = some P) :
    D.den (Val.den ρ) = BitVec.ofInt 64 (s * P.den (natOf ρ)) := by
  unfold idxOf at h
  split at h
  · next h8 =>
    cases hr : idxMs s D.ms with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      cases h
      show multDen (Val.den ρ) D.ms + D.k
        = BitVec.ofInt 64 (s * (multDen (natOf ρ) r + D.k.toInt / s))
      rw [Int.mul_add, ← h8, BitVec.ofInt_add, BitVec.ofInt_toInt, idxMs_den ρ s D.ms hr]
  · cases h

theorem idxOf_den (ρ : Env) {s : Nat} {D : Lin (BitVec 64)} {P : Lin Int}
    (h : idxOf s D = some P) (h0 : 0 ≤ P.den (natOf ρ)) :
    ∃ i : Nat, P.den (natOf ρ) = i ∧ D.den (Val.den ρ) = BitVec.ofNat 64 (s * i) := by
  refine ⟨(P.den (natOf ρ)).toNat, (Int.toNat_of_nonneg h0).symm, ?_⟩
  rw [idxOf_int ρ h, ← BitVec.ofInt_natCast, Int.natCast_mul, Int.toNat_of_nonneg h0]

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
  ⟨D.ms.map fun p => (BitVec.ofInt 64 (p.1.toInt / s), p.2), BitVec.ofInt 64 (D.k.toInt / s)⟩

theorem idxMs_val (ρ : Env) (s : Nat) : (l : Multiples (BitVec 64)) → {r : Multiples Int} →
    idxMs s l = some r →
    multDen (Val.den ρ) (l.map fun p => (BitVec.ofInt 64 (p.1.toInt / s), p.2))
      = BitVec.ofInt 64 (multDen (natOf ρ) r)
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
        show BitVec.ofInt 64 (p.1.toInt / s) * p.2.den ρ + multDen (Val.den ρ) (ps.map _)
          = BitVec.ofInt 64 (p.1.toInt / s * ((p.2.den ρ).toNat : Int) + multDen (natOf ρ) r')
        rw [ih, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
          BitVec.setWidth_eq]
    · cases h

/-- **How many strides along, as a term**: it stands for the count. -/
theorem idxLin_den (ρ : Env) {s : Nat} {D : Lin (BitVec 64)} {P : Lin Int} (h : idxOf s D = some P) :
    (idxLin s D).val.den ρ = BitVec.ofInt 64 (P.den (natOf ρ)) := by
  unfold idxOf at h
  split at h
  · cases hr : idxMs s D.ms with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      cases h
      rw [Lin.val_den]
      show multDen (Val.den ρ) (D.ms.map _) + BitVec.ofInt 64 (D.k.toInt / s)
        = BitVec.ofInt 64 (multDen (natOf ρ) r + D.k.toInt / s)
      rw [idxMs_val ρ s D.ms hr, BitVec.ofInt_add]
  · cases h

end TypedAsm.U
