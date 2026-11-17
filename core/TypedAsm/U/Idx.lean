import TypedAsm.U.Know

namespace TypedAsm.U
open TypedAsm

theorem ofNat_mul_toNat (a b : BitVec 64) : BitVec.ofNat 64 (a.toNat * b.toNat) = a * b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]

theorem ofNat_eight (n : Nat) : BitVec.ofNat 64 (8 * n) = 8 * BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_mul]
  rfl

/-- Multiples of eight, as an eighth as many, counted in whole numbers:
nothing unless each is so many eights. -/
def idxMs : Multiples (BitVec 64) → Option (Multiples Int)
  | [] => some []
  | p :: ps =>
    if p.1 = 8 * (p.1 / 8) then
      (idxMs ps).map fun r => (((p.1 / 8).toNat : Int), p.2) :: r
    else none

theorem idxMs_den (ρ : Env) : (l : Multiples (BitVec 64)) → {r : Multiples Int} → idxMs l = some r →
    ∃ i : Nat, multDen (natOf ρ) r = i ∧ multDen (Val.den ρ) l = BitVec.ofNat 64 (8 * i)
  | [], r, h => by
    cases h
    exact ⟨0, rfl, rfl⟩
  | p :: ps, r, h => by
    simp only [idxMs] at h
    split at h
    · next h8 =>
      cases hr : idxMs ps with
      | none => rw [hr] at h; cases h
      | some r' =>
        rw [hr] at h
        cases h
        obtain ⟨i, hi, hd⟩ := idxMs_den ρ ps hr
        refine ⟨(p.1 / 8).toNat * (p.2.den ρ).toNat + i, ?_, ?_⟩
        · show ((p.1 / 8).toNat : Int) * natOf ρ p.2 + multDen (natOf ρ) r' = _
          rw [hi]
          simp only [natOf]
          omega
        · show p.1 * p.2.den ρ + multDen (Val.den ρ) ps = _
          rw [hd, Nat.mul_add, BitVec.ofNat_add, ofNat_eight ((p.1 / 8).toNat * _),
            ofNat_mul_toNat, ← BitVec.mul_assoc, ← h8]
    · cases h

/-- **How many along an address is**, where taking one address from another
leaves only eights: the count, in whole numbers. -/
def idxOf (D : Lin (BitVec 64)) : Option (Lin Int) :=
  if D.k = 8 * (D.k / 8) then (idxMs D.ms).map fun r => ⟨r, ((D.k / 8).toNat : Int)⟩ else none

theorem idxOf_den (ρ : Env) {D : Lin (BitVec 64)} {P : Lin Int} (h : idxOf D = some P) :
    ∃ i : Nat, P.den (natOf ρ) = i ∧ D.den (Val.den ρ) = BitVec.ofNat 64 (8 * i) := by
  unfold idxOf at h
  split at h
  · next h8 =>
    cases hr : idxMs D.ms with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      cases h
      obtain ⟨i, hi, hd⟩ := idxMs_den ρ D.ms hr
      refine ⟨i + (D.k / 8).toNat, ?_, ?_⟩
      · show multDen (natOf ρ) r + ((D.k / 8).toNat : Int) = _
        rw [hi]
        omega
      · show multDen (Val.den ρ) D.ms + D.k = _
        rw [hd, Nat.mul_add, BitVec.ofNat_add, ofNat_eight (D.k / 8).toNat, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, ← h8]
  · cases h

end TypedAsm.U
