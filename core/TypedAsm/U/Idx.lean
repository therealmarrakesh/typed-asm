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

end TypedAsm.U
