import TypedAsm.U.Order

/-!
# A term as a whole number

What a term comes apart into, counted in whole numbers: the same multiples,
each read with its sign. It is the term's value but for wrapping; and the
value itself where it is seen to lie from nought to below two to the
sixty-fourth.
-/

namespace TypedAsm.U

open TypedAsm

/-- What a term is worth as a whole number. -/
def natOf (ρ : Env) (t : Val) : Int := ((t.den ρ).toNat : Int)

/-- Multiples of the machine's values as multiples of whole numbers, each
read with its sign. -/
def intMs : Multiples (BitVec 64) → Multiples Int
  | [] => []
  | p :: ps => (p.1.toInt, p.2) :: intMs ps

theorem intMs_den (ρ : Env) : (l : Multiples (BitVec 64)) →
    BitVec.ofInt 64 (multDen (natOf ρ) (intMs l)) = multDen (Val.den ρ) l
  | [] => rfl
  | p :: ps => by
    show BitVec.ofInt 64 (p.1.toInt * natOf ρ p.2 + multDen (natOf ρ) (intMs ps)) = _
    rw [BitVec.ofInt_add, BitVec.ofInt_mul, intMs_den ρ ps, BitVec.ofInt_toInt]
    show p.1 * BitVec.ofInt 64 ((p.2.den ρ).toNat : Int) + _ = _
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl

/-- **A term as a whole number**: its multiples with their signs, and the
number added, with its sign or without. -/
def Val.int (signed : Bool) (v : Val) : Lin Int :=
  ⟨intMs v.lin.ms, if signed then v.lin.k.toInt else (v.lin.k.toNat : Int)⟩

/-- It is the term's value, but for wrapping. -/
theorem Val.int_den (ρ : Env) (signed : Bool) (v : Val) :
    BitVec.ofInt 64 ((v.int signed).den (natOf ρ)) = v.den ρ := by
  rw [← Val.lin_den ρ v]
  show BitVec.ofInt 64 (multDen (natOf ρ) (intMs v.lin.ms) + _) = multDen (Val.den ρ) v.lin.ms + v.lin.k
  rw [BitVec.ofInt_add, intMs_den]
  congr 1
  cases signed
  · show BitVec.ofInt 64 (v.lin.k.toNat : Int) = v.lin.k
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact BitVec.ofInt_toInt

/-- **And the value itself, where it lies from nought to below two to the
sixty-fourth.** -/
theorem Val.int_eq (ρ : Env) (signed : Bool) (v : Val)
    (h0 : 0 ≤ (v.int signed).den (natOf ρ))
    (h1 : (v.int signed).den (natOf ρ) < 18446744073709551616) :
    natOf ρ v = (v.int signed).den (natOf ρ) := by
  have e := Val.int_den ρ signed v
  generalize (v.int signed).den (natOf ρ) = P at *
  show ((v.den ρ).toNat : Int) = P
  rw [← e, BitVec.toNat_ofInt]
  omega

end TypedAsm.U
