import TypedAsm.U.Norm

/-!
# Terms as sums of multiples

A term taken apart: a number, and so many times each of the terms it is
made of by adding, negating and shifting left. Two terms that come apart
the same way stand for the same value, however they were written; so the
checker sees that `(a + 1) << 3` is `(a << 3) + 8`, and that a count taken
from five and then one more taken is four less the count.
-/

namespace TypedAsm.U

open TypedAsm

/-- So many times each of some terms. -/
abbrev Multiples := List (BitVec 64 × Val)

/-- What they come to, added up. -/
def multDen (ρ : Env) : Multiples → BitVec 64
  | [] => 0
  | p :: ps => p.1 * p.2.den ρ + multDen ρ ps

/-- So many more of a term: added to what there is of it, and the term
dropped where none is left. -/
def put (c : BitVec 64) (t : Val) : Multiples → Multiples
  | [] => if c = 0 then [] else [(c, t)]
  | p :: ps =>
    if p.2 = t then (if p.1 + c = 0 then ps else (p.1 + c, t) :: ps) else p :: put c t ps

theorem put_den (ρ : Env) (c : BitVec 64) (t : Val) :
    (l : Multiples) → multDen ρ (put c t l) = c * t.den ρ + multDen ρ l
  | [] => by
    unfold put
    split
    · next h =>
      rw [h]
      simp
    · rfl
  | p :: ps => by
    unfold put
    split
    · next h =>
      subst h
      split
      · next h0 =>
        show multDen ρ ps = c * p.2.den ρ + (p.1 * p.2.den ρ + multDen ρ ps)
        rw [← BitVec.add_assoc, ← BitVec.add_mul, BitVec.add_comm c, h0]
        simp
      · show (p.1 + c) * p.2.den ρ + multDen ρ ps = c * p.2.den ρ + (p.1 * p.2.den ρ + multDen ρ ps)
        rw [← BitVec.add_assoc, ← BitVec.add_mul, BitVec.add_comm c]
    · show p.1 * p.2.den ρ + multDen ρ (put c t ps) = c * t.den ρ + (p.1 * p.2.den ρ + multDen ρ ps)
      rw [put_den ρ c t ps]
      ac_rfl

/-- So many times some multiples, added to others. -/
def putAll (k : BitVec 64) : Multiples → Multiples → Multiples
  | [], l => l
  | p :: ps, l => putAll k ps (put (k * p.1) p.2 l)

theorem putAll_den (ρ : Env) (k : BitVec 64) :
    (a l : Multiples) → multDen ρ (putAll k a l) = k * multDen ρ a + multDen ρ l
  | [], l => by
    show multDen ρ l = k * 0 + multDen ρ l
    simp
  | p :: ps, l => by
    show multDen ρ (putAll k ps (put (k * p.1) p.2 l)) = k * (p.1 * p.2.den ρ + multDen ρ ps) + _
    rw [putAll_den ρ k ps, put_den, BitVec.mul_add, BitVec.mul_assoc]
    ac_rfl

/-- **A term taken apart**: the multiples it is a sum of, and the number
added. -/
def Val.lin : Val → Multiples × BitVec 64
  | .lit v => ([], v)
  | .bin .add a b => (putAll 1 b.lin.1 a.lin.1, a.lin.2 + b.lin.2)
  | .un (.shl k) a => (putAll (BitVec.twoPow 64 k) a.lin.1 [], BitVec.twoPow 64 k * a.lin.2)
  | .un (.neg .w64) a => (putAll (-1) a.lin.1 [], -1 * a.lin.2)
  | t => (put 1 t [], 0)

theorem lin_leaf (ρ : Env) (t : Val) : t.den ρ = multDen ρ (put 1 t []) + 0 := by
  rw [put_den]
  simp [multDen]

theorem negOne_mul (a : BitVec 64) : -1 * a = -a := by
  rw [BitVec.neg_mul]
  simp

theorem neg64 (a : BitVec 64) : Un.eval (.neg .w64) a = -1 * a := by
  show (subBorrow 0 (a.setWidth 64) false).1.setWidth 64 = -1 * a
  rw [sub_res64, BitVec.setWidth_eq, negOne_mul]
  simp

/-- **A term is what it comes apart into.** -/
theorem Val.lin_den (ρ : Env) : (a : Val) → a.den ρ = multDen ρ a.lin.1 + a.lin.2
  | .lit v => by
    show v = 0 + v
    simp
  | .bin .add a b => by
    show a.den ρ + b.den ρ = multDen ρ (putAll 1 b.lin.1 a.lin.1) + (a.lin.2 + b.lin.2)
    rw [putAll_den, Val.lin_den ρ a, Val.lin_den ρ b]
    bv_omega
  | .un (.shl k) a => by
    show a.den ρ <<< k = multDen ρ (putAll (BitVec.twoPow 64 k) a.lin.1 []) + _ * a.lin.2
    rw [putAll_den, Val.lin_den ρ a, BitVec.shiftLeft_eq_mul_twoPow, BitVec.mul_comm,
      BitVec.mul_add]
    simp [multDen]
  | .un (.neg .w64) a => by
    show Un.eval (.neg .w64) (a.den ρ) = multDen ρ (putAll (-1) a.lin.1 []) + -1 * a.lin.2
    rw [putAll_den, neg64, Val.lin_den ρ a, BitVec.mul_add]
    simp [multDen]
  | .bin (.shift ..) a b => lin_leaf ρ _
  | .bin (.imul _) a b => lin_leaf ρ _
  | .var i => lin_leaf ρ _
  | .bvar d i => lin_leaf ρ _
  | .slot .. => lin_leaf ρ _
  | .un (.neg .w32) _ => lin_leaf ρ _
  | .un (.not _) _ => lin_leaf ρ _
  | .un (.popcnt _) _ => lin_leaf ρ _
  | .un (.bswap _) _ => lin_leaf ρ _
  | .un (.signFill _) _ => lin_leaf ρ _
  | .un (.trunc _) _ => lin_leaf ρ _
  | .un (.zx ..) _ => lin_leaf ρ _
  | .un (.sx ..) _ => lin_leaf ρ _
  | .un .sxd _ => lin_leaf ρ _
  | .un .low8 _ => lin_leaf ρ _
  | .un .low16 _ => lin_leaf ρ _
  | .tri .. => lin_leaf ρ _
  | .fop .. => lin_leaf ρ _

/-- Whether two terms come apart the same way: taking one from the other
leaves nothing. -/
def Val.linSame (a b : Val) : Bool :=
  (putAll (-1) b.lin.1 a.lin.1).isEmpty && a.lin.2 == b.lin.2

theorem Val.linSame_den (ρ : Env) {a b : Val} (h : a.linSame b = true) : a.den ρ = b.den ρ := by
  simp only [Val.linSame, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
  have e := putAll_den ρ (-1) b.lin.1 a.lin.1
  rw [h.1] at e
  have e' : multDen ρ a.lin.1 = multDen ρ b.lin.1 := by
    have : (0 : BitVec 64) = -1 * multDen ρ b.lin.1 + multDen ρ a.lin.1 := e
    rw [negOne_mul] at this
    bv_omega
  rw [Val.lin_den ρ a, Val.lin_den ρ b, e', h.2]

end TypedAsm.U
