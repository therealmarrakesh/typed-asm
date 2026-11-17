import TypedAsm.U.Norm

/-!
# Terms as sums of multiples

A term taken apart: a number, and so many times each of the terms it is
made of by adding, negating and shifting left. Two terms that come apart
the same way stand for the same value, however they were written; so the
checker sees that `(a + 1) << 3` is `(a << 3) + 8`.

The taking apart is the same whatever numbers the multiples are counted in:
values of the machine, where sums wrap, for whether two terms are the same
value; whole numbers, for which is the larger.
-/

namespace TypedAsm.U

open TypedAsm Lean.Grind

section
variable {α : Type} [CommRing α] [DecidableEq α]

/-- So many times each of some terms. -/
abbrev Multiples (α : Type) := List (α × Val)

/-- What they come to, added up, the terms being worth what `f` says. -/
def multDen (f : Val → α) : Multiples α → α
  | [] => 0
  | p :: ps => p.1 * f p.2 + multDen f ps

/-- So many more of a term: added to what there is of it, and the term
dropped where none is left. -/
def put (c : α) (t : Val) : Multiples α → Multiples α
  | [] => if c = 0 then [] else [(c, t)]
  | p :: ps =>
    if p.2 = t then (if p.1 + c = 0 then ps else (p.1 + c, t) :: ps) else p :: put c t ps

theorem put_den (f : Val → α) (c : α) (t : Val) :
    (l : Multiples α) → multDen f (put c t l) = c * f t + multDen f l
  | [] => by
    unfold put
    split
    · next h => simp only [multDen, h]; grind
    · simp only [multDen]
  | p :: ps => by
    unfold put
    split
    · next h =>
      subst h
      split
      · next h0 =>
        have : (p.1 + c) * f p.2 = 0 := by rw [h0]; grind
        simp only [multDen]
        grind
      · simp only [multDen]
        grind
    · simp only [multDen, put_den f c t ps]
      grind

/-- So many times some multiples, added to others. -/
def putAll (k : α) : Multiples α → Multiples α → Multiples α
  | [], l => l
  | p :: ps, l => putAll k ps (put (k * p.1) p.2 l)

theorem putAll_den (f : Val → α) (k : α) :
    (a l : Multiples α) → multDen f (putAll k a l) = k * multDen f a + multDen f l
  | [], l => by simp only [putAll, multDen]; grind
  | p :: ps, l => by
    simp only [putAll, multDen, putAll_den f k ps, put_den]
    grind

/-- A sum of multiples and a number. -/
structure Lin (α : Type) where
  ms : Multiples α
  k : α

def Lin.den (f : Val → α) (l : Lin α) : α := multDen f l.ms + l.k

/-- So many times one, added to another. -/
def Lin.addMul (c : α) (a b : Lin α) : Lin α := ⟨putAll c a.ms b.ms, c * a.k + b.k⟩

theorem Lin.addMul_den (f : Val → α) (c : α) (a b : Lin α) :
    (Lin.addMul c a b).den f = c * a.den f + b.den f := by
  simp only [Lin.den, Lin.addMul, putAll_den]
  grind

/-- So many times one. -/
def Lin.scale (c : α) (a : Lin α) : Lin α := Lin.addMul c a ⟨[], 0⟩

theorem Lin.scale_den (f : Val → α) (c : α) (a : Lin α) : (a.scale c).den f = c * a.den f := by
  rw [Lin.scale, Lin.addMul_den]
  simp only [Lin.den, multDen]
  grind

/-- A term alone. -/
def Lin.leaf (t : Val) : Lin α := ⟨put 1 t [], 0⟩

theorem Lin.leaf_den (f : Val → α) (t : Val) : (Lin.leaf t : Lin α).den f = f t := by
  simp only [Lin.leaf, Lin.den, put_den, multDen]
  grind

end

theorem neg64 (a : BitVec 64) : Un.eval (.neg .w64) a = -1 * a := by
  show (subBorrow 0 (a.setWidth 64) false).1.setWidth 64 = -1 * a
  rw [sub_res64, BitVec.setWidth_eq]
  grind

/-- **A term taken apart**, in values of the machine. -/
def Val.lin : Val → Lin (BitVec 64)
  | .lit v => ⟨[], v⟩
  | .bin .add a b => Lin.addMul 1 b.lin a.lin
  | .un (.shl k) a => a.lin.scale (BitVec.twoPow 64 k)
  | .un (.neg .w64) a => a.lin.scale (-1)
  | t => Lin.leaf t

/-- **A term is what it comes apart into.** -/
theorem Val.lin_den (ρ : Env) : (a : Val) → a.lin.den (Val.den ρ) = a.den ρ
  | .lit v => by simp [Val.lin, Lin.den, multDen, Val.den]
  | .bin .add a b => by
    show (Lin.addMul 1 b.lin a.lin).den _ = a.den ρ + b.den ρ
    rw [Lin.addMul_den, Val.lin_den ρ a, Val.lin_den ρ b]
    grind
  | .un (.shl k) a => by
    show (a.lin.scale _).den _ = a.den ρ <<< k
    rw [Lin.scale_den, Val.lin_den ρ a, BitVec.shiftLeft_eq_mul_twoPow, BitVec.mul_comm]
  | .un (.neg .w64) a => by
    show (a.lin.scale _).den _ = Un.eval (.neg .w64) (a.den ρ)
    rw [Lin.scale_den, Val.lin_den ρ a, neg64]
  | .bin (.shift ..) a b => Lin.leaf_den _ _
  | .bin (.imul _) a b => Lin.leaf_den _ _
  | .var i => Lin.leaf_den _ _
  | .bvar d i => Lin.leaf_den _ _
  | .slot .. => Lin.leaf_den _ _
  | .un (.neg .w32) _ => Lin.leaf_den _ _
  | .un (.not _) _ => Lin.leaf_den _ _
  | .un (.popcnt _) _ => Lin.leaf_den _ _
  | .un (.bswap _) _ => Lin.leaf_den _ _
  | .un (.signFill _) _ => Lin.leaf_den _ _
  | .un (.trunc _) _ => Lin.leaf_den _ _
  | .un (.zx ..) _ => Lin.leaf_den _ _
  | .un (.sx ..) _ => Lin.leaf_den _ _
  | .un .sxd _ => Lin.leaf_den _ _
  | .un .low8 _ => Lin.leaf_den _ _
  | .un .low16 _ => Lin.leaf_den _ _
  | .tri .. => Lin.leaf_den _ _
  | .fop .. => Lin.leaf_den _ _
  | .app .. => Lin.leaf_den _ _

/-- Whether two terms come apart the same way: taking one from the other
leaves nothing. -/
def Val.linSame (a b : Val) : Bool :=
  (Lin.addMul (-1) b.lin a.lin).ms.isEmpty && (Lin.addMul (-1) b.lin a.lin).k == 0

theorem Val.linSame_den (ρ : Env) {a b : Val} (h : a.linSame b = true) : a.den ρ = b.den ρ := by
  simp only [Val.linSame, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
  have e := Lin.addMul_den (Val.den ρ) (-1) b.lin a.lin
  rw [Val.lin_den, Val.lin_den] at e
  simp only [Lin.den, h.1, h.2, multDen] at e
  grind

/-- How far one term is past another, where taking the second from the
first leaves only a number. -/
def Val.minus (a p : Val) : Option (BitVec 64) :=
  if (Lin.addMul (-1) p.lin a.lin).ms.isEmpty then some (Lin.addMul (-1) p.lin a.lin).k else none

theorem Val.minus_den (ρ : Env) {a p : Val} {k : BitVec 64} (h : a.minus p = some k) :
    a.den ρ = p.den ρ + k := by
  unfold Val.minus at h
  split at h
  · next he =>
    cases h
    have e := Lin.addMul_den (Val.den ρ) (-1) p.lin a.lin
    rw [Val.lin_den, Val.lin_den] at e
    simp only [Lin.den, List.isEmpty_iff.mp he, multDen] at e
    grind
  · cases h

end TypedAsm.U
