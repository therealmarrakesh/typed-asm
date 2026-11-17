import TypedAsm.U.Check
import TypedAsm.U.CondRel
import TypedAsm.U.Norm
import TypedAsm.U.Lin

/-!
# Which bytes an address names

An address is a term: often the address of something, with a number added,
perhaps in several steps. To find the bytes it names, the term is taken
apart into the terms it is a sum of and the number added to them. It names
a byte of a region the context holds if it is the region's address, taken
apart the same way, with a number added that is less than the region's
size. Nothing is tried: the terms are compared.
-/

namespace TypedAsm.U

/-- A term as the terms it is a sum of, other than numbers, and the number
added to them. -/
def Val.summands : Val → List Val × BitVec 64
  | .lit v => ([], v)
  | .add a b => (a.summands.1 ++ b.summands.1, a.summands.2 + b.summands.2)
  | t => ([t], 0)

/-- What a list of terms comes to, added up. -/
def sumDen (ρ : Env) : List Val → BitVec 64
  | [] => 0
  | t :: ts => t.den ρ + sumDen ρ ts

theorem sumDen_append (ρ : Env) (l₁ l₂ : List Val) :
    sumDen ρ (l₁ ++ l₂) = sumDen ρ l₁ + sumDen ρ l₂ := by
  induction l₁ with
  | nil => simp [sumDen]
  | cons t ts ih => simp only [List.cons_append, sumDen, ih, BitVec.add_assoc]

theorem sumDen_one (ρ : Env) (t : Val) : t.den ρ = sumDen ρ [t] + 0 := by
  show t.den ρ = t.den ρ + 0 + 0
  simp

/-- A term is the sum of what it is taken apart into. -/
theorem Val.summands_den (ρ : Env) : (a : Val) → a.den ρ = sumDen ρ a.summands.1 + a.summands.2
  | .lit v => by simp [Val.summands, sumDen, Val.den]
  | .bin .add a b => by
    show a.den ρ + b.den ρ = sumDen ρ (a.summands.1 ++ b.summands.1) + (a.summands.2 + b.summands.2)
    rw [sumDen_append, Val.summands_den ρ a, Val.summands_den ρ b]
    bv_omega
  | .bin (.shift ..) a b => sumDen_one ρ _
  | .bin (.imul _) a b => sumDen_one ρ _
  | .var i => sumDen_one ρ _
  | .bvar d i => sumDen_one ρ _
  | .slot .. => sumDen_one ρ _
  | .un .. => sumDen_one ρ _
  | .tri .. => sumDen_one ρ _
  | .fop .. => sumDen_one ρ _

/-- How far an address is past another, where taking the one from the
other leaves only a number, however the two are written. -/
def offsetFrom (a base : Val) : Option Nat := (a.minus base).map (·.toNat)

theorem offsetFrom_den {ρ : Env} {a base : Val} {o : Nat} (h : offsetFrom a base = some o) :
    a.den ρ = base.den ρ + BitVec.ofNat 64 o := by
  unfold offsetFrom at h
  cases hm : a.minus base with
  | none => rw [hm] at h; cases h
  | some k =>
    rw [hm] at h
    cases h
    rw [Val.minus_den ρ hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **The region the context holds that an address names bytes of**, with
how far in: the first whose address the address is a number past, by less
than its size and with the bytes asked for inside it. -/
def findHeld (a : Val) (n : Nat) : List (Val × HeldS) → Nat → Option (Nat × Val × HeldS × Nat)
  | [], _ => none
  | (b, S) :: rest, k =>
    match offsetFrom a b with
    | some o => if o + n ≤ S.size then some (k, b, S, o) else findHeld a n rest (k + 1)
    | none => findHeld a n rest (k + 1)

theorem findHeld_spec {ρ : Env} {a : Val} {n : Nat} :
    (l : List (Val × HeldS)) → (k₀ : Nat) → {k : Nat} → {b : Val} → {S : HeldS} → {o : Nat} →
    findHeld a n l k₀ = some (k, b, S, o) →
    ∃ j, k = k₀ + j ∧ l[j]? = some (b, S) ∧ o + n ≤ S.size ∧
      a.den ρ = b.den ρ + BitVec.ofNat 64 o
  | [], _, _, _, _, _, h => by cases h
  | (b', S') :: rest, k₀, k, b, S, o, h => by
    unfold findHeld at h
    split at h
    · next o' ho =>
      split at h
      · next hin =>
        cases h
        exact ⟨0, rfl, rfl, hin, offsetFrom_den ho⟩
      · obtain ⟨j, hj, hl, hin, ha⟩ := findHeld_spec rest (k₀ + 1) h
        exact ⟨j + 1, by omega, hl, hin, ha⟩
    · obtain ⟨j, hj, hl, hin, ha⟩ := findHeld_spec rest (k₀ + 1) h
      exact ⟨j + 1, by omega, hl, hin, ha⟩

end TypedAsm.U
