import TypedAsm.U.Simp

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

/-- A term is the sum of what it is taken apart into. -/
theorem Val.summands_den (ρ : Env) : (a : Val) → a.den ρ = sumDen ρ a.summands.1 + a.summands.2
  | .lit v => by simp [Val.summands, sumDen, Val.den]
  | .add a b => by
    simp only [Val.summands, Val.den, sumDen_append]
    rw [Val.summands_den ρ a, Val.summands_den ρ b]
    bv_omega
  | .var i => by simp [Val.summands, sumDen]
  | .bvar d i => by simp [Val.summands, sumDen]
  | .shl a k => by simp [Val.summands, sumDen]
  | .out .. => by simp [Val.summands, sumDen]
  | .stored .. => by simp [Val.summands, sumDen]
  | .goes .. => by simp [Val.summands, sumDen]

/-- How far an address is past another, where the two are sums of the same
terms: the difference of the numbers added. -/
def offsetFrom (a base : Val) : Option Nat :=
  if a.summands.1 = base.summands.1 then some (a.summands.2 - base.summands.2).toNat else none

theorem offsetFrom_den {ρ : Env} {a base : Val} {o : Nat} (h : offsetFrom a base = some o) :
    a.den ρ = base.den ρ + BitVec.ofNat 64 o := by
  unfold offsetFrom at h
  split at h
  · next he =>
    cases h
    rw [Val.summands_den ρ a, Val.summands_den ρ base, he]
    bv_omega
  · cases h

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
