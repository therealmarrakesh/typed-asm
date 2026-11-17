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
