import TypedAsm.U.Check
import TypedAsm.U.CondRel
import TypedAsm.U.Norm
import TypedAsm.U.Lin
import TypedAsm.U.Size

/-!
# Which bytes an address names

An address is a term: often the address of something, with something
added, perhaps in several steps. It names bytes of a region the context
holds if what it is past the region's address, with the bytes asked for,
is within the region's size. How far past is a term; where it and the size
are numbers written out the question is answered by looking, and otherwise
by what is known of values.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

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

/-- The first region of a list an address names bytes of, with how far in,
among those it is a number past (`plain`), or among the others. The bytes
are as many as some terms come to and `n` more. -/
def findHeldP (plain : Bool) (G : List (Val × TyS)) (a : Val) (ls : List Val) (n : Nat) :
    List (Val × HeldS) → Nat → Option (Nat × Val × HeldS × Val)
  | [], _ => none
  | (b, S) :: rest, k =>
    if (a.minus b).isSome == plain && sumLe G (offTerm a b :: ls) n [S.size] 0 then
      some (k, b, S, offTerm a b)
    else findHeldP plain G a ls n rest (k + 1)

theorem findHeldP_raw {plain : Bool} {G : List (Val × TyS)} {a : Val} {ls : List Val} {n : Nat} :
    (l : List (Val × HeldS)) → (k₀ : Nat) → {k : Nat} → {b : Val} → {S : HeldS} → {o : Val} →
    findHeldP plain G a ls n l k₀ = some (k, b, S, o) →
    ∃ j, k = k₀ + j ∧ l[j]? = some (b, S) ∧ sumLe G (o :: ls) n [S.size] 0 = true ∧
      o = offTerm a b
  | [], _, _, _, _, _, h => by cases h
  | (b', S') :: rest, k₀, k, b, S, o, h => by
    unfold findHeldP at h
    split at h
    · next hc =>
      cases h
      exact ⟨0, rfl, rfl, (Bool.and_eq_true _ _ |>.mp hc).2, rfl⟩
    · obtain ⟨j, hj, hl, hin, ha⟩ := findHeldP_raw rest (k₀ + 1) h
      exact ⟨j + 1, by omega, hl, hin, ha⟩

theorem findHeldP_spec {ρ : Env} {Ψ' : MemTy} {m : Nat} {plain : Bool} {G : List (Val × TyS)}
    {a : Val} {ls : List Val} {n : Nat}
    (l : List (Val × HeldS)) (k₀ : Nat) {k : Nat} {b : Val} {S : HeldS} {o : Val}
    (h : findHeldP plain G a ls n l k₀ = some (k, b, S, o))
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' m (g.2.den ρ) (g.1.den ρ)) :
    ∃ j, k = k₀ + j ∧ l[j]? = some (b, S) ∧ o.nat ρ + (sumNat ρ ls + n) ≤ S.size.nat ρ ∧
      a.den ρ = b.den ρ + BitVec.ofNat 64 (o.nat ρ) := by
  obtain ⟨j, hj, hl, hin, ho⟩ := findHeldP_raw l k₀ h
  refine ⟨j, hj, hl, ?_, ?_⟩
  · have := sumLe_den hin hg
    simp only [sumNat, Nat.add_zero] at this
    omega
  · rw [ho, Val.nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact offTerm_den ρ a b

/-- **The region the context holds that an address names bytes of**, with
how far in: the first whose address the address is a number past, with the
bytes asked for inside it; failing that, the first it is shown to lie in by
what is known of values. -/
def findHeld (G : List (Val × TyS)) (a : Val) (ls : List Val) (n : Nat) (l : List (Val × HeldS))
    (k : Nat) : Option (Nat × Val × HeldS × Val) :=
  match findHeldP true G a ls n l k with
  | some r => some r
  | none => findHeldP false G a ls n l k

theorem findHeld_spec {ρ : Env} {Ψ' : MemTy} {m : Nat} {G : List (Val × TyS)} {a : Val}
    {ls : List Val} {n : Nat}
    (l : List (Val × HeldS)) (k₀ : Nat) {k : Nat} {b : Val} {S : HeldS} {o : Val}
    (h : findHeld G a ls n l k₀ = some (k, b, S, o))
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' m (g.2.den ρ) (g.1.den ρ)) :
    ∃ j, k = k₀ + j ∧ l[j]? = some (b, S) ∧ o.nat ρ + (sumNat ρ ls + n) ≤ S.size.nat ρ ∧
      a.den ρ = b.den ρ + BitVec.ofNat 64 (o.nat ρ) := by
  unfold findHeld at h
  split at h
  · next r hr => cases h; exact findHeldP_spec l k₀ hr hg
  · exact findHeldP_spec l k₀ h hg

end TypedAsm.U
