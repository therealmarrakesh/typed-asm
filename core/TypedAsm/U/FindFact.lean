import TypedAsm.U.Fresh
import TypedAsm.U.Shared

/-!
# Bytes of a block others may point into, found through a fact

An address names bytes of a block others may point into where the context
knows a value to point into the block, and the address is that value with
a number added. The fact is found by comparing terms, as a region held is.
What reading such bytes tells of the value read is what the block's shape
says is there.
-/

namespace TypedAsm.U

open TypedAsm

/-- The block a value is known to point into, by what is known of it, as
terms: its shape, whether it may be written through the value, and how far
in. A pointer says the shape; a pointer by kind says the kind, whose shape
the program's table of kinds has. -/
def TyS.pointee (kinds : Nat → Option ShapeS) : TyS → Option (ShapeS × Bool × Nat)
  | .ptr Sh w off => some (Sh, w, off)
  | .ref tag w off => (kinds tag).map fun Sh => (Sh, w, off)
  | _ => none

/-- Each kind in a program's table is a kind of the memory typing, of that
shape. The shapes of kinds mention no names: they stand for the same
whatever names stand for. -/
def KindsOk (Ψ : MemTy) (kinds : Nat → Option ShapeS) : Prop :=
  ∀ (ρ : Env) (t : Nat) (Sh : ShapeS), kinds t = some Sh → Ψ.kinds t = some (Sh.den ρ)

/-- A program with no kinds asks nothing of the memory typing's. -/
theorem KindsOk.none (Ψ : MemTy) : KindsOk Ψ fun _ => none := fun _ _ _ h => nomatch h

theorem TyS.pointee_den {Ψ : MemTy} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) (ρ : Env)
    {τ : TyS} {Sh : ShapeS} {w : Bool} {off : Nat} (h : τ.pointee kinds = some (Sh, w, off)) :
    (τ.den ρ).pointee Ψ.kinds = some (Sh.den ρ, w, off) := by
  cases τ with
  | ptr Sh' w' off' => cases h; rfl
  | ref tag w' off' =>
    simp only [TyS.pointee] at h
    cases hkt : kinds tag with
    | none => rw [hkt] at h; cases h
    | some Sh' =>
      rw [hkt] at h
      cases h
      show (Ψ.kinds tag).map _ = _
      rw [hk ρ tag _ hkt]
      rfl
  | _ => cases h

/-- The shape found stands for the same, whatever a name the fact does not
mention stands for. -/
theorem TyS.pointee_setVal {Ψ : MemTy} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds)
    (ρ : Env) (k : Nat) (x : BitVec 64) {τ : TyS} {Sh : ShapeS} {w : Bool} {off : Nat}
    (hu : τ.under k = true) (h : τ.pointee kinds = some (Sh, w, off)) :
    Sh.den (ρ.setVal k x) = Sh.den ρ := by
  cases τ with
  | ptr Sh' w' off' =>
    cases h
    exact ShapeS.den_setVal ρ k x Sh (by simpa only [TyS.under] using hu)
  | ref tag w' off' =>
    simp only [TyS.pointee] at h
    cases hkt : kinds tag with
    | none => rw [hkt] at h; cases h
    | some Sh' =>
      rw [hkt] at h
      cases h
      exact Option.some.inj ((hk (ρ.setVal k x) tag _ hkt).symm.trans (hk ρ tag _ hkt))
  | _ => cases h

/-- The fact a context has that an address is so far into a block others
may point into: the first, of a pointer the address is a number past, with
the bytes asked for inside the block. With the block's shape, whether it
may be written through that pointer, and how far in. -/
def findFact (kinds : Nat → Option ShapeS) (a : Val) (n : Nat) :
    List (Val × TyS) → Option (Val × ShapeS × Bool × Nat × Nat)
  | [] => none
  | (p, τ) :: rest =>
    match τ.pointee kinds with
    | some (Sh, w, off) =>
      match a.minus p with
      | some d =>
        if (d + BitVec.ofNat 64 off).toNat + n ≤ Sh.size then
          some (p, Sh, w, off, (d + BitVec.ofNat 64 off).toNat)
        else findFact kinds a n rest
      | none => findFact kinds a n rest
    | none => findFact kinds a n rest

theorem findFact_spec {ρ : Env} {kinds : Nat → Option ShapeS} {a : Val} {n : Nat} :
    (l : List (Val × TyS)) → {p : Val} → {Sh : ShapeS} → {w : Bool} → {off o : Nat} →
    findFact kinds a n l = some (p, Sh, w, off, o) →
    ∃ τ, (p, τ) ∈ l ∧ τ.pointee kinds = some (Sh, w, off) ∧ o + n ≤ Sh.size ∧
      a.den ρ + BitVec.ofNat 64 off = p.den ρ + BitVec.ofNat 64 o
  | [], _, _, _, _, _, h => by cases h
  | (q, τ) :: rest, p, Sh, w, off, o, h => by
    have tail : findFact kinds a n rest = some (p, Sh, w, off, o) →
        ∃ τ', (p, τ') ∈ (q, τ) :: rest ∧ τ'.pointee kinds = some (Sh, w, off) ∧ o + n ≤ Sh.size ∧
          a.den ρ + BitVec.ofNat 64 off = p.den ρ + BitVec.ofNat 64 o := fun h' => by
      obtain ⟨τ', hm, hpt, hin, ha⟩ := findFact_spec rest h'
      exact ⟨τ', List.mem_cons_of_mem _ hm, hpt, hin, ha⟩
    simp only [findFact] at h
    split at h
    · next Sh' w' off' hpt =>
      split at h
      · next d hsum =>
        split at h
        · next hin =>
          cases h
          refine ⟨τ, List.mem_cons_self, hpt, hin, ?_⟩
          rw [Val.minus_den ρ hsum, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]
        · exact tail h
      · exact tail h
    · exact tail h

/-- What a shape says is at a byte. -/
def ValsS.at (o : Nat) : ValsS → List TyS
  | .nil => []
  | .cons o' τ rest => if o' = o then τ :: rest.at o else rest.at o

/-- What reading the `n` bytes at `o` of a block of a shape tells of the
value read, as terms. -/
def readFactsS (Sh : ShapeS) (o n : Nat) (x : Val) : List (Val × TyS) :=
  if n = 8 then (Sh.vals.at o).map fun τ => (x, τ) else []

theorem ValsS.at_den (ρ : Env) (o : Nat) (x : BitVec 64) :
    (vs : ValsS) → ((vs.den ρ).filter fun q => q.1 = o).map (fun q => (x, q.2))
      = (vs.at o).map fun τ => (x, τ.den ρ)
  | .nil => rfl
  | .cons o' τ rest => by
    simp only [ValsS.den, ValsS.at, List.filter_cons]
    by_cases h : o' = o
    · simp only [h, decide_true, ↓reduceIte, List.map_cons]
      rw [ValsS.at_den ρ o x rest]
    · simp only [h, decide_false, ↓reduceIte]
      exact ValsS.at_den ρ o x rest

theorem readFactsS_den (ρ : Env) (Sh : ShapeS) (o n : Nat) (x : Val) :
    (readFactsS Sh o n x).map (fun f => (f.1.den ρ, f.2.den ρ))
      = readFacts (Sh.den ρ) o n (x.den ρ) := by
  unfold readFactsS readFacts
  split
  · rw [ShapeS.den_vals, ValsS.at_den ρ o (x.den ρ) Sh.vals, List.map_map]
    rfl
  · rfl

end TypedAsm.U
