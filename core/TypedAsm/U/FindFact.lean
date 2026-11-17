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

/-- The fact a context has that an address is so far into a block others
may point into: the first, of a pointer the address is a number past, with
the bytes asked for inside the block. With the block's shape, whether it
may be written through that pointer, and how far in. -/
def findFact (a : Val) (n : Nat) : List (Val × TyS) → Option (Val × ShapeS × Bool × Nat × Nat)
  | [] => none
  | (p, .ptr Sh w off) :: rest =>
    if a.summands.1 = p.summands.1 then
      let o := (a.summands.2 - p.summands.2 + BitVec.ofNat 64 off).toNat
      if o + n ≤ Sh.size then some (p, Sh, w, off, o) else findFact a n rest
    else findFact a n rest
  | _ :: rest => findFact a n rest

theorem findFact_spec {ρ : Env} {a : Val} {n : Nat} :
    (l : List (Val × TyS)) → {p : Val} → {Sh : ShapeS} → {w : Bool} → {off o : Nat} →
    findFact a n l = some (p, Sh, w, off, o) →
    (p, TyS.ptr Sh w off) ∈ l ∧ o + n ≤ Sh.size ∧
      a.den ρ + BitVec.ofNat 64 off = p.den ρ + BitVec.ofNat 64 o
  | [], _, _, _, _, _, h => by cases h
  | (q, τ) :: rest, p, Sh, w, off, o, h => by
    have tail : findFact a n rest = some (p, Sh, w, off, o) →
        (p, TyS.ptr Sh w off) ∈ (q, τ) :: rest ∧ o + n ≤ Sh.size ∧
          a.den ρ + BitVec.ofNat 64 off = p.den ρ + BitVec.ofNat 64 o := fun h' => by
      obtain ⟨hm, hin, ha⟩ := findFact_spec rest h'
      exact ⟨List.mem_cons_of_mem _ hm, hin, ha⟩
    cases τ with
    | ptr Sh' w' off' =>
      simp only [findFact] at h
      split at h
      · next hsum =>
        split at h
        · next hin =>
          cases h
          refine ⟨List.mem_cons_self, hin, ?_⟩
          rw [Val.summands_den ρ a, Val.summands_den ρ q, hsum, BitVec.ofNat_toNat,
            BitVec.setWidth_eq]
          rw [BitVec.add_assoc, BitVec.add_assoc]
          congr 1
          rw [← BitVec.add_assoc, BitVec.add_comm q.summands.2, BitVec.sub_add_cancel]
        · exact tail h
      · exact tail h
    | any => exact tail h
    | ref _ _ _ => exact tail h
    | nullable _ => exact tail h
    | orErr _ => exact tail h
    | str _ => exact tail h
    | atom _ => exact tail h
    | code _ _ _ _ _ => exact tail h
    | range _ _ => exact tail h

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
