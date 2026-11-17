import TypedAsm.U.Upper

/-!
# How far an address is past another, within a stretch

An address is a sum of terms and a number. Where it is the terms of another
address with more terms besides, each of which the context bounds, it is
that address with a number added that lies within a stretch: from the
difference of the numbers, for as much as the other terms can come to. An
indexed address is so: the base, and an index the program has compared
against a bound. Where there are no terms besides, the stretch is nothing
and the address is exactly so far past.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

/-- A list of terms with those of another taken out, one for one; nothing
unless each is there. -/
def without : List Val → List Val → Option (List Val)
  | l, [] => some l
  | l, t :: ts => if t ∈ l then without (l.erase t) ts else none

theorem sumDen_erase (ρ : Env) {t : Val} :
    (l : List Val) → t ∈ l → sumDen ρ l = t.den ρ + sumDen ρ (l.erase t)
  | [], h => nomatch h
  | x :: xs, h => by
    by_cases hx : x = t
    · subst hx
      rw [List.erase_cons_head]
      rfl
    · have ht : t ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      rw [List.erase_cons_tail (by simpa using hx)]
      show x.den ρ + sumDen ρ xs = t.den ρ + (x.den ρ + sumDen ρ (xs.erase t))
      rw [sumDen_erase ρ xs ht, ← BitVec.add_assoc, BitVec.add_comm (x.den ρ), BitVec.add_assoc]

theorem without_den (ρ : Env) : (ts l : List Val) → {e : List Val} → without l ts = some e →
    sumDen ρ l = sumDen ρ ts + sumDen ρ e
  | [], l, e, h => by
    cases h
    exact (BitVec.zero_add _).symm
  | t :: ts, l, e, h => by
    unfold without at h
    split at h
    · next hm =>
      rw [sumDen_erase ρ l hm, without_den ρ ts (l.erase t) h]
      show _ = (t.den ρ + sumDen ρ ts) + sumDen ρ e
      rw [BitVec.add_assoc]
    · cases h

/-- The most a list of terms can come to, added up. -/
def CtxS.upperAll (Γ : CtxS) : List Val → Option Nat
  | [] => some 0
  | t :: ts =>
    match Γ.upper t, Γ.upperAll ts with
    | some x, some y => some (x + y)
    | _, _ => none

theorem CtxS.upperAll_le {ρ : Env} {Γ : CtxS} {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    (l : List Val) → {m : Nat} → Γ.upperAll l = some m → (sumDen ρ l).toNat ≤ m
  | [], m, h => by cases h; exact Nat.le_refl _
  | t :: ts, m, h => by
    unfold CtxS.upperAll at h
    split at h
    · next x y hx hy =>
      cases h
      have h1 := CtxS.upper_le hg t hx
      have h2 := CtxS.upperAll_le hg ts hy
      show (t.den ρ + sumDen ρ ts).toNat ≤ x + y
      rw [BitVec.toNat_add]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add h1 h2)
    · cases h

theorem span_arith (E p q : BitVec 64) : q + (p - q + E) = E + p := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_comm p, BitVec.add_assoc, ← BitVec.add_assoc q,
    BitVec.add_right_neg, BitVec.zero_add, BitVec.add_comm]

/-- **How far an address is past another, within a stretch**: from so far,
for at most so much more. -/
def CtxS.spanFrom (Γ : CtxS) (a base : Val) : Option (Nat × Nat) :=
  match without a.summands.1 base.summands.1 with
  | some extra =>
    match Γ.upperAll extra with
    | some M => some ((a.summands.2 - base.summands.2).toNat, M)
    | none => none
  | none => none

theorem CtxS.spanFrom_den {ρ : Env} {Γ : CtxS} {a base : Val} {o M : Nat}
    (h : Γ.spanFrom a base = some (o, M)) {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    ∃ o', a.den ρ = base.den ρ + BitVec.ofNat 64 o' ∧ o ≤ o' ∧ o' ≤ o + M := by
  unfold CtxS.spanFrom at h
  split at h
  · next extra hw =>
    split at h
    · next M' hM =>
      cases h
      have hE := CtxS.upperAll_le hg extra hM
      have hsum := without_den ρ base.summands.1 a.summands.1 hw
      refine ⟨(a.summands.2 - base.summands.2).toNat + (sumDen ρ extra).toNat, ?_,
        Nat.le_add_right _ _, Nat.add_le_add_left hE _⟩
      rw [Val.summands_den ρ a, Val.summands_den ρ base, hsum, BitVec.ofNat_add,
        BitVec.ofNat_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]
      generalize sumDen ρ base.summands.1 = X
      generalize sumDen ρ extra = E
      generalize a.summands.2 = p
      generalize base.summands.2 = q
      rw [BitVec.add_assoc X q, span_arith, BitVec.add_assoc]
    · cases h
  · cases h

end TypedAsm.U
