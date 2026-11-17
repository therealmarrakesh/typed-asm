import TypedAsm.U.Learn
import TypedAsm.U.Know

/-!
# Between what numbers a value lies

An amount a program computes with is often known only by where it lies: an
index it has compared against a bound, a count a call handed back. Here is
the least and the most a term can be, as a number without sign, by
everything the context knows: the ranges values lie in, which is at most
which, and where each term's operator makes it lie. It is the one reasoner
about whole numbers that answers; nothing is read off the way a term
happens to be written.

The least and the most are first guessed, by doing away with every term
but two that stand for them, and then shown, by the reasoner, to be so.
Only the showing is relied on.

From that: how far an address is past another, within a stretch.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

/-! ## The least and the most a sum of multiples can be -/

/-- A term standing for a number at most the sum. No sum of multiples has a
number written out among its terms, so it is none of them. -/
def underMark : Val := .lit 0

/-- A term standing for a number at least the sum. -/
def overMark : Val := .lit 1

/-- The terms the things known are of, but for the two marks. -/
def termsOf (cs : List (Lin Int)) : List Val :=
  ((cs.flatMap fun c => c.ms.map (·.2)).eraseDups).filter fun t =>
    !(t == underMark) && !(t == overMark)

/-- The things known, with a number under the sum and one over it, every
other term done away with. -/
def project (cs : List (Lin Int)) (P : Lin Int) : List (Lin Int) :=
  let all := Lin.addMul (-1) P (Lin.leaf underMark) :: Lin.addMul (-1) (Lin.leaf overMark) P :: cs
  (termsOf all).foldl (fun l t => elim t l) all

/-- The lesser of a bound and another there may not be. -/
def tighter (pick : Int → Int → Int) : Option Int → Int → Option Int
  | some x, y => some (pick x y)
  | none, y => some y

/-- The most the number under the sum is left free to be. -/
def mostOf (pr : List (Lin Int)) : Option Int :=
  pr.foldl (fun best c =>
    if coeffOf overMark c.ms = 0 && decide (0 < coeffOf underMark c.ms) then
      tighter min best ((-c.k) / coeffOf underMark c.ms)
    else best) none

/-- The least the number over the sum is left free to be. -/
def leastOf (pr : List (Lin Int)) : Option Int :=
  pr.foldl (fun best c =>
    if coeffOf underMark c.ms = 0 && decide (coeffOf overMark c.ms < 0) then
      tighter max best (-((-c.k) / (-(coeffOf overMark c.ms))))
    else best) none

/-- **The least and the most a sum of multiples can be**, the things known
being so: guessed, and then shown. -/
def boundsOf (cs : List (Lin Int)) (P : Lin Int) : Option (Int × Int) :=
  match leastOf (project cs P), mostOf (project cs P) with
  | some lo, some hi =>
    if entails (cs.length + 1) cs (Lin.from lo P) && entails (cs.length + 1) cs (P.less hi) then
      some (lo, hi)
    else none
  | _, _ => none

theorem boundsOf_le {f : Val → Int} {cs : List (Lin Int)} {P : Lin Int} {lo hi : Int}
    (h : boundsOf cs P = some (lo, hi)) (hall : AllLe f cs) : lo ≤ P.den f ∧ P.den f ≤ hi := by
  unfold boundsOf at h
  split at h
  · split at h
    · next hc =>
      cases h
      rw [Bool.and_eq_true] at hc
      have a := entails_le hc.1 hall
      have b := entails_le hc.2 hall
      rw [Lin.from_den] at a
      rw [Lin.less_den] at b
      omega
    · cases h
  · cases h

/-- The least and the most over every way things may be. -/
def boundsAll (one : List (Lin Int) → Option (Int × Int)) :
    List (List (Lin Int)) → Option (Int × Int)
  | [] => none
  | cs :: rest =>
    match one cs with
    | some b =>
      if rest.isEmpty then some b
      else
        match boundsAll one rest with
        | some b' => some (min b.1 b'.1, max b.2 b'.2)
        | none => none
    | none => none

theorem boundsAll_mem {one : List (Lin Int) → Option (Int × Int)} :
    (l : List (List (Lin Int))) → {lo hi : Int} → boundsAll one l = some (lo, hi) →
    ∀ cs ∈ l, ∃ lo' hi', one cs = some (lo', hi') ∧ lo ≤ lo' ∧ hi' ≤ hi
  | [], _, _, h => by cases h
  | c :: rest, lo, hi, h => by
    intro cs hcs
    unfold boundsAll at h
    split at h
    · next b hb =>
      split at h
      · next he =>
        cases h
        rw [List.isEmpty_iff.mp he] at hcs
        cases List.mem_singleton.mp hcs
        exact ⟨_, _, hb, Int.le_refl _, Int.le_refl _⟩
      · split at h
        · next b' hb' =>
          cases h
          rcases List.mem_cons.mp hcs with rfl | hcs
          · exact ⟨b.1, b.2, hb, Int.min_le_left _ _, Int.le_max_left _ _⟩
          · obtain ⟨lo', hi', h1, h2, h3⟩ := boundsAll_mem rest (lo := b'.1) (hi := b'.2) hb' cs hcs
            exact ⟨lo', hi', h1, Int.le_trans (Int.min_le_right _ _) h2,
              Int.le_trans h3 (Int.le_max_right _ _)⟩
        · cases h
    · cases h

/-! ## Of a term -/

/-- **Between what numbers a term lies**, as a number without sign, by
what the context knows: each way things may be, its whole number is seen
not to wrap, and the least and the most of that are found. -/
def CtxS.within (Γ : CtxS) (d : Val) : Option (Nat × Nat) :=
  match boundsAll (fun cs => (noWrap (cs.length + 1) cs d).bind (boundsOf cs))
      (know Γ.known (d.lin.ms.map (·.2))) with
  | some (lo, hi) => some (lo.toNat, hi.toNat)
  | none => none

theorem CtxS.within_den {ρ : Env} {Γ : CtxS} {d : Val} {lo hi : Nat}
    (h : Γ.within d = some (lo, hi)) {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    lo ≤ (d.den ρ).toNat ∧ (d.den ρ).toNat ≤ hi := by
  unfold CtxS.within at h
  split at h
  · next l u hb =>
    cases h
    obtain ⟨cs, hcs, hall⟩ := know_le (ρ := ρ) (fetch := fetch) (sys := sys) (Ψ' := Ψ') (n := n)
      Γ.known (d.lin.ms.map (·.2))
      (fun g hgm => hg (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩))
    obtain ⟨l', u', hone, hl, hu⟩ := boundsAll_mem _ hb cs hcs
    cases hP : noWrap (cs.length + 1) cs d with
    | none => rw [hP] at hone; cases hone
    | some P =>
      rw [hP] at hone
      have e := noWrap_eq hP hall
      have b := boundsOf_le hone hall
      have e' : natOf ρ d = ((d.den ρ).toNat : Int) := rfl
      omega
  · cases h

/-- **The most a value can be**, as a number without sign. -/
def CtxS.upper (Γ : CtxS) (v : Val) : Option Nat := (Γ.within v).map (·.2)

theorem CtxS.upper_le {ρ : Env} {Γ : CtxS} {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1)
    (v : Val) {m : Nat} (h : Γ.upper v = some m) : (v.den ρ).toNat ≤ m := by
  unfold CtxS.upper at h
  cases hw : Γ.within v with
  | none => rw [hw] at h; cases h
  | some b =>
    obtain ⟨lo, hi⟩ := b
    rw [hw] at h
    cases h
    exact (CtxS.within_den hw hg).2

/-! ## How far an address is past another -/

/-- One term less another. -/
def Val.less (a base : Val) : Val := .bin .add a (.un (.neg .w64) base)

theorem Val.less_den (ρ : Env) (a base : Val) : (a.less base).den ρ = a.den ρ - base.den ρ := by
  have e := Val.lin_den ρ (a.less base)
  have e' : (a.less base).lin = Lin.addMul 1 (base.lin.scale (-1)) a.lin := rfl
  rw [e', Lin.addMul_den, Lin.scale_den, Val.lin_den, Val.lin_den] at e
  rw [← e]
  grind

/-- **How far an address is past another, within a stretch**: from so far,
for at most so much more. -/
def CtxS.spanFrom (Γ : CtxS) (a base : Val) : Option (Nat × Nat) :=
  (Γ.within (a.less base)).map fun b => (b.1, b.2 - b.1)

theorem CtxS.spanFrom_den {ρ : Env} {Γ : CtxS} {a base : Val} {o M : Nat}
    (h : Γ.spanFrom a base = some (o, M)) {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    ∃ o', a.den ρ = base.den ρ + BitVec.ofNat 64 o' ∧ o ≤ o' ∧ o' ≤ o + M := by
  unfold CtxS.spanFrom at h
  cases hw : Γ.within (a.less base) with
  | none => rw [hw] at h; cases h
  | some b =>
    obtain ⟨lo, hi⟩ := b
    rw [hw] at h
    cases h
    have hb := CtxS.within_den hw hg
    refine ⟨((a.less base).den ρ).toNat, ?_, hb.1, by omega⟩
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, Val.less_den]
    bv_omega

end TypedAsm.U
