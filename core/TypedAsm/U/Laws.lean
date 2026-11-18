import TypedAsm.U.Open
import TypedAsm.U.RegardS

/-!
# Functions a program's author defines, and what is proved of them

A term may be what a function the author defines gives of two values. What
the function is, the program says; the checker does not look into it. It
uses it two ways.

Where both values are numbers written out, what the function gives is
computed: Lean's kernel runs the function.

And the author may give laws: that two terms are the same value, whatever
the values in them, where some of them lie in given ranges. That each law
is so is proved once, by the author, as any theorem is. Where a term the
machine came to is not the term wanted, a law may show the two to be one
value: its terms are matched against them, and what it asks is shown by
what is known.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

theorem lookup_mem {α : Type} : (l : List (Nat × α)) → (j : Nat) → (v : α) →
    l.lookup j = some v → (j, v) ∈ l
  | [], _, _, h => nomatch h
  | (i, w) :: rest, j, v, h => by
    unfold List.lookup at h
    split at h
    · next heq =>
      cases h
      rw [beq_iff_eq.mp heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem rest j v h)

/-- The term a value of the nearest family must be given for a pattern to
be a value: where the pattern is a number and the name, or a number less
the name, what that makes the name. -/
def bindB (pat got : Val) : List (Nat × Val) :=
  match pat.lin with
  | ⟨[(c, .bvar 0 j)], k⟩ =>
    if c = 1 then [(j, if k = 0 then got else .add got (.lit (-k)))]
    else if c = -1 then [(j, .add (.lit k) (.un (.neg .w64) got))]
    else []
  | _ => []

/-- What a member of a family is, as terms in lists. -/
structure OpenL where
  bs : List (Nat × Val) := []
  f : FlagsT := .lit Flags.unknown
  rest : List (Val × HeldS) := []
  tail : RestS := .none

def OpenL.opening (l : OpenL) : Opening :=
  { b := fun j => (l.bs.lookup j).getD (.lit 0), f := l.f, rest := l.rest, tail := l.tail }

def OpenL.closed (l : OpenL) : Bool :=
  (l.bs.all fun p => p.2.closedAt 0) && l.f.closedAt 0 && heldClosedAt 0 l.rest &&
    l.tail.closedAt 0

theorem OpenL.closed_opening {l : OpenL} (h : l.closed = true) : l.opening.Closed := by
  simp only [OpenL.closed, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hb, hf⟩, hr⟩, ht⟩ := h
  constructor
  · intro j
    show ((l.bs.lookup j).getD (.lit 0)).closedAt 0 = true
    cases hl : l.bs.lookup j with
    | none => rfl
    | some v => exact hb _ (lookup_mem _ _ _ hl)
  · exact hf
  · exact hr
  · exact ht

/-! ## Laws -/

/-- **A law**: two terms that are the same value whatever the values of the
nearest family are, where each of some terms lies in a range. -/
structure LawS where
  pre : List (Val × BitVec 64 × BitVec 64) := []
  lhs : Val
  rhs : Val

/-- A law is so, of given functions. -/
def LawS.Holds (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) (l : LawS) : Prop :=
  ∀ ρ : Env, ρ.fn = fns → (∀ p ∈ l.pre, Range.has ⟨p.2.1, p.2.2⟩ (p.1.den ρ)) →
    l.lhs.den ρ = l.rhs.den ρ

/-- **Every law is so**: what the author proves. -/
def LawsHold (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) (laws : List LawS) : Prop :=
  ∀ l ∈ laws, l.Holds fns

theorem LawsHold.nil (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) : LawsHold fns [] :=
  fun _ h => nomatch h

/-! ## What a function gives of numbers written out -/

/-- A function's term, a number where both values are numbers. -/
def mkApp (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) (f : Nat) : Val → Val → Val
  | .lit x, .lit y => .lit (fns f x y)
  | a, b => .app f a b

theorem mkApp_den {ρ : Env} {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64} (hfn : ρ.fn = fns)
    (f : Nat) (a b : Val) : (mkApp fns f a b).den ρ = ρ.fn f (a.den ρ) (b.den ρ) := by
  unfold mkApp
  split
  · show fns f _ _ = ρ.fn f _ _
    rw [hfn]
    rfl
  · rfl

/-- **A term with every function of numbers written out computed**, and
what is then an operator on numbers worked out. -/
def Val.evalApps (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) : Val → Val
  | .un o a => mkUn o (a.evalApps fns)
  | .bin o a b => mkBin o (a.evalApps fns) (b.evalApps fns)
  | .tri o a b c => mkTri o (a.evalApps fns) (b.evalApps fns) (c.evalApps fns)
  | .fop o fl a b => mkFop o fl (a.evalApps fns) (b.evalApps fns)
  | .app f a b => mkApp fns f (a.evalApps fns) (b.evalApps fns)
  | .lit v => .lit v
  | .var i => .var i
  | .bvar d i => .bvar d i
  | .slot s => .slot s

theorem Val.evalApps_den {ρ : Env} {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64}
    (hfn : ρ.fn = fns) : (a : Val) → (a.evalApps fns).den ρ = a.den ρ
  | .un o a => by simp only [Val.evalApps, mkUn_den, Val.den, Val.evalApps_den hfn a]
  | .bin o a b => by
    simp only [Val.evalApps, mkBin_den, Val.den, Val.evalApps_den hfn a, Val.evalApps_den hfn b]
  | .tri o a b c => by
    simp only [Val.evalApps, mkTri_den, Val.den, Val.evalApps_den hfn a, Val.evalApps_den hfn b,
      Val.evalApps_den hfn c]
  | .fop o fl a b => by
    simp only [Val.evalApps, mkFop_den, Val.den, Val.evalApps_den hfn a, Val.evalApps_den hfn b]
  | .app f a b => by
    simp only [Val.evalApps, mkApp_den hfn, Val.den, Val.evalApps_den hfn a,
      Val.evalApps_den hfn b]
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar _ _ => rfl
  | .slot _ => rfl

/-! ## A law matched against two terms -/

/-- One list, or failing anything in it another. -/
def orList {α : Type} (l r : List α) : List α := if l.isEmpty then r else l

/-- What the values of the nearest family must be for a pattern to be a
term, as far as going through the two together shows. Nothing is relied on
of the answer: the pattern, with it put in, is compared with the term. -/
def matchPat : Val → Val → List (Nat × Val)
  | .un o p, got =>
    orList (bindB (.un o p) got) (match got with
      | .un _ g => matchPat p g
      | _ => [])
  | .bin o p q, got =>
    orList (bindB (.bin o p q) got) (match got with
      | .bin _ g h => matchPat p g ++ matchPat q h
      | _ => [])
  | .tri _ p q r, got =>
    match got with
    | .tri _ g h i => matchPat p g ++ matchPat q h ++ matchPat r i
    | _ => []
  | .fop _ _ p q, got =>
    match got with
    | .fop _ _ g h => matchPat p g ++ matchPat q h
    | _ => []
  | .app _ p q, got =>
    match got with
    | .app _ g h => matchPat p g ++ matchPat q h
    | _ => []
  | pat, got => bindB pat got

/-- The values a law's two terms, matched against two terms, give the
nearest family. -/
def lawOpen (l : LawS) (a b : Val) : OpenL := { bs := matchPat l.lhs a ++ matchPat l.rhs b }

/-- **Whether a law shows two terms to be the same value**, by what is
known: with the values the matching gives put in, its two terms are the
two, and each term it asks to lie in a range is shown to. -/
def lawApplies (K : List (Val × TyS)) (l : LawS) (a b : Val) : Bool :=
  (lawOpen l a b).closed &&
    (l.lhs.open (lawOpen l a b).opening 0).same a &&
    (l.rhs.open (lawOpen l a b).opening 0).same b &&
    l.pre.all fun p => rangeHolds K (p.1.open (lawOpen l a b).opening 0) p.2.1 p.2.2

theorem lawApplies_den {ρ : Env} {Ψ' : MemTy} {n : Nat}
    {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64} (hfn : ρ.fn = fns)
    {K : List (Val × TyS)} (hg : ∀ g ∈ K, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ))
    {l : LawS} (hl : l.Holds fns) {a b : Val} (h : lawApplies K l a b = true) :
    a.den ρ = b.den ρ := by
  simp only [lawApplies, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hc, ha⟩, hb⟩, hpre⟩ := h
  have ho := OpenL.closed_opening hc
  have open_den : ∀ x : Val, (x.open (lawOpen l a b).opening 0).den ρ
      = x.den { ρ with bound := famOf ρ (lawOpen l a b).opening :: ρ.bound } :=
    fun x => Val.den_open ρ _ ho [] ρ.bound x
  rw [← Val.same_den ρ ha, ← Val.same_den ρ hb, open_den, open_den]
  refine hl _ hfn fun p hp => ?_
  rw [← open_den]
  exact rangeHolds_has (hpre p hp) hg

/-- Whether two terms are seen to be the same value by the arithmetic of
what is known: their difference is seen to be nought. It is asked only
where a range is known of some term they are made of: else nothing could
show it. So a value a comparison has pinned to a number is that number
wherever it stands. -/
def sameKnown (K : List (Val × TyS)) (a b : Val) : Bool :=
  (K.any fun g =>
    match g.2 with
    | .range _ _ => touches ((a.less b).lin.ms.map (·.2)) g
    | _ => false) &&
    rangeHolds K (a.less b) 0 0

theorem sameKnown_den {ρ : Env} {Ψ' : MemTy} {n : Nat} {K : List (Val × TyS)}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) {a b : Val}
    (h : sameKnown K a b = true) : a.den ρ = b.den ρ := by
  unfold sameKnown at h
  rw [Bool.and_eq_true] at h
  have hr : (a.less b).den ρ - 0 ≤ (0 : BitVec 64) - 0 := rangeHolds_has h.2 hg
  rw [Val.less_den] at hr
  have hle : (a.den ρ - b.den ρ - 0).toNat ≤ ((0 : BitVec 64) - 0).toNat := BitVec.le_def.mp hr
  have h0 : ((0 : BitVec 64) - 0).toNat = 0 := by decide
  have h1 : a.den ρ - b.den ρ - 0 = a.den ρ - b.den ρ := by simp
  rw [h0, h1] at hle
  have hz : a.den ρ - b.den ρ = 0 := BitVec.eq_of_toNat_eq (by
    have : (0 : BitVec 64).toNat = 0 := rfl
    omega)
  have e : a.den ρ = a.den ρ - b.den ρ + b.den ρ := by
    rw [BitVec.sub_add_cancel]
  rw [e, hz]
  simp

/-- **Whether two terms are the same value**, by the functions and the laws
of a program and what is known: as terms; or once every function of numbers
is computed; or by a law, read either way; or by the arithmetic of what is
known. -/
def sameBy (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) (laws : List LawS)
    (K : List (Val × TyS)) (a b : Val) : Bool :=
  a.same b || (a.evalApps fns).same (b.evalApps fns) ||
    (laws.any fun l =>
      lawApplies K l (a.evalApps fns) (b.evalApps fns) ||
        lawApplies K l (b.evalApps fns) (a.evalApps fns)) ||
    sameKnown K a b

theorem sameBy_den {ρ : Env} {Ψ' : MemTy} {n : Nat}
    {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64} (hfn : ρ.fn = fns) {laws : List LawS}
    (hl : LawsHold fns laws) {K : List (Val × TyS)}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) {a b : Val}
    (h : sameBy fns laws K a b = true) : a.den ρ = b.den ρ := by
  simp only [sameBy, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ((h | h) | ⟨l, hlm, h | h⟩) | h
  rotate_right
  · exact sameKnown_den hg h
  · exact Val.same_den ρ h
  · rw [← Val.evalApps_den hfn a, ← Val.evalApps_den hfn b]
    exact Val.same_den ρ h
  · rw [← Val.evalApps_den hfn a, ← Val.evalApps_den hfn b]
    exact lawApplies_den hfn hg (hl l hlm) h
  · rw [← Val.evalApps_den hfn a, ← Val.evalApps_den hfn b]
    exact (lawApplies_den hfn hg (hl l hlm) h).symm

/-! ## A context with its functions of numbers computed -/

variable {Ψ : MemTy}

/-- A sum, written out from what it comes apart into: each term once, and
the numbers added as one. A term taken some number of times other than
once, or once away, is left as it was written. -/
def Val.gather (v : Val) : Val :=
  if v.lin.ms.all (fun p => p.1 = 1 || p.1 = -1) then
    match v.lin.ms.map (fun p => if p.1 = 1 then p.2 else Val.un (.neg .w64) p.2) with
    | [] => .lit v.lin.k
    | t :: ts =>
      if v.lin.k = 0 then ts.foldl (fun acc x => .bin .add acc x) t
      else .bin .add (ts.foldl (fun acc x => .bin .add acc x) t) (.lit v.lin.k)
  else v

/-- A context with each value a function gives of numbers worked out, and
each sum gathered: so that a value does not grow by what is added to it and
taken away again, as the stack pointer's does at each call and return. -/
def CtxS.evalApps (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) (Γ : CtxS) : CtxS :=
  { Γ with
    regs := Γ.regs.map fun v => (v.evalApps fns).gather
    held := Γ.held.map fun b =>
      (b.1.gather,
        ⟨b.2.size.gather, b.2.slots.map fun p => (p.1.gather, (p.2.evalApps fns).gather)⟩) }

/-- The same, where the context may be regarded so and mentions no name
from `k` on; else the context. So where a walk starts: a value a function
gives of numbers is then a number. -/
def evalFor (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) (Γ : CtxS) (k : Nat) : CtxS :=
  if (Γ.evalApps fns).under k && regardWith (sameBy fns []) noEnt Γ (Γ.evalApps fns) then
    Γ.evalApps fns
  else Γ

theorem evalFor_under {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64} {Γ : CtxS} {k : Nat}
    (hu : Γ.under k = true) : (evalFor fns Γ k).under k = true := by
  unfold evalFor
  split
  · next hc => exact (Bool.and_eq_true _ _ |>.mp hc).1
  · exact hu

theorem evalFor_regards {ρ : Env} {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64}
    (hfn : ρ.fn = fns) (Γ : CtxS) (k : Nat) :
    Regards fetch sys Ψ (Γ.den ρ) ((evalFor fns Γ k).den ρ) := by
  unfold evalFor
  split
  · next hc =>
    exact regardWith_sound noEnt_sound ρ
      (fun _ _ hg _ _ hs => sameBy_den hfn (LawsHold.nil fns) hg hs) (Bool.and_eq_true _ _ |>.mp hc).2
  · exact Regards.refl _

end TypedAsm.U
