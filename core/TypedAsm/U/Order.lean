import TypedAsm.U.Lin

/-!
# Which is the larger

Things known of whole numbers, each a sum of multiples said to be at most
nought; and whether together they cannot be. One term is done away with at
a time: each thing that has it one way is added to each that has it the
other, so many times each that it goes. What is left with no term in it and
a number above nought cannot be; and then neither could what it came from.
-/

namespace TypedAsm.U

open TypedAsm

/-- How many of a term there are. -/
def coeffOf (t : Val) : Multiples Int → Int
  | [] => 0
  | p :: ps => if p.2 = t then p.1 else coeffOf t ps

/-- All hold: each is at most nought. -/
def AllLe (f : Val → Int) (cs : List (Lin Int)) : Prop := ∀ c ∈ cs, c.den f ≤ 0

/-- Each of the first with each of the second, so many times each that the
term goes. -/
def crossAll (t : Val) (pos neg : List (Lin Int)) : List (Lin Int) :=
  pos.flatMap fun p => neg.map fun q =>
    Lin.addMul (-(coeffOf t q.ms)) p (q.scale (coeffOf t p.ms))

theorem crossAll_le {f : Val → Int} {t : Val} {pos neg : List (Lin Int)}
    (hp : ∀ p ∈ pos, 0 < coeffOf t p.ms ∧ p.den f ≤ 0)
    (hn : ∀ q ∈ neg, coeffOf t q.ms < 0 ∧ q.den f ≤ 0) : AllLe f (crossAll t pos neg) := by
  intro c hc
  simp only [crossAll, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨p, hpm, q, hqm, rfl⟩ := hc
  rw [Lin.addMul_den, Lin.scale_den]
  have h1 := hp p hpm
  have h2 := hn q hqm
  have a : -(coeffOf t q.ms) * p.den f ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h1.2
  have b : coeffOf t p.ms * q.den f ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (by omega) h2.2
  omega

/-- The things known, one term done away with. -/
def elim (t : Val) (cs : List (Lin Int)) : List (Lin Int) :=
  crossAll t (cs.filter fun c => decide (0 < coeffOf t c.ms))
      (cs.filter fun c => decide (coeffOf t c.ms < 0)) ++
    cs.filter fun c => decide (coeffOf t c.ms = 0)

theorem elim_le {f : Val → Int} {t : Val} {cs : List (Lin Int)} (h : AllLe f cs) :
    AllLe f (elim t cs) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact crossAll_le
      (fun p hp => ⟨of_decide_eq_true (List.mem_filter.mp hp).2, h p (List.mem_filter.mp hp).1⟩)
      (fun q hq => ⟨of_decide_eq_true (List.mem_filter.mp hq).2, h q (List.mem_filter.mp hq).1⟩)
      c hc
  · exact h c (List.mem_filter.mp hc).1

/-- Whether one of them, with no term in it, is a number above nought. -/
def absurdIn (cs : List (Lin Int)) : Bool := cs.any fun c => c.ms.isEmpty && decide (0 < c.k)

theorem absurdIn_false {f : Val → Int} {cs : List (Lin Int)} (h : absurdIn cs = true)
    (hall : AllLe f cs) : False := by
  simp only [absurdIn, List.any_eq_true, Bool.and_eq_true, List.isEmpty_iff,
    decide_eq_true_eq] at h
  obtain ⟨c, hc, hms, hk⟩ := h
  have := hall c hc
  simp only [Lin.den, hms, multDen] at this
  omega

/-- A term one of them has, if any does. -/
def someTerm : List (Lin Int) → Option Val
  | [] => none
  | c :: cs =>
    match c.ms with
    | p :: _ => some p.2
    | [] => someTerm cs

/-- **Whether the things known cannot all be**: terms done away with one at
a time, until something absurd is left or no term is. -/
def refute : Nat → List (Lin Int) → Bool
  | 0, cs => absurdIn cs
  | n + 1, cs =>
    absurdIn cs ||
      match someTerm cs with
      | some t => refute n (elim t cs)
      | none => false

theorem refute_false {f : Val → Int} : (n : Nat) → (cs : List (Lin Int)) → refute n cs = true →
    AllLe f cs → False
  | 0, cs, h, hall => absurdIn_false h hall
  | n + 1, cs, h, hall => by
    simp only [refute, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurdIn_false h hall
    · split at h
      · next t _ => exact refute_false n _ h (elim_le hall)
      · cases h

/-- **Whether, the things known being so, a sum of multiples is at most
nought**: were it not, it would be at least one; and that with the things
known cannot be. -/
def entails (fuel : Nat) (cs : List (Lin Int)) (g : Lin Int) : Bool :=
  refute fuel (Lin.addMul (-1) g ⟨[], 1⟩ :: cs)

theorem entails_le {f : Val → Int} {fuel : Nat} {cs : List (Lin Int)} {g : Lin Int}
    (h : entails fuel cs g = true) (hall : AllLe f cs) : g.den f ≤ 0 := by
  apply Classical.byContradiction
  intro hg
  refine refute_false (f := f) fuel _ h fun c hc => ?_
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [Lin.addMul_den]
    simp only [Lin.den, multDen] at hg ⊢
    omega
  · exact hall c hc

end TypedAsm.U
