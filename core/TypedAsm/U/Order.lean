import TypedAsm.U.Lin

/-!
# Which is the larger

Things known of whole numbers, each a sum of multiples said to be at most
nought; and whether together they cannot be. One term is done away with at
a time, the one that least comes of first: where two things known say
what the term is, it is put so in the rest; else each thing that has it
one way is added to each that has it the other, so many times each that it
goes. What says nothing, or no more than another, is not kept. What is
left with no term in it and a number above nought cannot be; and then
neither could what it came from.
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

/-- Whether two lots of multiples have as many of every term. -/
def sameMs (a b : Multiples Int) : Bool :=
  a.length == b.length && a.all fun p => coeffOf p.2 b == p.1

/-- Whether one thing known says no more than another: of the same
multiples, that a number no greater added is at most nought. -/
def saysLess (c d : Lin Int) : Bool := decide (c.k ≤ d.k) && sameMs c.ms d.ms

/-- Things known, without those that say nothing or no more than another
kept. -/
def prune : List (Lin Int) → List (Lin Int) → List (Lin Int)
  | acc, [] => acc
  | acc, c :: cs =>
    if (c.ms.isEmpty && decide (c.k ≤ 0)) || acc.any (saysLess c) then prune acc cs
    else prune (c :: acc.filter fun d => !saysLess d c) cs

theorem prune_sub : (cs acc : List (Lin Int)) → ∀ x ∈ prune acc cs, x ∈ acc ∨ x ∈ cs
  | [], _, _, h => .inl h
  | c :: cs, acc, x, h => by
    unfold prune at h
    split at h
    · exact (prune_sub cs acc x h).imp_right (List.mem_cons_of_mem _)
    · rcases prune_sub cs _ x h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr List.mem_cons_self
        · exact .inl (List.mem_filter.mp h).1
      · exact .inr (List.mem_cons_of_mem _ h)

theorem prune_le {f : Val → Int} {cs : List (Lin Int)} (h : AllLe f cs) : AllLe f (prune [] cs) :=
  fun c hc => (prune_sub cs [] c hc).elim (fun h => by cases h) (h c)

/-- Whether one thing known says a sum of multiples is at most nought and
another that it is at least: each the other turned about. -/
def opposite (p q : Lin Int) : Bool :=
  p.k + q.k == 0 && p.ms.length == q.ms.length && p.ms.all fun a => coeffOf a.2 q.ms + a.1 == 0

/-- Two things known that say a sum of multiples is nought: one that it is
at most, the other that it is at least. -/
def eqPair (pos neg : List (Lin Int)) : Option (Lin Int × Lin Int) :=
  pos.findSome? fun p => (neg.find? (opposite p)).map fun q => (p, q)

theorem eqPair_mem {pos neg : List (Lin Int)} {p q : Lin Int} (h : eqPair pos neg = some (p, q)) :
    p ∈ pos ∧ q ∈ neg := by
  obtain ⟨p', hp', h⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨q', hq', h⟩ := Option.map_eq_some_iff.mp h
  cases h
  exact ⟨hp', List.mem_of_find?_eq_some hq'⟩

/-- A term done away with, of the things known that have it one way, the
other, and not at all. Where two of them say what the term is, it is put
so in the rest; else each that has it one way is added to each that has it
the other. What says nothing more is not kept. -/
def elimOf (t : Val) (pos neg rest : List (Lin Int)) : List (Lin Int) :=
  prune [] ((match eqPair pos neg with
      | some (p, q) => crossAll t [p] neg ++ crossAll t pos [q]
      | none => crossAll t pos neg) ++ rest)

theorem elimOf_le {f : Val → Int} {t : Val} {pos neg rest : List (Lin Int)}
    (hp : ∀ p ∈ pos, 0 < coeffOf t p.ms ∧ p.den f ≤ 0)
    (hn : ∀ q ∈ neg, coeffOf t q.ms < 0 ∧ q.den f ≤ 0) (hr : AllLe f rest) :
    AllLe f (elimOf t pos neg rest) := by
  refine prune_le fun c hc => ?_
  rcases List.mem_append.mp hc with hc | hc
  · split at hc
    · next p q he =>
      obtain ⟨hpm, hqm⟩ := eqPair_mem he
      rcases List.mem_append.mp hc with hc | hc
      · exact crossAll_le (fun x hx => by cases List.mem_singleton.mp hx; exact hp p hpm) hn c hc
      · exact crossAll_le hp (fun x hx => by cases List.mem_singleton.mp hx; exact hn q hqm) c hc
    · exact crossAll_le hp hn c hc
  · exact hr c hc

/-- **The things known, one term done away with.** -/
def elim (t : Val) (cs : List (Lin Int)) : List (Lin Int) :=
  elimOf t (cs.filter fun c => decide (0 < coeffOf t c.ms))
    (cs.filter fun c => decide (coeffOf t c.ms < 0)) (cs.filter fun c => decide (coeffOf t c.ms = 0))

theorem elim_le {f : Val → Int} {t : Val} {cs : List (Lin Int)} (h : AllLe f cs) :
    AllLe f (elim t cs) :=
  elimOf_le
    (fun p hp => ⟨of_decide_eq_true (List.mem_filter.mp hp).2, h p (List.mem_filter.mp hp).1⟩)
    (fun q hq => ⟨of_decide_eq_true (List.mem_filter.mp hq).2, h q (List.mem_filter.mp hq).1⟩)
    (fun c hc => h c (List.mem_filter.mp hc).1)

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

/-- How many things would come of doing away with a term, of the things
known that have it one way and the other: none, where two say what it is. -/
def costOf (pos neg : List (Lin Int)) : Nat :=
  if (eqPair pos neg).isSome then 0 else pos.length * neg.length + 1

/-- The term of some that least comes of doing away with. -/
def cheapest (cs : List (Lin Int)) : List Val → Option (Val × Nat)
  | [] => none
  | t :: ts =>
    let c := costOf (cs.filter fun c => decide (0 < coeffOf t c.ms))
      (cs.filter fun c => decide (coeffOf t c.ms < 0))
    match cheapest cs ts with
    | some b => if c ≤ b.2 then some (t, c) else some b
    | none => some (t, c)

/-- **A term the things known have, but for some to be kept: the one that
least comes of doing away with.** -/
def nextTerm (keep : List Val) (cs : List (Lin Int)) : Option Val :=
  (cheapest cs ((cs.flatMap fun c => c.ms.map (·.2)).eraseDups.filter fun t =>
    !keep.contains t)).map (·.1)

/-- **The things known, every term done away with but some to be kept**:
one at a time, so many times at most. -/
def elimBut (keep : List Val) : Nat → List (Lin Int) → List (Lin Int)
  | 0, cs => cs
  | n + 1, cs =>
    match nextTerm keep cs with
    | some t => elimBut keep n (elim t cs)
    | none => cs

theorem elimBut_le {f : Val → Int} {keep : List Val} : (n : Nat) → (cs : List (Lin Int)) →
    AllLe f cs → AllLe f (elimBut keep n cs)
  | 0, _, h => h
  | n + 1, cs, h => by
    unfold elimBut
    split
    · exact elimBut_le n _ (elim_le h)
    · exact h

/-- **Whether the things known cannot all be**: terms done away with one at
a time, until something absurd is left or no term is. -/
def refute : Nat → List (Lin Int) → Bool
  | 0, cs => absurdIn cs
  | n + 1, cs =>
    absurdIn cs ||
      match nextTerm [] cs with
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
