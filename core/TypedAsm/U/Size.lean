import TypedAsm.U.Know

/-!
# Sizes and places as terms

How many bytes a region is, and how far into it a value lies, are terms: a
region may be as many bytes as a value says. Whether one such number is at
most another is then a question for the reasoner about whole numbers, by
what is known of values. Where both are numbers written out, it is answered
by looking.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

/-- A number, as a term. -/
def litNat (k : Nat) : Val := .lit (BitVec.ofNat 64 k)

/-- What a term is worth, as a number without sign. -/
def Val.nat (ρ : Env) (v : Val) : Nat := (v.den ρ).toNat

theorem litNat_nat (ρ : Env) {k : Nat} (h : k < 2 ^ 64) : (litNat k).nat ρ = k := by
  show (BitVec.ofNat 64 k).toNat = k
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- Two terms added: a number where both are numbers. -/
def Val.plus : Val → Val → Val
  | .lit x, .lit y => .lit (x + y)
  | a, b => .add a b

theorem Val.plus_den (ρ : Env) (a b : Val) : (a.plus b).den ρ = a.den ρ + b.den ρ := by
  unfold Val.plus
  split <;> rfl

/-- One term less another. -/
def Val.less (a base : Val) : Val := .bin .add a (.un (.neg .w64) base)

theorem Val.less_den (ρ : Env) (a base : Val) : (a.less base).den ρ = a.den ρ - base.den ρ := by
  have e := Val.lin_den ρ (a.less base)
  have e' : (a.less base).lin = Lin.addMul 1 (base.lin.scale (-1)) a.lin := rfl
  rw [e', Lin.addMul_den, Lin.scale_den, Val.lin_den, Val.lin_den] at e
  rw [← e]
  grind

/-- **How far an address is past another**, as a term: a number where
taking the one from the other leaves only a number. -/
def offTerm (a base : Val) : Val :=
  match a.minus base with
  | some k => .lit k
  | none => a.less base

theorem offTerm_den (ρ : Env) (a base : Val) : a.den ρ = base.den ρ + (offTerm a base).den ρ := by
  unfold offTerm
  split
  · next k hk => exact Val.minus_den ρ hk
  · rw [Val.less_den]
    bv_omega

/-- What terms come to, added up as numbers without sign. -/
def sumNat (ρ : Env) : List Val → Nat
  | [] => 0
  | x :: xs => x.nat ρ + sumNat ρ xs

/-- What terms come to added up, where each is a number written out. -/
def litSum : List Val → Option Nat
  | [] => some 0
  | .lit a :: xs =>
    match litSum xs with
    | some s => some (a.toNat + s)
    | none => none
  | _ :: _ => none

theorem litSum_eq (ρ : Env) : (xs : List Val) → {s : Nat} → litSum xs = some s → sumNat ρ xs = s
  | [], _, h => by cases h; rfl
  | .lit a :: xs, s, h => by
    simp only [litSum] at h
    split at h
    · next s' hs =>
      cases h
      show a.toNat + sumNat ρ xs = _
      rw [litSum_eq ρ xs hs]
    · cases h
  | .var _ :: _, _, h => by cases h
  | .bvar _ _ :: _, _, h => by cases h
  | .slot .. :: _, _, h => by cases h
  | .un .. :: _, _, h => by cases h
  | .bin .. :: _, _, h => by cases h
  | .tri .. :: _, _, h => by cases h
  | .fop .. :: _, _, h => by cases h

/-- What terms come to added up, as a sum of multiples of whole numbers. -/
def wholeSum : List Val → Lin Int
  | [] => ⟨[], 0⟩
  | x :: xs => Lin.addMul 1 x.alone (wholeSum xs)

theorem wholeSum_den (ρ : Env) : (xs : List Val) →
    (wholeSum xs).den (natOf ρ) = (sumNat ρ xs : Int)
  | [] => by simp [wholeSum, Lin.den, multDen, sumNat]
  | x :: xs => by
    have e' : natOf ρ x = (x.nat ρ : Int) := rfl
    rw [wholeSum, Lin.addMul_den, wholeSum_den ρ xs, Val.alone_den]
    show _ = ((x.nat ρ + sumNat ρ xs : Nat) : Int)
    omega

/-- **Whether some numbers and so much come to at most others and so
much**, the numbers being terms: by looking, where all are written out;
else by what is known, each way things may be. -/
def sumLe (G : List (Val × TyS)) (xs : List Val) (c : Nat) (ys : List Val) (d : Nat) : Bool :=
  match litSum xs, litSum ys with
  | some a, some b => decide (a + c ≤ b + d)
  | _, _ =>
    byKnown G (xs ++ ys) fun cs =>
      entails (cs.length + 1) cs
        ((Lin.addMul (-1) (wholeSum ys) (wholeSum xs)).less ((d : Int) - (c : Int)))

theorem sumLe_den {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {xs ys : List Val}
    {c d : Nat} (h : sumLe G xs c ys d = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    sumNat ρ xs + c ≤ sumNat ρ ys + d := by
  unfold sumLe at h
  split at h
  · next a b ha hb =>
    rw [litSum_eq ρ xs ha, litSum_eq ρ ys hb]
    exact of_decide_eq_true h
  · refine byKnown_of h hg fun cs hc hall => ?_
    have b := entails_le hc hall
    rw [Lin.less_den, Lin.addMul_den, wholeSum_den, wholeSum_den] at b
    omega

/-- **Whether one number and so much is at most another and so much.** -/
def leS (G : List (Val × TyS)) (x : Val) (c : Nat) (y : Val) (d : Nat) : Bool :=
  sumLe G [x] c [y] d

theorem leS_den {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {x y : Val} {c d : Nat}
    (h : leS G x c y d = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    x.nat ρ + c ≤ y.nat ρ + d := by
  have := sumLe_den h hg
  simpa [sumNat] using this

/-- Whether so many bytes from so far in lie within so many. -/
def fitsS (G : List (Val × TyS)) (o : Val) (n : Nat) (size : Val) : Bool := leS G o n size 0

/-- Whether two stretches, each so many bytes from so far in, are apart. -/
def clearS (G : List (Val × TyS)) (o : Val) (n : Nat) (p : Val) (m : Nat) : Bool :=
  leS G o n p 0 || leS G p m o 0

theorem clearS_den {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {o p : Val} {k m : Nat}
    (h : clearS G o k p m = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    o.nat ρ + k ≤ p.nat ρ ∨ p.nat ρ + m ≤ o.nat ρ := by
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · exact .inl (leS_den h hg)
  · exact .inr (leS_den h hg)

end TypedAsm.U
