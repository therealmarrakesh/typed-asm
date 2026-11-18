import TypedAsm.U.Ints
import TypedAsm.U.Basic
import TypedAsm.U.TyS

/-!
# What is known of how large values are

The ranges known of terms, gathered as things known of whole numbers; and
whether a sum of multiples is then at most nought. A range known of a term
says something of the term's whole number once that is seen not to wrap; a
range that goes round says one of two things, and each is followed.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

/-- A number less a sum of multiples. -/
def Lin.from (c : Int) (P : Lin Int) : Lin Int := Lin.addMul (-1) P ⟨[], c⟩

theorem Lin.from_den (f : Val → Int) (c : Int) (P : Lin Int) : (Lin.from c P).den f = c - P.den f := by
  rw [Lin.from, Lin.addMul_den]
  simp only [Lin.den, multDen]
  omega

/-- A sum of multiples less a number. -/
def Lin.less (P : Lin Int) (c : Int) : Lin Int := ⟨P.ms, P.k - c⟩

theorem Lin.less_den (f : Val → Int) (c : Int) (P : Lin Int) : (P.less c).den f = P.den f - c := by
  simp only [Lin.den, Lin.less]
  omega

theorem natOf_lt (ρ : Env) (t : Val) : natOf ρ t < 18446744073709551616 := by
  have := (t.den ρ).isLt
  show ((t.den ρ).toNat : Int) < _
  omega

theorem natOf_nonneg (ρ : Env) (t : Val) : 0 ≤ natOf ρ t := Int.natCast_nonneg _

theorem Range.has_nat {lo hi v : BitVec 64} (h : Range.has ⟨lo, hi⟩ v) :
    if lo ≤ hi then lo.toNat ≤ v.toNat ∧ v.toNat ≤ hi.toNat
    else lo.toNat ≤ v.toNat ∨ v.toNat ≤ hi.toNat := by
  simp only [Range.has] at h
  split <;> bv_omega

theorem Range.of_nat {lo hi v : BitVec 64}
    (h : if lo ≤ hi then lo.toNat ≤ v.toNat ∧ v.toNat ≤ hi.toNat
      else lo.toNat ≤ v.toNat ∨ v.toNat ≤ hi.toNat) : Range.has ⟨lo, hi⟩ v := by
  simp only [Range.has]
  split at h <;> bv_omega

/-- What is so of a term whatever is known: it is a value of the machine,
and lies where its operator makes it lie. -/
def atomCs (G : List (Val × TyS)) (t : Val) : List (Lin Int) :=
  [⟨[(-1, t)], 0⟩, ⟨[(1, t)], -18446744073709551615⟩] ++
    if (t.boundIn G).lo ≤ (t.boundIn G).hi then
      [⟨[(-1, t)], (t.boundIn G).lo.toNat⟩, ⟨[(1, t)], -((t.boundIn G).hi.toNat : Int)⟩]
    else []

theorem atomCs_le {ρ : Env} {G : List (Val × TyS)} (hG : RangesHold ρ G) (t : Val) :
    AllLe (natOf ρ) (atomCs G t) := by
  have h0 := natOf_nonneg ρ t
  have h1 := natOf_lt ρ t
  have hb := Range.has_nat (lo := (t.boundIn G).lo) (hi := (t.boundIn G).hi) (Val.boundIn_has hG t)
  have e : natOf ρ t = ((t.den ρ).toNat : Int) := rfl
  intro c hc
  unfold atomCs at hc
  generalize t.boundIn G = b at hb hc
  obtain ⟨lo, hi⟩ := b
  by_cases hle : lo ≤ hi
  · simp only [hle, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hb hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp only [Lin.den, multDen] <;> omega
  · simp only [hle, ↓reduceIte, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp only [Lin.den, multDen] <;> omega

theorem add_res32 (a b : BitVec 32) : (addCarry a b false).1 = a + b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt
  simp [addCarry, BitVec.toNat_add, BitVec.toNat_setWidth]

theorem sub_res32 (a b : BitVec 32) : (subBorrow a b false).1 = a - b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt
  simp [subBorrow, BitVec.toNat_sub, BitVec.toNat_setWidth]
  omega

/-- **The low `k` bits of a term, as a whole number**: the term read with its
sign, so many twos to the `k` taken away as often as they go. So of every
value that is the low part of another. -/
theorem low_int (ρ : Env) (x : Val) {k : Nat} (hk : k ≤ 64) :
    (((x.den ρ).toNat % 2 ^ k : Nat) : Int) = (x.int true).den (natOf ρ) % 2 ^ k := by
  have ex := Val.int_den ρ true x
  generalize (x.int true).den (natOf ρ) = X at *
  have h1 : ((x.den ρ).toNat : Int) = X % 2 ^ 64 := by
    rw [← ex, BitVec.toNat_ofInt]
    have := Int.emod_nonneg X (by decide : (2 : Int) ^ 64 ≠ 0)
    omega
  have hd : (2 : Int) ^ k ∣ 2 ^ 64 := by exact_mod_cast Nat.pow_dvd_pow 2 hk
  rw [Int.natCast_emod, h1]
  push_cast
  exact Int.emod_emod_of_dvd _ hd

/-- A mask of the low `k` bits: what `k` is, where a number written out is
one and no more than a width holds. -/
def maskBits (w : Width) (m : BitVec 64) : Option Nat :=
  if m.toNat + 1 = 2 ^ Nat.log2 (m.toNat + 1) ∧ Nat.log2 (m.toNat + 1) ≤ w.bits then
    some (Nat.log2 (m.toNat + 1))
  else none

theorem maskBits_spec {w : Width} {m : BitVec 64} {k : Nat} (h : maskBits w m = some k) :
    m.toNat = 2 ^ k - 1 ∧ k ≤ w.bits := by
  unfold maskBits at h
  split at h
  · next hc => cases h; exact ⟨by omega, hc.2⟩
  · cases h

/-- What a term is the low part of, as a whole number, and how much the
part holds: a sum or difference of low halves is the low half of the sum or
difference itself, each number with its sign; a value cut to a width, or
widened with noughts from a narrow one, or masked to its low bits, the low
part of the value. -/
def halfOf : Val → Option (Lin Int × Int)
  | .fop (.alu .add .w32) _ x y => some (Lin.addMul 1 (x.int true) (y.int true), 4294967296)
  | .fop (.alu .sub .w32) _ x y => some (Lin.addMul (-1) (y.int true) (x.int true), 4294967296)
  | .un (.trunc w) x => some (x.int true, 2 ^ w.bits)
  | .un (.zx _ sw) x => some (x.int true, 2 ^ sw.bits)
  | .un .low8 x => some (x.int true, 256)
  | .un .low16 x => some (x.int true, 65536)
  | .fop (.alu .and w) _ x (.lit m) => (maskBits w m).map fun k => (x.int true, 2 ^ k)
  | _ => none

theorem halfOf_mod (ρ : Env) {t : Val} {E : Lin Int} {M : Int} (h : halfOf t = some (E, M)) :
    0 < M ∧ natOf ρ t = E.den (natOf ρ) % M := by
  have low : ∀ (x : Val) (k : Nat), k ≤ 64 → (t.den ρ).toNat = (x.den ρ).toNat % 2 ^ k →
      E = x.int true → M = 2 ^ k → 0 < M ∧ natOf ρ t = E.den (natOf ρ) % M := by
    intro x k hk ht hE hM
    subst hE hM
    refine ⟨by exact_mod_cast Nat.two_pow_pos k, ?_⟩
    show ((t.den ρ).toNat : Int) = _
    rw [ht]
    exact_mod_cast low_int ρ x hk
  unfold halfOf at h
  split at h
  · next fl x y =>
    cases h
    refine ⟨by omega, ?_⟩
    have ex := Val.int_den ρ true x
    have ey := Val.int_den ρ true y
    rw [Lin.addMul_den]
    generalize (x.int true).den (natOf ρ) = X at *
    generalize (y.int true).den (natOf ρ) = Y at *
    show ((BitVec.setWidth 64 (addCarry (BitVec.setWidth 32 (x.den ρ))
      (BitVec.setWidth 32 (y.den ρ)) false).1).toNat : Int) = _
    rw [add_res32, ← ex, ← ey]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofInt]
    omega
  · next fl x y =>
    cases h
    refine ⟨by omega, ?_⟩
    have ex := Val.int_den ρ true x
    have ey := Val.int_den ρ true y
    rw [Lin.addMul_den]
    generalize (x.int true).den (natOf ρ) = X at *
    generalize (y.int true).den (natOf ρ) = Y at *
    show ((BitVec.setWidth 64 (subBorrow (BitVec.setWidth 32 (x.den ρ))
      (BitVec.setWidth 32 (y.den ρ)) false).1).toNat : Int) = _
    rw [sub_res32, ← ex, ← ey]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofInt]
    omega
  · next w x =>
    cases h
    refine low x w.bits (by cases w <;> decide) ?_ rfl rfl
    show (wide (BitVec.setWidth w.bits (x.den ρ))).toNat = _
    rw [toNat_wide, BitVec.toNat_setWidth]
  · next w sw x =>
    cases h
    refine low x sw.bits (by cases sw <;> decide) ?_ rfl rfl
    show (wide (w := w) ((BitVec.setWidth sw.bits (x.den ρ)).setWidth w.bits)).toNat = _
    rw [toNat_wide, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by omega) (by cases w <;> cases sw <;> decide)))
  · next x =>
    cases h
    refine low x 8 (by decide) ?_ rfl rfl
    show ((BitVec.setWidth 8 (x.den ρ)).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 8)) (by decide))]
  · next x =>
    cases h
    refine low x 16 (by decide) ?_ rfl rfl
    show ((BitVec.setWidth 16 (x.den ρ)).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 16)) (by decide))]
  · next w fl x m =>
    obtain ⟨k, hk, hE⟩ := Option.map_eq_some_iff.mp h
    cases hE
    obtain ⟨hm, hkw⟩ := maskBits_spec hk
    refine low x k (Nat.le_trans hkw (by cases w <;> decide)) ?_ rfl rfl
    show (wide (BitVec.setWidth w.bits (x.den ρ) &&& BitVec.setWidth w.bits m)).toNat = _
    have hmw : m.toNat < 2 ^ w.bits := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) hkw
      have := Nat.two_pow_pos k
      omega
    rw [toNat_wide, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt hmw, hm, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hkw)]
  · cases h

/-- That one sum of multiples is another: each at most the other. -/
def eqCs (A B : Lin Int) : List (Lin Int) := [Lin.addMul (-1) B A, Lin.addMul (-1) A B]

/-- **The ways a low part may be**: what it is the low part of, itself; or
that, a wrap more or less; or what it is the low part of is further off
than that, and nothing more is said. Of any other term, the one way, saying
nothing. -/
def waysOf (t : Val) : List (List (Lin Int)) :=
  match halfOf t with
  | none => [[]]
  | some (E, M) =>
    [eqCs ⟨[(1, t)], 0⟩ E,
     eqCs ⟨[(1, t)], 0⟩ ⟨E.ms, E.k + M⟩,
     eqCs ⟨[(1, t)], 0⟩ ⟨E.ms, E.k - M⟩,
     [Lin.from (2 * M) E],
     [⟨E.ms, E.k + M + 1⟩]]

theorem waysOf_le (ρ : Env) (t : Val) : ∃ w ∈ waysOf t, AllLe (natOf ρ) w := by
  unfold waysOf
  split
  · exact ⟨[], List.mem_singleton.mpr rfl, fun c hc => nomatch hc⟩
  · next E M hE =>
    obtain ⟨hM, hm⟩ := halfOf_mod ρ hE
    generalize hv : E.den (natOf ρ) = V at hm
    have hV : multDen (natOf ρ) E.ms + E.k = V := hv
    have hlo := Int.emod_nonneg V (Int.ne_of_gt hM)
    have hhi := Int.emod_lt_of_pos V hM
    by_cases h0 : 0 ≤ V ∧ V < M
    · have e : V % M = V := Int.emod_eq_of_lt h0.1 h0.2
      refine ⟨_, List.mem_cons_self, fun c hc => ?_⟩
      simp only [eqCs, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rw [Lin.addMul_den] <;> simp only [Lin.den, multDen] <;> omega
    · by_cases h1 : -M ≤ V ∧ V < 0
      · have e : V % M = V + M := by
          rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
        refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun c hc => ?_⟩
        simp only [eqCs, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rw [Lin.addMul_den] <;> simp only [Lin.den, multDen] <;> omega
      · by_cases h2 : M ≤ V ∧ V < 2 * M
        · have e : V % M = V - M := by
            rw [← Int.sub_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
          refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
            fun c hc => ?_⟩
          simp only [eqCs, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> rw [Lin.addMul_den] <;> simp only [Lin.den, multDen] <;>
            omega
        · by_cases h3 : 2 * M ≤ V
          · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self)), fun c hc => ?_⟩
            rw [List.mem_singleton.mp hc, Lin.from_den]
            omega
          · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))), fun c hc => ?_⟩
            rw [List.mem_singleton.mp hc]
            simp only [Lin.den]
            omega

/-- Each way things may be, with each way each of some terms may be: but
for the ways that cannot be. -/
def addWays (fuel : Nat) : List Val → List (List (Lin Int)) → List (List (Lin Int))
  | [], K => K
  | t :: ts, K =>
    match halfOf t with
    | none => addWays fuel ts K
    | some _ =>
      addWays fuel ts
        ((K.flatMap fun cs => (waysOf t).map (· ++ cs)).filter fun cs => !refute fuel cs)

theorem addWays_le {ρ : Env} {fuel : Nat} : (ts : List Val) → (K : List (List (Lin Int))) →
    (∃ cs ∈ K, AllLe (natOf ρ) cs) → ∃ cs ∈ addWays fuel ts K, AllLe (natOf ρ) cs
  | [], _, h => h
  | t :: ts, K, ⟨cs, hcs, hall⟩ => by
    unfold addWays
    split
    · exact addWays_le ts K ⟨cs, hcs, hall⟩
    · obtain ⟨w, hw, hwall⟩ := waysOf_le ρ t
      have hboth : AllLe (natOf ρ) (w ++ cs) := fun c hc =>
        (List.mem_append.mp hc).elim (hwall c) (hall c)
      refine addWays_le ts _ ⟨w ++ cs, List.mem_filter.mpr
        ⟨List.mem_flatMap.mpr ⟨cs, hcs, List.mem_map.mpr ⟨w, hw, rfl⟩⟩, ?_⟩, hboth⟩
      cases hr : refute fuel (w ++ cs) with
      | false => rfl
      | true => exact (refute_false fuel _ hr hboth).elim

/-- A term, and the terms it is a sum or difference of low halves of, and
those of them: so far in. -/
def inside : Nat → Val → List Val
  | 0, t => [t]
  | n + 1, t =>
    t :: match halfOf t with
      | some E => E.1.ms.flatMap fun p => inside n p.2
      | none => []

/-- The terms a term is made of, with those inside them. -/
def termsIn (v : Val) : List Val := v.lin.ms.flatMap fun p => inside 3 p.2

/-- **A term's whole number, where the things known show it does not
wrap**: with the number added read without its sign, or with. -/
def noWrap (fuel : Nat) (cs : List (Lin Int)) (u : Val) : Option (Lin Int) :=
  [false, true].findSome? fun s =>
    if entails fuel cs (Lin.from 0 (u.int s)) &&
        entails fuel cs ((u.int s).less 18446744073709551615) then some (u.int s) else none

theorem noWrap_eq {ρ : Env} {fuel : Nat} {cs : List (Lin Int)} {u : Val} {P : Lin Int}
    (h : noWrap fuel cs u = some P) (hall : AllLe (natOf ρ) cs) :
    natOf ρ u = P.den (natOf ρ) := by
  obtain ⟨s, _, hs⟩ := List.exists_of_findSome?_eq_some h
  split at hs
  · next hc =>
    cases hs
    rw [Bool.and_eq_true] at hc
    have a := entails_le hc.1 hall
    have b := entails_le hc.2 hall
    rw [Lin.from_den] at a
    rw [Lin.less_den] at b
    exact Val.int_eq ρ s u (by omega) (by omega)
  · cases hs

/-- The things known, and with them what a range known of a term says:
where the term is seen not to wrap, that its whole number lies in the
range; one way or the other, where the range goes round. -/
def addFact (fuel : Nat) (u : Val) (lo hi : BitVec 64) (cs : List (Lin Int)) :
    List (List (Lin Int)) :=
  match noWrap fuel cs u with
  | some P =>
    if lo ≤ hi then [Lin.from lo.toNat P :: P.less hi.toNat :: cs]
    else [Lin.from lo.toNat P :: cs, P.less hi.toNat :: cs]
  | none => [cs]

theorem addFact_le {ρ : Env} {fuel : Nat} {u : Val} {lo hi : BitVec 64} {cs : List (Lin Int)}
    (hall : AllLe (natOf ρ) cs) (hu : Range.has ⟨lo, hi⟩ (u.den ρ)) :
    ∃ cs' ∈ addFact fuel u lo hi cs, AllLe (natOf ρ) cs' := by
  unfold addFact
  split
  · next P hP =>
    have e := noWrap_eq hP hall
    have hn := Range.has_nat hu
    have e' : natOf ρ u = ((u.den ρ).toNat : Int) := rfl
    split
    · next hle =>
      simp only [hle, ↓reduceIte] at hn
      refine ⟨_, List.mem_singleton.mpr rfl, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [Lin.from_den]; omega
      · rcases List.mem_cons.mp hc with rfl | hc
        · rw [Lin.less_den]; omega
        · exact hall c hc
    · next hle =>
      simp only [hle, ↓reduceIte] at hn
      rcases hn with hn | hn
      · refine ⟨_, List.mem_cons_self, fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [Lin.from_den]; omega
        · exact hall c hc
      · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [Lin.less_den]; omega
        · exact hall c hc
  · exact ⟨cs, List.mem_singleton.mpr rfl, hall⟩

/-- The things known, and with them what one term's being at most another,
or less, says: where neither is seen to wrap, that of their whole numbers. -/
def addUpTo (fuel : Nat) (u t : Val) (strict : Bool) (cs : List (Lin Int)) : List (Lin Int) :=
  match noWrap fuel cs u, noWrap fuel cs t with
  | some Pu, some Pt => Lin.addMul (-1) Pt ⟨Pu.ms, Pu.k + (if strict then 1 else 0)⟩ :: cs
  | _, _ => cs

theorem addUpTo_le {ρ : Env} {fuel : Nat} {u t : Val} {strict : Bool} {cs : List (Lin Int)}
    (hall : AllLe (natOf ρ) cs)
    (hu : if strict then u.den ρ < t.den ρ else u.den ρ ≤ t.den ρ) :
    AllLe (natOf ρ) (addUpTo fuel u t strict cs) := by
  unfold addUpTo
  split
  · next Pu Pt hPu hPt =>
    have eu := noWrap_eq hPu hall
    have et := noWrap_eq hPt hall
    have e1 : natOf ρ u = ((u.den ρ).toNat : Int) := rfl
    have e2 : natOf ρ t = ((t.den ρ).toNat : Int) := rfl
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [Lin.addMul_den]
      simp only [Lin.den] at eu et ⊢
      cases strict
      · simp only [Bool.false_eq_true, ↓reduceIte] at hu ⊢
        have := BitVec.le_def.mp hu
        omega
      · simp only [↓reduceIte] at hu ⊢
        have := BitVec.lt_def.mp hu
        omega
    · exact hall c hc
  · exact hall

/-- Each way things may be, with what the things known of ranges say, and
of one term's being at most another. -/
def addFacts (fuel : Nat) : List (Val × TyS) → List (List (Lin Int)) → List (List (Lin Int))
  | [], K => K
  | (u, .range lo hi) :: G, K => addFacts fuel G (K.flatMap (addFact fuel u lo hi))
  | (u, .upTo t strict) :: G, K => addFacts fuel G (K.map (addUpTo fuel u t strict))
  | _ :: G, K => addFacts fuel G K

theorem addFacts_le {ρ : Env} {Ψ' : MemTy} {n : Nat} {fuel : Nat} :
    (G : List (Val × TyS)) → (K : List (List (Lin Int))) →
    (∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) →
    (∃ cs ∈ K, AllLe (natOf ρ) cs) → ∃ cs ∈ addFacts fuel G K, AllLe (natOf ρ) cs
  | [], K, _, h => h
  | (u, τ) :: G, K, hg, ⟨cs, hcs, hall⟩ => by
    have hrest : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ) :=
      fun g hgm => hg g (List.mem_cons_of_mem _ hgm)
    cases τ with
    | range lo hi =>
      have hu : Range.has ⟨lo, hi⟩ (u.den ρ) := hasTy_range.mp (hg (u, .range lo hi) List.mem_cons_self)
      obtain ⟨cs', hcs', hall'⟩ := addFact_le (fuel := fuel) hall hu
      exact addFacts_le G _ hrest ⟨cs', List.mem_flatMap.mpr ⟨cs, hcs, hcs'⟩, hall'⟩
    | upTo t strict =>
      have hu := hasTy_upTo.mp (hg (u, .upTo t strict) List.mem_cons_self)
      exact addFacts_le G _ hrest
        ⟨_, List.mem_map.mpr ⟨cs, hcs, rfl⟩, addUpTo_le (fuel := fuel) hall hu⟩
    | _ => exact addFacts_le G K hrest ⟨cs, hcs, hall⟩

/-- The terms the ranges known are of are made of. -/
def factAtoms : List (Val × TyS) → List Val
  | [] => []
  | (u, .range _ _) :: G => termsIn u ++ factAtoms G
  | (u, .upTo t _) :: G => termsIn u ++ termsIn t ++ factAtoms G
  | _ :: G => factAtoms G

/-- Whether a thing known is of a term made of one of some terms. -/
def touches (as : List Val) (f : Val × TyS) : Bool := (factAtoms [f]).any fun a => as.contains a

/-- **The things known that bear on some terms**: those of terms made of
them, and so on through the terms those are made of, till no more are
found. What is known of other terms says nothing of these. -/
def cone : Nat → List (Val × TyS) → List Val → List (Val × TyS)
  | 0, G, as => G.filter (touches as)
  | n + 1, G, as =>
    if (as ++ factAtoms (G.filter (touches as))).eraseDups.length = as.eraseDups.length then
      G.filter (touches as)
    else cone n G (as ++ factAtoms (G.filter (touches as))).eraseDups

theorem cone_sub : (n : Nat) → (G : List (Val × TyS)) → (as : List Val) →
    ∀ g ∈ cone n G as, g ∈ G
  | 0, _, _, _, h => (List.mem_filter.mp h).1
  | n + 1, G, as, g, h => by
    unfold cone at h
    split at h
    · exact (List.mem_filter.mp h).1
    · exact cone_sub n G _ g h

/-- Each way things may be, by all of some ranges known: what is so of
each term whatever is known, and what the ranges say; gone through twice,
for a range may be of a term another shows not to wrap; and between, each
way a low part may be that the ranges leave open. -/
def knowAll (G : List (Val × TyS)) (more : List Val) : List (List (Lin Int)) :=
  addFacts ((factAtoms G ++ more).length + 1) G
    (addWays ((factAtoms G ++ more).length + 1) (factAtoms G ++ more).eraseDups
      (addFacts ((factAtoms G ++ more).length + 1) G
        [(factAtoms G ++ more).eraseDups.flatMap (atomCs G)]))

/-- **Each way things may be, by the ranges known that bear on some
terms.** -/
def know (G : List (Val × TyS)) (more : List Val) : List (List (Lin Int)) :=
  knowAll (cone G.length G (more.flatMap (inside 3))) (more.flatMap (inside 3))

theorem know_le {ρ : Env} {Ψ' : MemTy} {n : Nat} (G : List (Val × TyS)) (more : List Val)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    ∃ cs ∈ know G more, AllLe (natOf ρ) cs :=
  have hg' : ∀ g ∈ cone G.length G (more.flatMap (inside 3)),
      HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ) :=
    fun g hgm => hg g (cone_sub _ _ _ g hgm)
  addFacts_le _ _ hg' (addWays_le _ _ (addFacts_le _ _ hg'
    ⟨_, List.mem_singleton.mpr rfl, fun c hc => by
      obtain ⟨t, _, hc⟩ := List.mem_flatMap.mp hc
      exact atomCs_le (rangesHold_of hg') t c hc⟩))

/-- **Whether a term lies in a range, by the ranges known**, each way
things may be: its whole number, seen not to wrap, lies there; on one side
or the other, where the range goes round. -/
def rangeHolds (G : List (Val × TyS)) (v : Val) (lo hi : BitVec 64) : Bool :=
  (know G (v.lin.ms.map (·.2))).all fun cs =>
    match noWrap (cs.length + 1) cs v with
    | some P =>
      if lo ≤ hi then
        entails (cs.length + 1) cs (Lin.from lo.toNat P) &&
          entails (cs.length + 1) cs (P.less hi.toNat)
      else
        entails (cs.length + 1) cs (Lin.from lo.toNat P) ||
          entails (cs.length + 1) cs (P.less hi.toNat)
    | none => false

theorem rangeHolds_has {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {v : Val}
    {lo hi : BitVec 64} (h : rangeHolds G v lo hi = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    Range.has ⟨lo, hi⟩ (v.den ρ) := by
  obtain ⟨cs, hcs, hall⟩ := know_le (ρ := ρ) G (v.lin.ms.map (·.2)) hg
  have hc := List.all_eq_true.mp h cs hcs
  split at hc
  · next P hP =>
    have e := noWrap_eq hP hall
    have e' : natOf ρ v = ((v.den ρ).toNat : Int) := rfl
    refine Range.of_nat ?_
    split at hc
    · next hle =>
      rw [Bool.and_eq_true] at hc
      have a := entails_le hc.1 hall
      have b := entails_le hc.2 hall
      rw [Lin.from_den] at a
      rw [Lin.less_den] at b
      simp only [hle, ↓reduceIte]
      omega
    · next hle =>
      simp only [hle, ↓reduceIte]
      rcases Bool.or_eq_true _ _ |>.mp hc with hc | hc
      · have a := entails_le hc hall
        rw [Lin.from_den] at a
        exact .inl (by omega)
      · have b := entails_le hc hall
        rw [Lin.less_den] at b
        exact .inr (by omega)
  · cases hc

/-- **Whether one term is at most another, or below it, by what is
known**, each way things may be: both seen not to wrap, and the whole
number of the one no more than, or less than, that of the other. -/
def upToHolds (G : List (Val × TyS)) (v t : Val) (strict : Bool) : Bool :=
  (know G (v.lin.ms.map (·.2) ++ t.lin.ms.map (·.2))).all fun cs =>
    match noWrap (cs.length + 1) cs v, noWrap (cs.length + 1) cs t with
    | some P, some Q =>
      entails (cs.length + 1) cs ((Lin.addMul (-1) Q P).less (if strict then -1 else 0))
    | _, _ => false

theorem upToHolds_has {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {v t : Val}
    {strict : Bool} (h : upToHolds G v t strict = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    if strict then v.den ρ < t.den ρ else v.den ρ ≤ t.den ρ := by
  obtain ⟨cs, hcs, hall⟩ := know_le (ρ := ρ) G (v.lin.ms.map (·.2) ++ t.lin.ms.map (·.2)) hg
  have hc := List.all_eq_true.mp h cs hcs
  split at hc
  · next P Q hP hQ =>
    have eP := noWrap_eq hP hall
    have eQ := noWrap_eq hQ hall
    have eP' : natOf ρ v = ((v.den ρ).toNat : Int) := rfl
    have eQ' : natOf ρ t = ((t.den ρ).toNat : Int) := rfl
    have a := entails_le hc hall
    rw [Lin.less_den, Lin.addMul_den] at a
    cases strict
    · simp only [Bool.false_eq_true, ↓reduceIte] at a ⊢
      rw [BitVec.le_def]
      omega
    · simp only [↓reduceIte] at a ⊢
      rw [BitVec.lt_def]
      omega
  · cases hc

end TypedAsm.U
