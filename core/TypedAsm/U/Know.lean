import TypedAsm.U.Ints
import TypedAsm.U.Basic
import TypedAsm.U.TyS

/-!
# What is known of how large values are

The ranges known of terms, gathered as things known of whole numbers; and
whether a question of whole numbers is then answered. Every term is a
number of its own. A range known of a term says where that number lies; a
range that goes round says one of two things, and each is followed. A term
an operator made by wrapping is tied to the terms it was made from as a low
part: the sum of them, less so many times what the part holds.
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

/-- **A term's whole number is what it comes apart into, less two to the
sixty-fourth as often as it goes.** -/
theorem int_mod (ρ : Env) (s : Bool) (t : Val) :
    natOf ρ t = (t.int s).den (natOf ρ) % 18446744073709551616 := by
  have e := Val.int_den ρ s t
  generalize (t.int s).den (natOf ρ) = P at *
  show ((t.den ρ).toNat : Int) = _
  rw [← e, BitVec.toNat_ofInt]
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
part of the value; and a sum of whole values, a value shifted left or
turned about nought, the low sixty-four bits of what it comes apart
into. -/
def halfOf : Val → Option (Lin Int × Int)
  | .fop (.alu .add .w32) _ x y => some (Lin.addMul 1 (x.int true) (y.int true), 4294967296)
  | .fop (.alu .sub .w32) _ x y => some (Lin.addMul (-1) (y.int true) (x.int true), 4294967296)
  | .un (.trunc w) x => some (x.int true, 2 ^ w.bits)
  | .un (.zx _ sw) x => some (x.int true, 2 ^ sw.bits)
  | .un .low8 x => some (x.int true, 256)
  | .un .low16 x => some (x.int true, 65536)
  | .fop (.alu .and w) _ x (.lit m) => (maskBits w m).map fun k => (x.int true, 2 ^ k)
  | .bin .add a b => some ((Val.bin .add a b).int true, 18446744073709551616)
  | .un (.shl k) a => some ((Val.un (.shl k) a).int true, 18446744073709551616)
  | .un (.neg .w64) a => some ((Val.un (.neg .w64) a).int true, 18446744073709551616)
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
  · cases h; exact ⟨by omega, int_mod ρ true _⟩
  · cases h; exact ⟨by omega, int_mod ρ true _⟩
  · cases h; exact ⟨by omega, int_mod ρ true _⟩
  · cases h

/-! ## The least and the most a sum of multiples can be

A term none of the things known is of is made to stand for the sum, and
every other term is done away with. What is left says of that term alone
how small and how large it can be; and so of the sum. -/

/-- The term made to stand for a sum. -/
def mark : Val := .lit 0

/-- Whether a sum of multiples has none of a term. -/
def Lin.free (m : Val) (P : Lin Int) : Bool := P.ms.all fun p => p.2 != m

theorem multDen_free {f g : Val → Int} {m : Val} (hfg : ∀ v, v ≠ m → g v = f v) :
    (ms : Multiples Int) → (ms.all fun p => p.2 != m) = true → multDen g ms = multDen f ms
  | [], _ => rfl
  | p :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [multDen, hfg p.2 h.1, multDen_free hfg ps h.2]

theorem Lin.free_den {f g : Val → Int} {m : Val} (hfg : ∀ v, v ≠ m → g v = f v) {P : Lin Int}
    (h : P.free m = true) : P.den g = P.den f := by
  simp only [Lin.den, multDen_free hfg P.ms h]

/-- The most a term is left free to be, by things known of it alone. -/
def mostOf (m : Val) : List (Lin Int) → Option Int
  | [] => none
  | c :: cs =>
    match c.ms with
    | [(a, t)] =>
      if t = m ∧ 0 < a then
        match mostOf m cs with
        | some b => some (min (-c.k / a) b)
        | none => some (-c.k / a)
      else mostOf m cs
    | _ => mostOf m cs

theorem mostOf_le {f : Val → Int} {m : Val} : (cs : List (Lin Int)) → {hi : Int} →
    mostOf m cs = some hi → AllLe f cs → f m ≤ hi
  | [], _, h, _ => by cases h
  | c :: cs, hi, h, hall => by
    have hrest : AllLe f cs := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    unfold mostOf at h
    split at h
    · next a t hms =>
      split at h
      · next hc =>
        have hcd := hall c List.mem_cons_self
        simp only [Lin.den, hms, multDen, hc.1] at hcd
        have hb : f m ≤ -c.k / a := Int.le_ediv_of_mul_le hc.2 (by rw [Int.mul_comm]; omega)
        split at h
        · next b hb' =>
          cases h
          have := mostOf_le cs hb' hrest
          omega
        · cases h; exact hb
      · exact mostOf_le cs h hrest
    · exact mostOf_le cs h hrest

/-- The least a term is left free to be, by things known of it alone. -/
def leastOf (m : Val) : List (Lin Int) → Option Int
  | [] => none
  | c :: cs =>
    match c.ms with
    | [(a, t)] =>
      if t = m ∧ a < 0 then
        match leastOf m cs with
        | some b => some (max (-(-c.k / -a)) b)
        | none => some (-(-c.k / -a))
      else leastOf m cs
    | _ => leastOf m cs

theorem leastOf_le {f : Val → Int} {m : Val} : (cs : List (Lin Int)) → {lo : Int} →
    leastOf m cs = some lo → AllLe f cs → lo ≤ f m
  | [], _, h, _ => by cases h
  | c :: cs, lo, h, hall => by
    have hrest : AllLe f cs := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    unfold leastOf at h
    split at h
    · next a t hms =>
      split at h
      · next hc =>
        have hcd := hall c List.mem_cons_self
        simp only [Lin.den, hms, multDen, hc.1] at hcd
        have hb : -f m ≤ -c.k / -a := Int.le_ediv_of_mul_le (by omega) (by
          rw [Int.neg_mul_neg, Int.mul_comm]; omega)
        split at h
        · next b hb' =>
          cases h
          have := leastOf_le cs hb' hrest
          omega
        · cases h; omega
      · exact leastOf_le cs h hrest
    · exact leastOf_le cs h hrest

/-- The things known, with a term standing for a sum, every other term
done away with. -/
def project (cs : List (Lin Int)) (P : Lin Int) : List (Lin Int) :=
  elimBut [mark] (cs.length + 3)
    (Lin.addMul (-1) P (Lin.leaf mark) :: Lin.addMul (-1) (Lin.leaf mark) P :: cs)

/-- **The least and the most a sum of multiples can be**, the things known
being so. -/
def boundsOf (cs : List (Lin Int)) (P : Lin Int) : Option (Int × Int) :=
  if P.free mark && cs.all (Lin.free mark) then
    match leastOf mark (project cs P), mostOf mark (project cs P) with
    | some lo, some hi => some (lo, hi)
    | _, _ => none
  else none

theorem boundsOf_le {f : Val → Int} {cs : List (Lin Int)} {P : Lin Int} {lo hi : Int}
    (h : boundsOf cs P = some (lo, hi)) (hall : AllLe f cs) : lo ≤ P.den f ∧ P.den f ≤ hi := by
  unfold boundsOf at h
  split at h
  · next hfree =>
    rw [Bool.and_eq_true, List.all_eq_true] at hfree
    -- the mark worth what the sum is, every other term what it was
    have hfg : ∀ v, v ≠ mark → (fun v => if v = mark then P.den f else f v) v = f v :=
      fun v hv => by simp only [hv, ↓reduceIte]
    have hP := Lin.free_den hfg hfree.1
    have hpr : AllLe (fun v => if v = mark then P.den f else f v) (project cs P) := by
      refine elimBut_le _ _ fun c hc => ?_
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [Lin.addMul_den, Lin.leaf_den, hP]; simp only [↓reduceIte]; omega
      · rcases List.mem_cons.mp hc with rfl | hc
        · rw [Lin.addMul_den, Lin.leaf_den, hP]; simp only [↓reduceIte]; omega
        · rw [Lin.free_den hfg (hfree.2 c hc)]; exact hall c hc
    split at h
    · next lo' hi' hl hm =>
      cases h
      have a := leastOf_le _ hl hpr
      have b := mostOf_le _ hm hpr
      simp only [↓reduceIte] at a b
      exact ⟨a, b⟩
    · cases h
  · cases h

/-! ## Low parts

A term that is the low part of a sum, at so much, is the sum less so many
times that much: a whole number of times, and the same whichever operator
made it: a sum of whole values that wraps at two to the sixty-fourth, a sum
of low halves, a value cut, widened or masked. How many times is not known
outright; between what numbers it lies is, by what is known of how large
the sum and the term are. Even where it may be several, that says something
of the term: at most the sum less the fewest times, at least the sum less
the most. Where it can be only one, the term is the sum less that many. -/

/-- A term's whole number, as a sum of multiples: a number written out is
itself; any other term is one of itself. -/
def Val.alone : Val → Lin Int
  | .lit v => ⟨[], (v.toNat : Int)⟩
  | t => Lin.leaf t

theorem Val.alone_den (ρ : Env) (t : Val) : t.alone.den (natOf ρ) = natOf ρ t := by
  unfold Val.alone
  split
  · simp [Lin.den, multDen, natOf, Val.den]
  · exact Lin.leaf_den _ _

/-- **A low part, with how many times it may be off** what it is the low part
of: `t` is the low part of `E` at `M`, and `E` is `t` and `M` times one of
the `n` whole numbers from `qlo`. -/
structure LowPart where
  t : Val
  E : Lin Int
  M : Int
  qlo : Int
  n : Nat

/-- That it is so. -/
def LowPart.Ok (ρ : Env) (l : LowPart) : Prop :=
  halfOf l.t = some (l.E, l.M) ∧ l.qlo ≤ l.E.den (natOf ρ) / l.M ∧
    l.E.den (natOf ρ) / l.M < l.qlo + l.n

/-- **What a low part says of whole numbers**: the term is at most the sum
less the fewest times, and at least the sum less the most. -/
def LowPart.says (l : LowPart) : List (Lin Int) :=
  [Lin.addMul (-1) ⟨l.E.ms, l.E.k - l.M * l.qlo⟩ (Lin.leaf l.t),
   Lin.addMul (-1) (Lin.leaf l.t) ⟨l.E.ms, l.E.k - l.M * (l.qlo + l.n - 1)⟩]

theorem LowPart.says_le {ρ : Env} {l : LowPart} (h : l.Ok ρ) : AllLe (natOf ρ) l.says := by
  obtain ⟨hh, h1, h2⟩ := h
  obtain ⟨hM, hm⟩ := halfOf_mod ρ hh
  have e := Int.emod_def (l.E.den (natOf ρ)) l.M
  have a := Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt hM)
  have b := Int.mul_le_mul_of_nonneg_left (show l.E.den (natOf ρ) / l.M ≤ l.qlo + l.n - 1 by omega)
    (Int.le_of_lt hM)
  intro c hc
  simp only [LowPart.says, List.mem_cons, List.not_mem_nil, or_false] at hc
  simp only [Lin.den] at e hm a b
  rcases hc with rfl | rfl <;> rw [Lin.addMul_den, Lin.leaf_den] <;> simp only [Lin.den] <;> omega

/-- The same low part, off just so many times. -/
def LowPart.off (l : LowPart) (c : Int) : LowPart := { l with qlo := c, n := 1 }

/-- The numbers of times it may be off. -/
def LowPart.qs (l : LowPart) : List Int := (List.range l.n).map fun (i : Nat) => l.qlo + (i : Int)

/-- **It is off one of the numbers of times it may be.** -/
theorem LowPart.off_ok {ρ : Env} {l : LowPart} (h : l.Ok ρ) : ∃ c ∈ l.qs, (l.off c).Ok ρ := by
  obtain ⟨hh, h1, h2⟩ := h
  exact ⟨l.E.den (natOf ρ) / l.M, List.mem_map.mpr ⟨(l.E.den (natOf ρ) / l.M - l.qlo).toNat,
    List.mem_range.mpr (by omega), by omega⟩, hh, Int.le_refl _,
    show l.E.den (natOf ρ) / l.M < l.E.den (natOf ρ) / l.M + ((1 : Nat) : Int) by omega⟩

/-- **How many times a low part may be off**, the things known being so:
what the sum is more than the term by lies between two numbers, and is so
many times so much exactly. -/
def lowIn (cs : List (Lin Int)) (t : Val) : Option LowPart :=
  match halfOf t with
  | some (E, M) =>
    match boundsOf cs (Lin.addMul (-1) (Lin.leaf t) E) with
    | some (lo, hi) => some ⟨t, E, M, -(-lo / M), (hi / M + -lo / M + 1).toNat⟩
    | none => none
  | none => none

theorem lowIn_ok {ρ : Env} {cs : List (Lin Int)} {t : Val} {l : LowPart}
    (hall : AllLe (natOf ρ) cs) (h : lowIn cs t = some l) : l.Ok ρ := by
  unfold lowIn at h
  split at h
  · next E M hE =>
    split at h
    · next lo hi hb =>
      cases h
      obtain ⟨hM, hm⟩ := halfOf_mod ρ hE
      have b := boundsOf_le hb hall
      rw [Lin.addMul_den, Lin.leaf_den] at b
      have e := Int.emod_def (E.den (natOf ρ)) M
      have hq1 : -(E.den (natOf ρ) / M) ≤ -lo / M := Int.le_ediv_of_mul_le hM (by
        rw [Int.neg_mul, Int.mul_comm]; omega)
      have hq2 : E.den (natOf ρ) / M ≤ hi / M := Int.le_ediv_of_mul_le hM (by
        rw [Int.mul_comm]; omega)
      refine ⟨hE, ?_, ?_⟩
      · show -(-lo / M) ≤ E.den (natOf ρ) / M
        omega
      · show E.den (natOf ρ) / M < -(-lo / M) + ((hi / M + -lo / M + 1).toNat : Int)
        omega
    · cases h
  · cases h

/-- The low parts looked at again, one after another, the things known
being so: one seen to be off fewer numbers of times than it was says more,
and that is known for the rest. With them, whether any was. -/
def lowsPass : List (Lin Int) → List LowPart → List (Lin Int) × List LowPart × Bool
  | cs, [] => (cs, [], false)
  | cs, l :: ls =>
    match lowIn cs l.t with
    | some l' =>
      if l'.n < l.n then
        let r := lowsPass (l'.says ++ cs) ls
        (r.1, l' :: r.2.1, true)
      else
        let r := lowsPass cs ls
        (r.1, l :: r.2.1, r.2.2)
    | none =>
      let r := lowsPass cs ls
      (r.1, l :: r.2.1, r.2.2)

theorem lowsPass_le {ρ : Env} : (ls : List LowPart) → (cs : List (Lin Int)) →
    AllLe (natOf ρ) cs → (∀ l ∈ ls, l.Ok ρ) →
    AllLe (natOf ρ) (lowsPass cs ls).1 ∧ ∀ l ∈ (lowsPass cs ls).2.1, l.Ok ρ
  | [], cs, hall, _ => ⟨hall, fun _ h => by cases h⟩
  | l :: ls, cs, hall, hok => by
    have hrest : ∀ l' ∈ ls, l'.Ok ρ := fun l' h => hok l' (List.mem_cons_of_mem _ h)
    unfold lowsPass
    split
    · next l' hl' =>
      have ok' := lowIn_ok hall hl'
      split
      · have ih := lowsPass_le ls (l'.says ++ cs)
          (fun c hc => (List.mem_append.mp hc).elim (LowPart.says_le ok' c) (hall c)) hrest
        exact ⟨ih.1, fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ ok') (ih.2 x)⟩
      · have ih := lowsPass_le ls cs hall hrest
        exact ⟨ih.1, fun x hx =>
          (List.mem_cons.mp hx).elim (fun e => e ▸ hok l List.mem_cons_self) (ih.2 x)⟩
    · have ih := lowsPass_le ls cs hall hrest
      exact ⟨ih.1, fun x hx =>
        (List.mem_cons.mp hx).elim (fun e => e ▸ hok l List.mem_cons_self) (ih.2 x)⟩

/-- The low parts that may be off more than one number of times looked at
again and again, till none is seen to be off fewer than it was: for one
may be settled only by what another, settled, says. -/
def lowsAgain : Nat → List (Lin Int) → List LowPart → List (Lin Int) × List LowPart
  | 0, cs, ls => (cs, ls.filter fun l => decide (2 ≤ l.n))
  | k + 1, cs, ls =>
    let r := lowsPass cs (ls.filter fun l => decide (2 ≤ l.n))
    if r.2.2 then lowsAgain k r.1 r.2.1 else (cs, ls.filter fun l => decide (2 ≤ l.n))

theorem lowsAgain_le {ρ : Env} : (k : Nat) → (cs : List (Lin Int)) → (ls : List LowPart) →
    AllLe (natOf ρ) cs → (∀ l ∈ ls, l.Ok ρ) →
    AllLe (natOf ρ) (lowsAgain k cs ls).1 ∧ ∀ l ∈ (lowsAgain k cs ls).2, l.Ok ρ
  | 0, _, _, hall, hok => ⟨hall, fun l h => hok l (List.mem_filter.mp h).1⟩
  | k + 1, cs, ls, hall, hok => by
    have ih := lowsPass_le (ρ := ρ) (ls.filter fun l => decide (2 ≤ l.n)) cs hall
      (fun l h => hok l (List.mem_filter.mp h).1)
    unfold lowsAgain
    dsimp only
    split
    · exact lowsAgain_le k _ _ ih.1 ih.2
    · exact ⟨hall, fun l h => hok l (List.mem_filter.mp h).1⟩

/-- **The things known, with what the low parts among some terms say**, and
the low parts left that may be off more than one number of times. -/
def lowsIn (cs : List (Lin Int)) (ts : List Val) : List (Lin Int) × List LowPart :=
  let ls := ts.filterMap (lowIn cs)
  lowsAgain (ls.length + 1) (ls.flatMap LowPart.says ++ cs) ls

theorem lowsIn_le {ρ : Env} {cs : List (Lin Int)} (ts : List Val) (hall : AllLe (natOf ρ) cs) :
    AllLe (natOf ρ) (lowsIn cs ts).1 ∧ ∀ l ∈ (lowsIn cs ts).2, l.Ok ρ := by
  have hok : ∀ l ∈ ts.filterMap (lowIn cs), l.Ok ρ := fun l h => by
    obtain ⟨t, -, ht⟩ := List.mem_filterMap.mp h
    exact lowIn_ok hall ht
  exact lowsAgain_le _ _ _ (fun c hc => (List.mem_append.mp hc).elim
    (fun hc => by
      obtain ⟨l, hl, hc⟩ := List.mem_flatMap.mp hc
      exact LowPart.says_le (hok l hl) c hc) (hall c)) hok

/-- How many ways, all told, the reasoner goes into for one question: a
bound on searching only. A low part left out of that still says what it
says whichever number of times it is off. -/
def mostWays : Nat := 64

/-- The first low parts of some, as many as come to no more ways than so
many. -/
def fewLows : Nat → List LowPart → List LowPart
  | _, [] => []
  | b, l :: ls => if l.n ≤ b then l :: fewLows (b / l.n) ls else []

theorem fewLows_sub : (b : Nat) → (ls : List LowPart) → ∀ l ∈ fewLows b ls, l ∈ ls
  | _, [], _, h => by cases h
  | b, l :: ls, x, h => by
    unfold fewLows at h
    split at h
    · exact (List.mem_cons.mp h).elim (fun e => e ▸ List.mem_cons_self)
        (fun h => List.mem_cons_of_mem _ (fewLows_sub _ ls x h))
    · cases h

/-- A low part put among others that go from fewest numbers of times it
may be off, where it goes. -/
def putLow (l : LowPart) : List LowPart → List LowPart
  | [] => [l]
  | x :: xs => if l.n ≤ x.n then l :: x :: xs else x :: putLow l xs

theorem putLow_sub (l : LowPart) : (ls : List LowPart) → ∀ x ∈ putLow l ls, x = l ∨ x ∈ ls
  | [], x, h => .inl (List.mem_singleton.mp h)
  | y :: ys, x, h => by
    unfold putLow at h
    split at h
    · exact (List.mem_cons.mp h).imp_right id
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inr List.mem_cons_self
      · exact (putLow_sub l ys x h).imp_right (List.mem_cons_of_mem _)

/-- Low parts, from the one that may be off fewest numbers of times. -/
def sortLows : List LowPart → List LowPart
  | [] => []
  | l :: ls => putLow l (sortLows ls)

theorem sortLows_sub : (ls : List LowPart) → ∀ x ∈ sortLows ls, x ∈ ls
  | [], _, h => h
  | l :: ls, x, h => (putLow_sub l _ x h).elim (fun e => e ▸ List.mem_cons_self)
      (fun h => List.mem_cons_of_mem _ (sortLows_sub ls x h))

/-- **Whether a question is answered, the things known being so**: as they
are; else in each way the first of some low parts may be, and so on. The
question is asked of things known, and may be any that more known answers
no worse. -/
def askIn (ask : List (Lin Int) → Bool) : List LowPart → List (Lin Int) → Bool
  | [], cs => ask cs
  | l :: ls, cs => ask cs || l.qs.all fun c => askIn ask ls ((l.off c).says ++ cs)

theorem askIn_of {ρ : Env} {P : Prop} {ask : List (Lin Int) → Bool}
    (hask : ∀ cs, ask cs = true → AllLe (natOf ρ) cs → P) :
    (ls : List LowPart) → (cs : List (Lin Int)) → askIn ask ls cs = true →
    AllLe (natOf ρ) cs → (∀ l ∈ ls, l.Ok ρ) → P
  | [], cs, h, hall, _ => hask cs h hall
  | l :: ls, cs, h, hall, hok => by
    simp only [askIn, Bool.or_eq_true, List.all_eq_true] at h
    rcases h with h | h
    · exact hask cs h hall
    · obtain ⟨c, hc, hco⟩ := LowPart.off_ok (hok l List.mem_cons_self)
      exact askIn_of hask ls _ (h c hc)
        (fun x hx => (List.mem_append.mp hx).elim (LowPart.says_le hco x) (hall x))
        (fun l' hl' => hok l' (List.mem_cons_of_mem _ hl'))

/-- **The ways things may be with some low parts gone into**, each off one
of the numbers of times it may be: but for the ways that cannot be. -/
def waysIn : List LowPart → List (Lin Int) → List (List (Lin Int))
  | [], cs => [cs]
  | l :: ls, cs => l.qs.flatMap fun c =>
    if refute (cs.length + 3) ((l.off c).says ++ cs) then []
    else waysIn ls ((l.off c).says ++ cs)

theorem waysIn_le {ρ : Env} : (ls : List LowPart) → (cs : List (Lin Int)) →
    AllLe (natOf ρ) cs → (∀ l ∈ ls, l.Ok ρ) → ∃ cs' ∈ waysIn ls cs, AllLe (natOf ρ) cs'
  | [], cs, hall, _ => ⟨cs, List.mem_singleton.mpr rfl, hall⟩
  | l :: ls, cs, hall, hok => by
    obtain ⟨c, hc, hco⟩ := LowPart.off_ok (hok l List.mem_cons_self)
    have hb : AllLe (natOf ρ) ((l.off c).says ++ cs) :=
      fun x hx => (List.mem_append.mp hx).elim (LowPart.says_le hco x) (hall x)
    obtain ⟨cs', hcs', hall'⟩ := waysIn_le ls _ hb
      (fun l' hl' => hok l' (List.mem_cons_of_mem _ hl'))
    refine ⟨cs', List.mem_flatMap.mpr ⟨c, hc, ?_⟩, hall'⟩
    cases hr : refute (cs.length + 3) ((l.off c).says ++ cs) with
    | false => simpa using hcs'
    | true => exact (refute_false _ _ hr hb).elim

/-! ## What is known, gathered -/

/-- How deep a term goes. -/
def Val.height : Val → Nat
  | .un _ a => a.height + 1
  | .bin _ a b => max a.height b.height + 1
  | .tri _ a b c => max a.height (max b.height c.height) + 1
  | .fop _ _ a b => max a.height b.height + 1
  | .app _ a b => max a.height b.height + 1
  | _ => 0

/-- A term, the terms of what it is the low part of, and theirs: so far in. -/
def inside : Nat → Val → List Val
  | 0, t => [t]
  | n + 1, t =>
    t :: match halfOf t with
      | some E => E.1.ms.flatMap fun p => inside n p.2
      | none => []

/-- A term with every term it is made of through low parts; of a number
written out, none. -/
def termsIn : Val → List Val
  | .lit _ => []
  | v => inside v.height v

/-- The things known, and with them what a range known of a term says of
its whole number: that it lies in the range; one way or the other, where
the range goes round. -/
def addFact (u : Val) (lo hi : BitVec 64) (cs : List (Lin Int)) : List (List (Lin Int)) :=
  if lo ≤ hi then [Lin.from lo.toNat u.alone :: u.alone.less hi.toNat :: cs]
  else [Lin.from lo.toNat u.alone :: cs, u.alone.less hi.toNat :: cs]

theorem addFact_le {ρ : Env} {u : Val} {lo hi : BitVec 64} {cs : List (Lin Int)}
    (hall : AllLe (natOf ρ) cs) (hu : Range.has ⟨lo, hi⟩ (u.den ρ)) :
    ∃ cs' ∈ addFact u lo hi cs, AllLe (natOf ρ) cs' := by
  have e := Val.alone_den ρ u
  have hn := Range.has_nat hu
  have e' : natOf ρ u = ((u.den ρ).toNat : Int) := rfl
  unfold addFact
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

/-- The things known, and with them what one term's being at most another,
or less, says of their whole numbers. -/
def addUpTo (u t : Val) (strict : Bool) (cs : List (Lin Int)) : List (Lin Int) :=
  (Lin.addMul (-1) t.alone u.alone).less (if strict then -1 else 0) :: cs

theorem addUpTo_le {ρ : Env} {u t : Val} {strict : Bool} {cs : List (Lin Int)}
    (hall : AllLe (natOf ρ) cs)
    (hu : if strict then u.den ρ < t.den ρ else u.den ρ ≤ t.den ρ) :
    AllLe (natOf ρ) (addUpTo u t strict cs) := by
  have eu := Val.alone_den ρ u
  have et := Val.alone_den ρ t
  have e1 : natOf ρ u = ((u.den ρ).toNat : Int) := rfl
  have e2 : natOf ρ t = ((t.den ρ).toNat : Int) := rfl
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [Lin.less_den, Lin.addMul_den]
    cases strict
    · simp only [Bool.false_eq_true, ↓reduceIte] at hu ⊢
      have := BitVec.le_def.mp hu
      omega
    · simp only [↓reduceIte] at hu ⊢
      have := BitVec.lt_def.mp hu
      omega
  · exact hall c hc

/-- Each way things may be, with what the things known of ranges say, and
of one term's being at most another. -/
def addFacts : List (Val × TyS) → List (List (Lin Int)) → List (List (Lin Int))
  | [], K => K
  | (u, .range lo hi) :: G, K => addFacts G (K.flatMap (addFact u lo hi))
  | (u, .upTo t strict) :: G, K => addFacts G (K.map (addUpTo u t strict))
  | _ :: G, K => addFacts G K

theorem addFacts_le {ρ : Env} {Ψ' : MemTy} {n : Nat} :
    (G : List (Val × TyS)) → (K : List (List (Lin Int))) →
    (∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) →
    (∃ cs ∈ K, AllLe (natOf ρ) cs) → ∃ cs ∈ addFacts G K, AllLe (natOf ρ) cs
  | [], K, _, h => h
  | (u, τ) :: G, K, hg, ⟨cs, hcs, hall⟩ => by
    have hrest : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ) :=
      fun g hgm => hg g (List.mem_cons_of_mem _ hgm)
    cases τ with
    | range lo hi =>
      have hu : Range.has ⟨lo, hi⟩ (u.den ρ) := hasTy_range.mp (hg (u, .range lo hi) List.mem_cons_self)
      obtain ⟨cs', hcs', hall'⟩ := addFact_le hall hu
      exact addFacts_le G _ hrest ⟨cs', List.mem_flatMap.mpr ⟨cs, hcs, hcs'⟩, hall'⟩
    | upTo t strict =>
      have hu := hasTy_upTo.mp (hg (u, .upTo t strict) List.mem_cons_self)
      exact addFacts_le G _ hrest ⟨_, List.mem_map.mpr ⟨cs, hcs, rfl⟩, addUpTo_le hall hu⟩
    | _ => exact addFacts_le G K hrest ⟨cs, hcs, hall⟩

/-- The terms the ranges known are of, with those they are made of. -/
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

/-- Each way things may be, by all of some ranges known, of some terms:
what is so of each term whatever is known, what the ranges say, and what
the low parts among the terms say; with the low parts left to go into. -/
def knowAll (G : List (Val × TyS)) (ts : List Val) : List (List (Lin Int) × List LowPart) :=
  (addFacts G [ts.flatMap (atomCs G)]).map fun cs =>
    let r := lowsIn cs ts
    (r.1, fewLows mostWays (sortLows r.2))

/-- **Each way things may be, by the ranges known that bear on some
terms**: the things known of whole numbers, and the low parts that may yet
be off one of a few numbers of times, those of fewest first. -/
def know (G : List (Val × TyS)) (more : List Val) : List (List (Lin Int) × List LowPart) :=
  let as := more.flatMap termsIn
  let G' := cone G.length G as
  knowAll G' (factAtoms G' ++ as).eraseDups

theorem know_le {ρ : Env} {Ψ' : MemTy} {n : Nat} (G : List (Val × TyS)) (more : List Val)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    ∃ w ∈ know G more, AllLe (natOf ρ) w.1 ∧ ∀ l ∈ w.2, l.Ok ρ := by
  have hg' : ∀ g ∈ cone G.length G (more.flatMap termsIn),
      HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ) :=
    fun g hgm => hg g (cone_sub _ _ _ g hgm)
  obtain ⟨cs, hcs, hall⟩ := addFacts_le _ _ hg'
    ⟨_, List.mem_singleton.mpr rfl, fun c hc => by
      obtain ⟨t, _, hc⟩ := List.mem_flatMap.mp hc
      exact atomCs_le (rangesHold_of hg') t c hc⟩
  have hl := lowsIn_le (ρ := ρ) (factAtoms (cone G.length G (more.flatMap termsIn)) ++
    more.flatMap termsIn).eraseDups hall
  exact ⟨_, List.mem_map.mpr ⟨cs, hcs, rfl⟩, hl.1, fun l h =>
    hl.2 l (sortLows_sub _ l (fewLows_sub _ _ l h))⟩

/-! ## Questions -/

/-- **Whether a question of some terms is answered by what is known**, each
way things may be; going into the ways low parts may be only where it is
not answered without. -/
def byKnown (G : List (Val × TyS)) (more : List Val) (ask : List (Lin Int) → Bool) : Bool :=
  (know G more).all fun w => askIn ask w.2 w.1

theorem byKnown_of {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {more : List Val}
    {ask : List (Lin Int) → Bool} {P : Prop} (h : byKnown G more ask = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ))
    (hask : ∀ cs, ask cs = true → AllLe (natOf ρ) cs → P) : P := by
  obtain ⟨w, hw, hall, hok⟩ := know_le (ρ := ρ) G more hg
  exact askIn_of hask _ _ (List.all_eq_true.mp h w hw) hall hok

/-- **Each way things may be, by what is known of some terms, the low
parts gone into.** -/
def knowWays (G : List (Val × TyS)) (more : List Val) : List (List (Lin Int)) :=
  (know G more).flatMap fun w => waysIn w.2 w.1

theorem knowWays_le {ρ : Env} {Ψ' : MemTy} {n : Nat} (G : List (Val × TyS)) (more : List Val)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    ∃ cs ∈ knowWays G more, AllLe (natOf ρ) cs := by
  obtain ⟨w, hw, hall, hok⟩ := know_le (ρ := ρ) G more hg
  obtain ⟨cs, hcs, hall'⟩ := waysIn_le w.2 w.1 hall hok
  exact ⟨cs, List.mem_flatMap.mpr ⟨w, hw, hcs⟩, hall'⟩

/-- **Whether a term lies in a range, by the ranges known**, each way
things may be: its whole number lies there; on one side or the other, where
the range goes round. -/
def rangeHolds (G : List (Val × TyS)) (v : Val) (lo hi : BitVec 64) : Bool :=
  byKnown G [v] fun cs =>
    if lo ≤ hi then
      entails (cs.length + 1) cs (Lin.from lo.toNat v.alone) &&
        entails (cs.length + 1) cs (v.alone.less hi.toNat)
    else
      entails (cs.length + 1) cs (Lin.from lo.toNat v.alone) ||
        entails (cs.length + 1) cs (v.alone.less hi.toNat)

theorem rangeHolds_has {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {v : Val}
    {lo hi : BitVec 64} (h : rangeHolds G v lo hi = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    Range.has ⟨lo, hi⟩ (v.den ρ) := by
  refine byKnown_of h hg fun cs hc hall => ?_
  have e := Val.alone_den ρ v
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

/-- **Whether one term is at most another, or below it, by what is
known**, each way things may be: the whole number of the one no more than,
or less than, that of the other. -/
def upToHolds (G : List (Val × TyS)) (v t : Val) (strict : Bool) : Bool :=
  byKnown G [v, t] fun cs =>
    entails (cs.length + 1) cs ((Lin.addMul (-1) t.alone v.alone).less (if strict then -1 else 0))

theorem upToHolds_has {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {v t : Val}
    {strict : Bool} (h : upToHolds G v t strict = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    if strict then v.den ρ < t.den ρ else v.den ρ ≤ t.den ρ := by
  refine byKnown_of h hg fun cs hc hall => ?_
  have eP := Val.alone_den ρ v
  have eQ := Val.alone_den ρ t
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

end TypedAsm.U
