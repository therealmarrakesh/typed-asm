import TypedAsm.U.CondRel
import TypedAsm.U.Basic
import TypedAsm.U.TyS
import TypedAsm.U.Ops

namespace TypedAsm.U
open TypedAsm

/-! # The least and the most a value can be, by what it is made of -/

/-- From `lo` to `hi`, as numbers without sign. -/
structure Ival where
  lo : Nat
  hi : Nat

def Ival.has (I : Ival) (x : Nat) : Prop := I.lo ≤ x ∧ x ≤ I.hi

/-- Every value of `n` bits. -/
def Ival.bits (n : Nat) : Ival := ⟨0, 2 ^ n - 1⟩

theorem Ival.bits_has {n x : Nat} (h : x < 2 ^ n) : (Ival.bits n).has x := ⟨Nat.zero_le _, by
  simp only [Ival.bits]; omega⟩

/-- What a value is once cut to its low `n` bits. -/
def Ival.cut (n : Nat) (I : Ival) : Ival := if I.hi < 2 ^ n then I else .bits n

theorem Ival.cut_has {n x : Nat} {I : Ival} (h : I.has x) : (I.cut n).has (x % 2 ^ n) := by
  unfold Ival.cut
  split
  · next hlt =>
    rw [Nat.mod_eq_of_lt (by have := h.2; omega)]
    exact h
  · exact Ival.bits_has (Nat.mod_lt _ (Nat.two_pow_pos n))

theorem Ival.cut_hi {n : Nat} {I : Ival} : (I.cut n).hi < 2 ^ n ∨ (I.cut n).hi = 2 ^ n - 1 := by
  unfold Ival.cut; split
  · exact .inl (by assumption)
  · exact .inr rfl

theorem toNat_wide (w : Width) (x : BitVec w.bits) : (wide x).toNat = x.toNat := by
  have := x.isLt
  cases w <;> simp only [wide, BitVec.toNat_setWidth, Width.bits] at this ⊢ <;> omega

theorem toNat_cut (w : Width) (a : BitVec 64) : (a.setWidth w.bits).toNat = a.toNat % 2 ^ w.bits :=
  BitVec.toNat_setWidth ..

theorem add_res_w (w : Width) (a b : BitVec w.bits) : (addCarry a b false).1 = a + b := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    (apply BitVec.eq_of_toNat_eq
     have := a.isLt; have := b.isLt
     simp [addCarry, BitVec.toNat_add, BitVec.toNat_setWidth]
     try omega)

/-- **A sum, from the operands' ranges**: where the most it can be fits, the
sum of the least and of the most. -/
def Ival.add (n : Nat) (A B : Ival) : Ival :=
  if A.hi + B.hi < 2 ^ n then ⟨A.lo + B.lo, A.hi + B.hi⟩ else .bits n

theorem Ival.add_has {n x y : Nat} {A B : Ival} (ha : A.has x) (hb : B.has y) :
    (A.add n B).has ((x + y) % 2 ^ n) := by
  unfold Ival.add
  split
  · next hlt =>
    rw [Nat.mod_eq_of_lt (by have := ha.2; have := hb.2; omega)]
    obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact Ival.bits_has (Nat.mod_lt _ (Nat.two_pow_pos n))

/-- **A difference**: where the least of the first is at least the most of the
second, it does not wrap. -/
def Ival.sub (n : Nat) (A B : Ival) : Ival :=
  if B.hi ≤ A.lo ∧ A.hi < 2 ^ n then ⟨A.lo - B.hi, A.hi - B.lo⟩ else .bits n

theorem Ival.sub_has {n x y : Nat} {A B : Ival} (ha : A.has x) (hb : B.has y) (hy : y < 2 ^ n) :
    (A.sub n B).has ((2 ^ n - y + x) % 2 ^ n) := by
  unfold Ival.sub
  split
  · next hc =>
    have e : (2 ^ n - y + x) % 2 ^ n = x - y := by
      rw [show 2 ^ n - y + x = (x - y) + 2 ^ n by have := ha.1; have := hb.2; omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by have := ha.2; omega)]
    rw [e]
    obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
    exact ⟨by dsimp only; omega, by dsimp only; omega⟩
  · exact Ival.bits_has (Nat.mod_lt _ (Nat.two_pow_pos n))

/-- Every value. -/
def Ival.full : Ival := .bits 64

theorem Ival.full_has (x : BitVec 64) : Ival.full.has x.toNat := Ival.bits_has x.isLt

/-- Either of two. -/
def Ival.union (A B : Ival) : Ival := ⟨min A.lo B.lo, max A.hi B.hi⟩

theorem Ival.union_left {A B : Ival} {x : Nat} (h : A.has x) : (A.union B).has x :=
  ⟨by have := h.1; simp only [Ival.union]; omega, by have := h.2; simp only [Ival.union]; omega⟩

theorem Ival.union_right {A B : Ival} {x : Nat} (h : B.has x) : (A.union B).has x :=
  ⟨by have := h.1; simp only [Ival.union]; omega, by have := h.2; simp only [Ival.union]; omega⟩

/-- So many times, where the most it can be fits in `n` bits. -/
def Ival.scale (n m : Nat) (A : Ival) : Ival :=
  if A.hi * m < 2 ^ n then ⟨A.lo * m, A.hi * m⟩ else .bits n

theorem Ival.scale_has {n m x : Nat} {A : Ival} (h : A.has x) : (A.scale n m).has (x * m % 2 ^ n) := by
  unfold Ival.scale
  split
  · next hlt =>
    obtain ⟨h1, h2⟩ := h
    have hm : x * m ≤ A.hi * m := Nat.mul_le_mul_right _ h2
    rw [Nat.mod_eq_of_lt (by omega)]
    exact ⟨by dsimp only; exact Nat.mul_le_mul_right _ h1, by dsimp only; exact hm⟩
  · exact Ival.bits_has (Nat.mod_lt _ (Nat.two_pow_pos n))

/-- So many times fewer, rounded down. -/
def Ival.shr (c : Nat) (A : Ival) : Ival := ⟨A.lo / 2 ^ c, A.hi / 2 ^ c⟩

theorem Ival.shr_has {c x : Nat} {A : Ival} (h : A.has x) : (A.shr c).has (x / 2 ^ c) :=
  ⟨Nat.div_le_div_right h.1, Nat.div_le_div_right h.2⟩

/-! ## One operand -/

/-- **The range of what an operator on one value gives**, from the range of
the value. -/
def Un.ival : Un → Ival → Ival
  | .trunc w, A => A.cut w.bits
  | .zx _ sw, A => A.cut sw.bits
  | .low8, A => A.cut 8
  | .low16, A => A.cut 16
  | .shl k, A => A.scale 64 (2 ^ k)
  | .sxd, _ => .full
  | .neg w, _ | .not w, _ | .popcnt w, _ | .bswap w, _ | .signFill w, _ | .sx w _, _ => .bits w.bits

theorem Un.ival_has (o : Un) {A : Ival} {a : BitVec 64} (h : A.has a.toNat) :
    (o.ival A).has (o.eval a).toNat := by
  cases o with
  | trunc w =>
    show (A.cut w.bits).has (wide (a.setWidth w.bits)).toNat
    rw [toNat_wide, toNat_cut]; exact Ival.cut_has h
  | zx w sw =>
    show (A.cut sw.bits).has (wide (w := w) ((a.setWidth sw.bits).setWidth w.bits)).toNat
    rw [toNat_wide, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have hle : 2 ^ sw.bits ≤ 2 ^ w.bits := Nat.pow_le_pow_right (by omega) (by
      cases w <;> cases sw <;> simp [Width.bits, NarrowW.bits])
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hle)]
    exact Ival.cut_has h
  | low8 =>
    show (A.cut 8).has ((a.setWidth 8).setWidth 64).toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 8)) (by decide))]
    exact Ival.cut_has h
  | low16 =>
    show (A.cut 16).has ((a.setWidth 16).setWidth 64).toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 16)) (by decide))]
    exact Ival.cut_has h
  | shl k =>
    show (A.scale 64 (2 ^ k)).has (a <<< k).toNat
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    exact Ival.scale_has h
  | sxd => exact Ival.full_has _
  | neg w => exact Ival.bits_has (by rw [Un.eval, toNat_wide]; exact BitVec.isLt _)
  | not w => exact Ival.bits_has (by rw [Un.eval, toNat_wide]; exact BitVec.isLt _)
  | popcnt w => exact Ival.bits_has (by rw [Un.eval, toNat_wide]; exact BitVec.isLt _)
  | bswap w => exact Ival.bits_has (by rw [Un.eval, toNat_wide]; exact BitVec.isLt _)
  | signFill w => exact Ival.bits_has (by rw [Un.eval, toNat_wide]; exact BitVec.isLt _)
  | sx w sw => exact Ival.bits_has (by rw [Un.eval, toNat_wide]; exact BitVec.isLt _)

/-! ## Two operands -/

/-- What a shift at a width gives, as a number: the value cut to the width,
moved so many bits; with nought it is the value. -/
theorem shift_eval (op : ShiftOp) (w : Width) (a : BitVec 64) (c : Nat) :
    (op.eval Flags.unknown (a.setWidth w.bits) c).1
      = if c = 0 then a.setWidth w.bits else (op.eval Flags.unknown (a.setWidth w.bits) c).1 := by
  split
  · next h => subst h; simp [ShiftOp.eval]
  · rfl

/-- **The range of what an operator on two values that leaves the flags
alone gives**, from theirs; the second as a term, for a count written out. -/
def Bin.ival : Bin → Ival → Ival → Val → Ival
  | .add, A, B, _ => A.add 64 B
  | .shift .shr w, A, _, .lit k => (A.cut w.bits).shr (k.toNat % w.bits)
  | .shift .shr w, A, _, _ => ⟨0, (A.cut w.bits).hi⟩
  | .shift .shl w, A, _, .lit k => (A.cut w.bits).scale w.bits (2 ^ (k.toNat % w.bits))
  | .shift _ w, _, _, _ => .bits w.bits
  | .imul w, _, _, _ => .bits w.bits

theorem shr_toNat (w : Width) (a : BitVec 64) (c : Nat) :
    (wide (ShiftOp.eval .shr Flags.unknown (a.setWidth w.bits) c).1).toNat
      = a.toNat % 2 ^ w.bits / 2 ^ c := by
  rw [toNat_wide]
  unfold ShiftOp.eval
  split
  · next h => subst h; simp
  · show (a.setWidth w.bits >>> c).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_cut]

theorem shl_toNat (w : Width) (a : BitVec 64) (c : Nat) :
    (wide (ShiftOp.eval .shl Flags.unknown (a.setWidth w.bits) c).1).toNat
      = a.toNat % 2 ^ w.bits * 2 ^ c % 2 ^ w.bits := by
  rw [toNat_wide]
  unfold ShiftOp.eval
  split
  · next h =>
    subst h
    rw [toNat_cut, Nat.pow_zero, Nat.mul_one, Nat.mod_mod]
  · show (a.setWidth w.bits <<< c).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, toNat_cut]

theorem Bin.ival_has (o : Bin) {A B : Ival} {a : BitVec 64} (b : Val) {ρ : Env}
    (ha : A.has a.toNat) (hb : B.has (b.den ρ).toNat) :
    (o.ival A B b).has (o.eval a (b.den ρ)).toNat := by
  cases o with
  | add =>
    show (A.add 64 B).has (a + b.den ρ).toNat
    rw [BitVec.toNat_add]; exact Ival.add_has ha hb
  | imul w => exact Ival.bits_has (by rw [Bin.eval, toNat_wide]; exact BitVec.isLt _)
  | shift op w =>
    cases op with
    | shr =>
      cases b with
      | lit k =>
        show ((A.cut w.bits).shr (k.toNat % w.bits)).has
          (wide (ShiftOp.eval .shr Flags.unknown (a.setWidth w.bits) (k.toNat % w.bits)).1).toNat
        rw [shr_toNat]
        exact Ival.shr_has (Ival.cut_has ha)
      | _ =>
        refine ⟨Nat.zero_le _, ?_⟩
        show _ ≤ (A.cut w.bits).hi
        rw [Bin.eval, shr_toNat]
        exact Nat.le_trans (Nat.div_le_self _ _) (Ival.cut_has ha).2
    | shl =>
      cases b with
      | lit k =>
        show ((A.cut w.bits).scale w.bits (2 ^ (k.toNat % w.bits))).has
          (wide (ShiftOp.eval .shl Flags.unknown (a.setWidth w.bits) (k.toNat % w.bits)).1).toNat
        rw [shl_toNat]
        exact Ival.scale_has (Ival.cut_has ha)
      | _ => exact Ival.bits_has (by rw [Bin.eval, toNat_wide]; exact BitVec.isLt _)
    | sar => exact Ival.bits_has (by rw [Bin.eval, toNat_wide]; exact BitVec.isLt _)
    | rol => exact Ival.bits_has (by rw [Bin.eval, toNat_wide]; exact BitVec.isLt _)
    | ror => exact Ival.bits_has (by rw [Bin.eval, toNat_wide]; exact BitVec.isLt _)

/-! ## Two operands, with the flags -/

/-- At most what both, or either, of two values below `2 ^ n` have set. -/
def Ival.bitsOf (A B : Ival) : Ival := ⟨0, 2 ^ (Nat.log2 (max A.hi B.hi) + 1) - 1⟩

theorem Ival.bitsOf_or {A B : Ival} {x y : Nat} (ha : A.has x) (hb : B.has y) :
    (A.bitsOf B).has (x ||| y) ∧ (A.bitsOf B).has (x ^^^ y) := by
  have hm := @Nat.lt_log2_self (max A.hi B.hi)
  have hx : x < 2 ^ (Nat.log2 (max A.hi B.hi) + 1) := by have := ha.2; omega
  have hy : y < 2 ^ (Nat.log2 (max A.hi B.hi) + 1) := by have := hb.2; omega
  have h1 := Nat.or_lt_two_pow hx hy
  have h2 := Nat.xor_lt_two_pow hx hy
  exact ⟨⟨Nat.zero_le _, by simp only [Ival.bitsOf]; omega⟩,
    ⟨Nat.zero_le _, by simp only [Ival.bitsOf]; omega⟩⟩

/-- **The range of what an operator on two values with the flags gives**. -/
def FOp.ival : FOp → Ival → Ival → Ival
  | .alu .add w, A, B => (A.cut w.bits).add w.bits (B.cut w.bits)
  | .alu .sub w, A, B | .alu .cmp w, A, B => (A.cut w.bits).sub w.bits (B.cut w.bits)
  | .alu .and w, A, B => ⟨0, min (A.cut w.bits).hi (B.cut w.bits).hi⟩
  | .alu .or w, A, B | .alu .xor w, A, B => (A.cut w.bits).bitsOf (B.cut w.bits)
  | .alu .adc w, _, _ | .alu .sbb w, _, _ => .bits w.bits
  | .cmov _ w, A, B => (A.cut w.bits).union (B.cut w.bits)
  | .setcc _, _, _ => .full
  | .condByte _, _, _ => ⟨0, 1⟩

theorem alu_lt (op : AluOp) (w : Width) (fl : Flags) (a b : BitVec 64) :
    (FOp.eval (.alu op w) fl a b).toNat < 2 ^ w.bits := by
  rw [FOp.eval, toNat_wide]; exact BitVec.isLt _

theorem FOp.ival_has (o : FOp) {A B : Ival} {a b : BitVec 64} (fl : Flags)
    (ha : A.has a.toNat) (hb : B.has b.toNat) : (o.ival A B).has (o.eval fl a b).toNat := by
  have ca := Ival.cut_has (n := 64) ha
  cases o with
  | alu op w =>
    have cA := Ival.cut_has (n := w.bits) ha
    have cB := Ival.cut_has (n := w.bits) hb
    have hbl : b.toNat % 2 ^ w.bits < 2 ^ w.bits := Nat.mod_lt _ (Nat.two_pow_pos _)
    cases op with
    | add =>
      show ((A.cut w.bits).add w.bits (B.cut w.bits)).has
        (wide (addCarry (a.setWidth w.bits) (b.setWidth w.bits) false).1).toNat
      rw [toNat_wide, add_res_w, BitVec.toNat_add, toNat_cut, toNat_cut]
      exact Ival.add_has cA cB
    | sub =>
      show ((A.cut w.bits).sub w.bits (B.cut w.bits)).has
        (wide (subBorrow (a.setWidth w.bits) (b.setWidth w.bits) false).1).toNat
      rw [toNat_wide, sub_res, BitVec.toNat_sub, toNat_cut, toNat_cut]
      exact Ival.sub_has cA cB hbl
    | cmp =>
      show ((A.cut w.bits).sub w.bits (B.cut w.bits)).has
        (wide (subBorrow (a.setWidth w.bits) (b.setWidth w.bits) false).1).toNat
      rw [toNat_wide, sub_res, BitVec.toNat_sub, toNat_cut, toNat_cut]
      exact Ival.sub_has cA cB hbl
    | and =>
      show (⟨0, min (A.cut w.bits).hi (B.cut w.bits).hi⟩ : Ival).has
        (wide (a.setWidth w.bits &&& b.setWidth w.bits)).toNat
      rw [toNat_wide, BitVec.toNat_and, toNat_cut, toNat_cut]
      have h1 := @Nat.and_le_left (a.toNat % 2 ^ w.bits) (b.toNat % 2 ^ w.bits)
      have h2 := @Nat.and_le_right (a.toNat % 2 ^ w.bits) (b.toNat % 2 ^ w.bits)
      exact ⟨Nat.zero_le _, by have := cA.2; have := cB.2; dsimp only; omega⟩
    | or =>
      show ((A.cut w.bits).bitsOf (B.cut w.bits)).has
        (wide (a.setWidth w.bits ||| b.setWidth w.bits)).toNat
      rw [toNat_wide, BitVec.toNat_or, toNat_cut, toNat_cut]
      exact (Ival.bitsOf_or cA cB).1
    | xor =>
      show ((A.cut w.bits).bitsOf (B.cut w.bits)).has
        (wide (a.setWidth w.bits ^^^ b.setWidth w.bits)).toNat
      rw [toNat_wide, BitVec.toNat_xor, toNat_cut, toNat_cut]
      exact (Ival.bitsOf_or cA cB).2
    | adc => exact Ival.bits_has (alu_lt _ _ _ _ _)
    | sbb => exact Ival.bits_has (alu_lt _ _ _ _ _)
  | cmov c w =>
    show ((A.cut w.bits).union (B.cut w.bits)).has
      (wide (w := w) (if (c.eval fl).getD false then b.setWidth w.bits else a.setWidth w.bits)).toNat
    rw [toNat_wide]
    split
    · rw [toNat_cut]; exact Ival.union_right (Ival.cut_has hb)
    · rw [toNat_cut]; exact Ival.union_left (Ival.cut_has ha)
  | setcc c => exact Ival.full_has _
  | condByte c =>
    show (⟨0, 1⟩ : Ival).has ((condBit c fl).setWidth 64).toNat
    unfold condBit
    split <;> exact ⟨Nat.zero_le _, by decide⟩

/-! ## Three operands: the halves of a product or a quotient -/

/-- **The range of a half of a product or quotient**: of a quotient by a
divisor seen not to be nought, where the high half of the dividend is
nought, the least by the most, and the most by the least; of what is left,
less than the most the divisor can be; and otherwise what the width holds,
or the half as it was where the machine would fault. -/
def Tri.ival : Tri → Ival → Ival → Ival → Ival
  | .mulLo .div w, H, L, S =>
    if (H.cut w.bits).hi = 0 ∧ 0 < (S.cut w.bits).lo then
      ⟨(L.cut w.bits).lo / (S.cut w.bits).hi, (L.cut w.bits).hi / (S.cut w.bits).lo⟩
    else ⟨0, max (2 ^ w.bits - 1) L.hi⟩
  | .mulHi .div w, H, _, S =>
    if 0 < (S.cut w.bits).lo then ⟨0, max ((S.cut w.bits).hi - 1) H.hi⟩
    else ⟨0, max (2 ^ w.bits - 1) H.hi⟩
  | .mulLo _ w, _, L, _ => ⟨0, max (2 ^ w.bits - 1) L.hi⟩
  | .mulHi _ w, H, _, _ => ⟨0, max (2 ^ w.bits - 1) H.hi⟩

/-- A half is one the width holds, or the half as it was. -/
theorem tri_lo_or (op : MulDivOp) (w : Width) (h l s : BitVec 64) :
    (Tri.eval (.mulLo op w) h l s).toNat < 2 ^ w.bits ∨ Tri.eval (.mulLo op w) h l s = l := by
  rw [Tri.eval]
  generalize op.eval (h.setWidth w.bits) (l.setWidth w.bits) (s.setWidth w.bits) = r
  cases r with
  | next p => obtain ⟨x, y, z⟩ := p; exact .inl (by rw [toNat_wide]; exact BitVec.isLt _)
  | fault _ => exact .inr rfl
  | exit _ => exact .inr rfl
  | stuck => exact .inr rfl

theorem tri_hi_or (op : MulDivOp) (w : Width) (h l s : BitVec 64) :
    (Tri.eval (.mulHi op w) h l s).toNat < 2 ^ w.bits ∨ Tri.eval (.mulHi op w) h l s = h := by
  rw [Tri.eval]
  generalize op.eval (h.setWidth w.bits) (l.setWidth w.bits) (s.setWidth w.bits) = r
  cases r with
  | next p => obtain ⟨x, y, z⟩ := p; exact .inl (by rw [toNat_wide]; exact BitVec.isLt _)
  | fault _ => exact .inr rfl
  | exit _ => exact .inr rfl
  | stuck => exact .inr rfl

theorem lo_or_has {w : Width} {L : Ival} {l v : BitVec 64} (hl : L.has l.toNat)
    (h : v.toNat < 2 ^ w.bits ∨ v = l) : (⟨0, max (2 ^ w.bits - 1) L.hi⟩ : Ival).has v.toNat := by
  refine ⟨Nat.zero_le _, ?_⟩
  rcases h with h | rfl
  · dsimp only; omega
  · have := hl.2; dsimp only; omega

/-- What a division at a width gives, where it does not fault. -/
theorem div_next {n : Nat} {h l s q r : BitVec n} {f : Flags}
    (e : MulDivOp.eval .div h l s = .next (q, r, f)) :
    s.toNat ≠ 0 ∧ q.toNat = (h ++ l).toNat / s.toNat ∧ r.toNat = (h ++ l).toNat % s.toNat := by
  unfold MulDivOp.eval at e
  simp only at e
  split at e
  · cases e
  · next hnf =>
    cases e
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hnf
    obtain ⟨hs0, hq⟩ := hnf
    have hst : (s.setWidth (n + n)).toNat = s.toNat := by
      rw [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
    have hsn : s.toNat ≠ 0 := fun h0 => hs0 (BitVec.eq_of_toNat_eq (by simpa using h0))
    refine ⟨hsn, ?_, ?_⟩
    · have := congrArg BitVec.toNat hq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_udiv, hst] at this
      rw [BitVec.toNat_setWidth, BitVec.toNat_udiv, hst]
      have hlt := Nat.mod_lt ((h ++ l).toNat / s.toNat) (Nat.two_pow_pos n)
      have hlt2 : (h ++ l).toNat / s.toNat % 2 ^ n < 2 ^ (n + n) :=
        Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.mod_eq_of_lt hlt2] at this
      exact this
    · rw [BitVec.toNat_setWidth, BitVec.toNat_umod, hst]
      have hm := Nat.mod_lt (h ++ l).toNat (Nat.pos_of_ne_zero hsn)
      exact Nat.mod_eq_of_lt (Nat.lt_trans hm s.isLt)

theorem Tri.ival_has (o : Tri) {H L S : Ival} {h l s : BitVec 64} (hh : H.has h.toNat)
    (hl : L.has l.toNat) (hs : S.has s.toNat) : (o.ival H L S).has (o.eval h l s).toNat := by
  cases o with
  | mulLo op w =>
    cases op with
    | div =>
      show (if (H.cut w.bits).hi = 0 ∧ 0 < (S.cut w.bits).lo then
          (⟨(L.cut w.bits).lo / (S.cut w.bits).hi, (L.cut w.bits).hi / (S.cut w.bits).lo⟩ : Ival)
        else ⟨0, max (2 ^ w.bits - 1) L.hi⟩).has (Tri.eval (.mulLo .div w) h l s).toNat
      split
      · next hc =>
        have cH := Ival.cut_has (n := w.bits) hh
        have cL := Ival.cut_has (n := w.bits) hl
        have cS := Ival.cut_has (n := w.bits) hs
        have h0 : (h.setWidth w.bits).toNat = 0 := by
          rw [toNat_cut]; have := cH.2; omega
        have happ : (h.setWidth w.bits ++ l.setWidth w.bits).toNat = (l.setWidth w.bits).toNat := by
          rw [BitVec.toNat_append, h0, Nat.zero_shiftLeft, Nat.zero_or]
        rw [Tri.eval]
        generalize he : MulDivOp.eval .div (h.setWidth w.bits) (l.setWidth w.bits)
          (s.setWidth w.bits) = r
        cases r with
        | next p =>
          obtain ⟨q, r, f⟩ := p
          obtain ⟨hsn, hq, -⟩ := div_next he
          show (⟨_, _⟩ : Ival).has (wide q).toNat
          rw [toNat_wide, hq, happ, toNat_cut, toNat_cut]
          rw [toNat_cut] at hsn
          refine ⟨?_, ?_⟩
          · exact Nat.div_le_div cL.1 cS.2 hsn
          · exact Nat.div_le_div cL.2 cS.1 (by omega)
        | exit _ =>
          exfalso
          unfold MulDivOp.eval at he
          simp only at he
          split at he <;> cases he
        | stuck =>
          exfalso
          unfold MulDivOp.eval at he
          simp only at he
          split at he <;> cases he
        | fault _ =>
          exfalso
          unfold MulDivOp.eval at he
          simp only at he
          split at he
          · next hf =>
            simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hf
            rcases hf with hf | hf
            · have h1 : (s.setWidth w.bits).toNat = 0 := by rw [hf]; rfl
              rw [toNat_cut] at h1
              have := cS.1
              have := hc.2
              omega
            · apply hf
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_udiv, happ]
              have hsd : ((s.setWidth w.bits).setWidth (w.bits + w.bits)).toNat
                  = (s.setWidth w.bits).toNat := by
                rw [BitVec.toNat_setWidth]
                exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
                  (Nat.pow_le_pow_right (by omega) (by omega)))
              rw [hsd]
              have hq : (l.setWidth w.bits).toNat / (s.setWidth w.bits).toNat < 2 ^ w.bits :=
                Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (BitVec.isLt _)
              rw [Nat.mod_eq_of_lt hq]
              exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hq
                (Nat.pow_le_pow_right (by omega) (by omega)))
          · cases he
      · exact lo_or_has hl (tri_lo_or _ _ _ _ _)
    | mul => exact lo_or_has hl (tri_lo_or _ _ _ _ _)
    | imul => exact lo_or_has hl (tri_lo_or _ _ _ _ _)
    | idiv => exact lo_or_has hl (tri_lo_or _ _ _ _ _)
  | mulHi op w =>
    cases op with
    | div =>
      show (if 0 < (S.cut w.bits).lo then (⟨0, max ((S.cut w.bits).hi - 1) H.hi⟩ : Ival)
        else ⟨0, max (2 ^ w.bits - 1) H.hi⟩).has (Tri.eval (.mulHi .div w) h l s).toNat
      split
      · next hc =>
        have cS := Ival.cut_has (n := w.bits) hs
        refine ⟨Nat.zero_le _, ?_⟩
        rw [Tri.eval]
        generalize he : MulDivOp.eval .div (h.setWidth w.bits) (l.setWidth w.bits)
          (s.setWidth w.bits) = res
        cases res with
        | next p =>
          obtain ⟨q, r, f⟩ := p
          obtain ⟨hsn, -, hr⟩ := div_next he
          show (wide r).toNat ≤ _
          rw [toNat_wide, hr]
          have hm := Nat.mod_lt (h.setWidth w.bits ++ l.setWidth w.bits).toNat (Nat.pos_of_ne_zero hsn)
          rw [toNat_cut] at hm
          have := cS.2
          dsimp only
          rw [toNat_cut]
          omega
        | fault _ => have := hh.2; dsimp only; omega
        | exit _ => have := hh.2; dsimp only; omega
        | stuck => have := hh.2; dsimp only; omega
      · exact lo_or_has hh (tri_hi_or _ _ _ _ _)
    | mul => exact lo_or_has hh (tri_hi_or _ _ _ _ _)
    | imul => exact lo_or_has hh (tri_hi_or _ _ _ _ _)
    | idiv => exact lo_or_has hh (tri_hi_or _ _ _ _ _)

/-! ## A term -/

/-- Both: what is so of each. -/
def Ival.meet (A B : Ival) : Ival := ⟨max A.lo B.lo, min A.hi B.hi⟩

theorem Ival.meet_has {A B : Ival} {x : Nat} (ha : A.has x) (hb : B.has x) : (A.meet B).has x :=
  ⟨by have := ha.1; have := hb.1; simp only [Ival.meet]; omega,
    by have := ha.2; have := hb.2; simp only [Ival.meet]; omega⟩

/-- That the ranges some things known say of terms are so. -/
def RangesHold (ρ : Env) (K : List (Val × TyS)) : Prop :=
  ∀ g ∈ K, ∀ lo hi, g.2 = .range lo hi → g.1.den ρ - lo ≤ hi - lo

theorem rangesHold_nil (ρ : Env) : RangesHold ρ [] := fun _ h => nomatch h

theorem rangesHold_of {ρ : Env} {K : List (Val × TyS)} {fetch : Fetch} {sys : Syscall}
    {Ψ : MemTy} {n : Nat} (hg : ∀ g ∈ K, HasTy fetch sys Ψ n (g.2.den ρ) (g.1.den ρ)) :
    RangesHold ρ K := fun g hgm lo hi hτ => by
  have := hg g hgm
  rw [hτ] at this
  exact hasTy_range.mp this

/-- What things known say of a term's range: of each range known of it that
does not go round, that it lies there. -/
def knownIval (K : List (Val × TyS)) (v : Val) : Ival :=
  K.foldl (fun I f =>
    if f.1 == v then
      match f.2 with
      | .range lo hi => if lo ≤ hi then I.meet ⟨lo.toNat, hi.toNat⟩ else I
      | _ => I
    else I) Ival.full

theorem knownIval_has {K : List (Val × TyS)} {v : Val} {ρ : Env} (hK : RangesHold ρ K) :
    (knownIval K v).has (v.den ρ).toNat := by
  unfold knownIval
  have key : ∀ (L : List (Val × TyS)) (I : Ival), RangesHold ρ L →
      I.has (v.den ρ).toNat →
      (L.foldl (fun I f =>
        if f.1 == v then
          match f.2 with
          | .range lo hi => if lo ≤ hi then I.meet ⟨lo.toNat, hi.toNat⟩ else I
          | _ => I
        else I) I).has (v.den ρ).toNat := by
    intro L
    induction L with
    | nil => exact fun _ _ h => h
    | cons f L ih =>
      intro I hL hI
      refine ih _ (fun g hg' => hL g (List.mem_cons_of_mem _ hg')) ?_
      dsimp only
      split
      · next heq =>
        have hv : f.1 = v := by simpa using heq
        split
        · next lo hi hτ =>
          split
          · next hle =>
            refine Ival.meet_has hI ?_
            have hr := hL f List.mem_cons_self lo hi hτ
            rw [hv] at hr
            simp only [Ival.has]
            constructor <;> bv_omega
          · exact hI
        · exact hI
      · exact hI
  exact key K _ hK (Ival.full_has _)

/-- **The least and the most a term can be**: by what each operator does to
the least and the most its operands can be, and by what is known of the
term and of each term it is made of. -/
def Val.ival (K : List (Val × TyS)) : Val → Ival
  | .lit v => ⟨v.toNat, v.toNat⟩
  | .un o a => (o.ival (a.ival K)).meet (knownIval K (.un o a))
  | .bin o a b => (o.ival (a.ival K) (b.ival K) b).meet (knownIval K (.bin o a b))
  | .tri o h l s => (o.ival (h.ival K) (l.ival K) (s.ival K)).meet (knownIval K (.tri o h l s))
  | .fop o fl a b => (o.ival (a.ival K) (b.ival K)).meet (knownIval K (.fop o fl a b))
  | v => knownIval K v

theorem Val.ival_has {K : List (Val × TyS)} {ρ : Env} (hg : RangesHold ρ K) :
    (v : Val) → (v.ival K).has (v.den ρ).toNat
  | .lit _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | .un o a => Ival.meet_has (Un.ival_has o (Val.ival_has hg a)) (knownIval_has hg)
  | .bin o a b => Ival.meet_has (Bin.ival_has o b (Val.ival_has hg a) (Val.ival_has hg b))
      (knownIval_has hg)
  | .tri o h l s => Ival.meet_has (Tri.ival_has o (Val.ival_has hg h) (Val.ival_has hg l)
      (Val.ival_has hg s)) (knownIval_has hg)
  | .fop o fl a b => Ival.meet_has (FOp.ival_has o (fl.den ρ) (Val.ival_has hg a)
      (Val.ival_has hg b)) (knownIval_has hg)
  | .var _ => knownIval_has hg
  | .bvar _ _ => knownIval_has hg
  | .slot _ => knownIval_has hg
  | .app _ _ _ => knownIval_has hg

end TypedAsm.U
