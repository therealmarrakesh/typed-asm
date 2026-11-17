import TypedAsm.U.FlagSrc

/-!
# What a condition says, as a term

A comparison between two operands at a width, as data; and, for the flags
an instruction left, the comparison a condition on them comes to.
-/

namespace TypedAsm.U

open TypedAsm

/-- An operand of a comparison: a value, of which the low bits are taken; a
number written in the instruction; or zero. -/
inductive OpT
  | val (v : Val)
  | imm (i : BitVec 32)
  | zero
  deriving DecidableEq

def OpT.den (ρ : Env) (w : Width) : OpT → BitVec w.bits
  | .val v => (v.den ρ).setWidth w.bits
  | .imm i => i.signExtend w.bits
  | .zero => 0

/-- A comparison of two operands at a width. -/
structure CmpT where
  form : Form
  w : Width
  a : OpT
  b : OpT
  deriving DecidableEq

def CmpT.den (ρ : Env) (p : CmpT) : Bool := p.form.eval (p.a.den ρ p.w) (p.b.den ρ p.w)

/-- What a condition comes to, for flags come by in each way. -/
def FlagKind.cond : FlagKind → Cond → Option Form
  | .sub, c => condSub c
  | .tst, c => some (condTst c)
  | .res, .e => some ⟨false, .tstz, false⟩
  | .res, .ne => some ⟨true, .tstz, false⟩
  | .res, .s => some ⟨false, .tstneg, false⟩
  | .res, .ns => some ⟨true, .tstneg, false⟩
  | .res, _ => none
  | .zero, c => some (condZero c)

theorem FlagKind.cond_eval {k : FlagKind} {w : Width} {x y : BitVec w.bits} {F : Flags}
    (hF : k.Holds x y F) (hres : k = .res → y = x) (hzero : k = .zero → y = x) {c : Cond}
    {f : Form}
    (h : k.cond c = some f) : c.eval F = some (f.eval x y) := by
  cases k with
  | sub => cases hF; exact condSub_eval w x y h
  | tst => cases hF; cases h; exact condTst_eval x y c
  | res =>
    obtain ⟨hz, hs⟩ := hF
    cases hres rfl
    have hand : x &&& x = x := BitVec.and_self
    cases c <;> cases h
    · show F.zf = some (x &&& x == 0); rw [hand]; exact hz
    · show F.zf.map (!·) = some (!(x &&& x == 0)); rw [hand, hz]; rfl
    · show F.sf = some (x &&& x).msb; rw [hand]; exact hs
    · show F.sf.map (!·) = some (!(x &&& x).msb); rw [hand, hs]; rfl
  | zero =>
    cases hF
    cases hzero rfl
    cases h
    exact condZero_eval x c

/-- An operand of an instruction, as a term. -/
def Opnd.term (i : Instr) (a b c : Val) (fl : FlagsT) (next : BitVec 64) (ea cell : Val) :
    Opnd → OpT
  | .arg 0 => .val a
  | .arg 1 => .val b
  | .arg 2 => .val c
  | .arg _ => .zero
  | .cell => .val cell
  | .imm v => .imm v
  | .zero => .zero
  | .out => .val (.out i 0 a b c fl next ea cell)
  | .stored => .val (.stored i a b c fl next ea cell)

theorem Opnd.term_den (ρ : Env) (i : Instr) (a b c : Val) (fl : FlagsT) (next : BitVec 64)
    (ea cell : Val) (w : Width) (o : Opnd) :
    (o.term i a b c fl next ea cell).den ρ w
      = o.sem i [a.den ρ, b.den ρ, c.den ρ] (fl.den ρ) next (ea.den ρ) (cell.den ρ) w := by
  cases o with
  | arg j =>
    rcases j with _ | _ | _ | j
    · rfl
    · rfl
    · rfl
    · show (0 : BitVec w.bits) = BitVec.setWidth w.bits 0
      simp
  | _ => rfl

theorem flagSrc_zero {i : Instr} {w : Width} {A B : Opnd}
    (h : i.flagSrc = some (.zero, w, A, B)) : B = A := by
  cases i with
  | alu op w' ops => cases op <;> cases h
  | test w' dst src => cases src <;> cases h
  | unary op w' dst => cases op <;> cases h
  | popcnt w' dst src => cases h; rfl
  | shift op w' dst cnt =>
    cases cnt with
    | cl => cases h
    | imm c =>
      by_cases hc : c.toNat % w'.bits = 0
      · simp only [Instr.flagSrc, hc, ↓reduceIte] at h
        cases h
      · simp only [Instr.flagSrc, hc, ↓reduceIte] at h
        cases op <;> cases h
  | _ => cases h

theorem flagSrc_res {i : Instr} {w : Width} {A B : Opnd} (h : i.flagSrc = some (.res, w, A, B)) :
    B = A := by
  cases i with
  | alu op w' ops => cases op <;> cases h <;> rfl
  | test w' dst src => cases src <;> cases h
  | unary op w' dst => cases op <;> cases h
  | shift op w' dst cnt =>
    cases cnt with
    | cl => cases h
    | imm c =>
      by_cases hc : c.toNat % w'.bits = 0
      · simp only [Instr.flagSrc, hc, ↓reduceIte] at h
        cases h
      · simp only [Instr.flagSrc, hc, ↓reduceIte] at h
        cases op <;> first | (cases h; rfl) | (cases h; done)
  | _ => cases h

/-- A comparison of a value with itself, where a condition has a form for
flags that say whether a result is nought and whether it is negative. -/
def resCmp (w : Width) (r : Val) (cnd : Cond) : Option CmpT :=
  (FlagKind.res.cond cnd).map fun f => ⟨f, w, .val r, .val r⟩

/-- **What a condition comes to, for each way flags arise**: of the values
the flags arose from, or of the result. -/
def FSrc.says (o : FSrc) (fl : FlagsT) (a b : Val) (cnd : Cond) : Option CmpT :=
  match o with
  | .alu .sub w | .alu .cmp w => (condSub cnd).map fun f => ⟨f, w, .val a, .val b⟩
  | .alu .and w | .test w => some ⟨condTst cnd, w, .val a, .val b⟩
  | .alu .add w => resCmp w (mkFop (.alu .add w) fl a b) cnd
  | .alu .or w => resCmp w (mkFop (.alu .or w) fl a b) cnd
  | .alu .xor w => resCmp w (mkFop (.alu .xor w) fl a b) cnd
  | .neg w => (condSub cnd).map fun f => ⟨f, w, .zero, .val a⟩
  | .popcnt w => some ⟨condZero cnd, w, .val a, .val a⟩
  | .shift op w =>
    match b.lit? with
    | some n =>
      if n.toNat % w.bits = 0 then none
      else
        match op with
        | .shl | .shr | .sar => resCmp w (mkBin (.shift op w) a b) cnd
        | _ => none
    | none => none
  | _ => none

theorem resCmp_den {ρ : Env} {w : Width} {r : Val} {cnd : Cond} {p : CmpT} {F : Flags}
    (h : resCmp w r cnd = some p)
    (hF : FlagKind.res.Holds ((r.den ρ).setWidth w.bits) ((r.den ρ).setWidth w.bits) F) :
    cnd.eval F = some (p.den ρ) := by
  unfold resCmp at h
  cases hc : FlagKind.res.cond cnd with
  | none => rw [hc] at h; cases h
  | some f =>
    rw [hc] at h
    cases h
    exact FlagKind.cond_eval hF (fun _ => rfl) (fun _ => rfl) hc

theorem FSrc.says_den (ρ : Env) {o : FSrc} {fl : FlagsT} {a b : Val} {cnd : Cond} {p : CmpT}
    (h : o.says fl a b cnd = some p) (c : BitVec 64) :
    cnd.eval (o.eval (fl.den ρ) (a.den ρ) (b.den ρ) c) = some (p.den ρ) := by
  have sub : ∀ {w : Width} {A B : OpT} {F : Flags},
      (condSub cnd).map (fun f => (⟨f, w, A, B⟩ : CmpT)) = some p →
      F = (subBorrow (A.den ρ w) (B.den ρ w) false).2 → cnd.eval F = some (p.den ρ) := by
    intro w A B F h hF
    cases hc : condSub cnd with
    | none => rw [hc] at h; cases h
    | some f =>
      rw [hc] at h
      cases h
      subst hF
      exact condSub_eval w _ _ hc
  have res : ∀ {w : Width} {op : AluOp}, (op = .add ∨ op = .or ∨ op = .xor) →
      resCmp w (mkFop (.alu op w) fl a b) cnd = some p →
      cnd.eval ((FSrc.alu op w).eval (fl.den ρ) (a.den ρ) (b.den ρ) c) = some (p.den ρ) := by
    intro w op hop h
    refine resCmp_den h ?_
    rw [mkFop_den]
    rcases hop with rfl | rfl | rfl <;>
      exact ⟨by show some _ = some ((wide _).setWidth _ == 0); rw [wide_low]; rfl,
        by show some _ = some ((wide _).setWidth _).msb; rw [wide_low]; rfl⟩
  cases o with
  | alu op w =>
    cases op with
    | sub => exact sub h rfl
    | cmp => exact sub h rfl
    | and => cases h; exact condTst_eval _ _ cnd
    | add => exact res (.inl rfl) h
    | or => exact res (.inr (.inl rfl)) h
    | xor => exact res (.inr (.inr rfl)) h
    | _ => cases h
  | test w => cases h; exact condTst_eval _ _ cnd
  | neg w => exact sub h rfl
  | popcnt w => cases h; exact condZero_eval _ cnd
  | shift op w =>
    simp only [FSrc.says] at h
    cases hb : b.lit? with
    | none => rw [hb] at h; cases h
    | some n =>
      rw [hb] at h
      simp only at h
      have hbn : b.den ρ = n := Val.lit?_den hb
      by_cases hc : n.toNat % w.bits = 0
      · simp only [hc, ↓reduceIte] at h
        cases h
      · simp only [hc, ↓reduceIte] at h
        have hop : op = .shl ∨ op = .shr ∨ op = .sar := by
          cases op with
          | shl => exact .inl rfl
          | shr => exact .inr (.inl rfl)
          | sar => exact .inr (.inr rfl)
          | rol => cases h
          | ror => cases h
        have h' : resCmp w (mkBin (.shift op w) a b) cnd = some p := by
          rcases hop with rfl | rfl | rfl <;> exact h
        refine resCmp_den h' ?_
        rw [mkBin_den]
        have key := shift_res hop (fl.den ρ) ((a.den ρ).setWidth w.bits) (c := (b.den ρ).toNat % w.bits)
          (by rw [hbn]; exact hc)
        rw [shift_fst op (fl.den ρ)] at key
        refine ⟨?_, ?_⟩
        · show (ShiftOp.eval op (fl.den ρ) _ _).2.zf = some ((wide _).setWidth _ == 0)
          rw [wide_low]; exact key.1
        · show (ShiftOp.eval op (fl.den ρ) _ _).2.sf = some ((wide _).setWidth _).msb
          rw [wide_low]; exact key.2
  | _ => cases h

/-- **What a condition on the flags comes to**, where the flags are those an
instruction left and the table says where they came from. -/
def FlagsT.says : FlagsT → Cond → Option CmpT
  | .out i a b c fl next ea cell, cnd =>
    match i.flagSrc with
    | some (k, w, A, B) =>
      match k.cond cnd with
      | some f => some ⟨f, w, A.term i a b c fl next ea cell, B.term i a b c fl next ea cell⟩
      | none => none
    | none => none
  | .src o fl a b _, cnd => o.says fl a b cnd
  | _, _ => none

theorem FlagsT.says_den (ρ : Env) {t : FlagsT} {cnd : Cond} {p : CmpT} (h : t.says cnd = some p) :
    cnd.eval (t.den ρ) = some (p.den ρ) := by
  cases t with
  | lit f => cases h
  | var j => cases h
  | bvar _ => cases h
  | old => cases h
  | src o fl a b c => exact FSrc.says_den ρ h (c.den ρ)
  | out i a b c fl next ea cell =>
    rw [FlagsT.says] at h
    cases hs : i.flagSrc with
    | none => rw [hs] at h; cases h
    | some q =>
      obtain ⟨k, w, A, B⟩ := q
      rw [hs] at h
      simp only at h
      cases hc : k.cond cnd with
      | none => rw [hc] at h; cases h
      | some f =>
        rw [hc] at h
        cases h
        show cnd.eval (effectOf i _ (fl.den ρ) next _ _).flags = some (f.eval _ _)
        rw [Opnd.term_den, Opnd.term_den]
        refine FlagKind.cond_eval (flagSrc_sound hs _ _ _ _ _ _ _) (fun hk => ?_) (fun hk => ?_) hc
        · subst hk
          rw [flagSrc_res hs]
        · subst hk
          rw [flagSrc_zero hs]

end TypedAsm.U
