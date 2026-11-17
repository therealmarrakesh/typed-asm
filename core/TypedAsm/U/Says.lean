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

theorem FlagKind.cond_eval {k : FlagKind} {w : Width} {x y : BitVec w.bits} {F : Flags}
    (hF : k.Holds x y F) (hres : k = .res → y = x) {c : Cond} {f : Form}
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

theorem flagSrc_res {i : Instr} {w : Width} {A B : Opnd} (h : i.flagSrc = some (.res, w, A, B)) :
    B = A := by
  cases i with
  | alu op w' ops => cases op <;> cases h <;> rfl
  | test w' dst src => cases src <;> cases h
  | unary op w' dst => cases op <;> cases h
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
  | _, _ => none

theorem FlagsT.says_den (ρ : Env) {t : FlagsT} {cnd : Cond} {p : CmpT} (h : t.says cnd = some p) :
    cnd.eval (t.den ρ) = some (p.den ρ) := by
  cases t with
  | lit f => cases h
  | var j => cases h
  | bvar _ => cases h
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
        refine FlagKind.cond_eval (flagSrc_sound hs _ _ _ _ _ _ _) (fun hk => ?_) hc
        subst hk
        rw [flagSrc_res hs]

end TypedAsm.U
