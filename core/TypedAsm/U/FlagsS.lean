import TypedAsm.U.Term
import TypedAsm.U.FlagFate
import TypedAsm.U.Norm

/-!
# What is known of the flags, from their term

What each way flags arise does to each flag; whether a flag is therefore
defined, looking back through the operations the term records; and whether
a condition can therefore be decided.
-/

namespace TypedAsm.U

open TypedAsm

/-- **What each way flags arise does to each flag**, given the second
operand where it is a number written out: the count of a shift. -/
def FSrc.fate : FSrc → Option (BitVec 64) → Flag → Fate
  | .alu op _, _, _ => if op.carryIn then .definesIf .cf else .defines
  | .test _, _, _ => .defines
  | .neg _, _, _ => .defines
  | .shift op w, some n, x => shiftFate op (n.toNat % w.bits) x
  | .shift _ _, none, _ => .lost
  | .mul .mul _, _, x | .mul .imul _, _, x => mulFate x
  | .mul _ _, _, _ => .lost
  | .imul _, _, x => mulFate x
  | .popcnt _, _, _ => .defines

theorem FSrc.fate_sound (o : FSrc) (n : Option (BitVec 64)) (fl : Flags) (a b c : BitVec 64)
    (hn : ∀ v, n = some v → b = v) (x : Flag) :
    (o.fate n x).Holds fl (fl.get x) ((o.eval fl a b c).get x) := by
  cases o with
  | alu op w =>
    cases op <;> first
      | (cases x <;> rfl)
      | (intro hcf
         obtain ⟨cf, zf, sf, of⟩ := fl
         cases cf with
         | none => cases hcf
         | some c => cases x <;> rfl)
  | test w => cases x <;> rfl
  | neg w => cases x <;> rfl
  | shift op w =>
    cases n with
    | none => exact trivial
    | some v =>
      cases hn v rfl
      show (shiftFate op (b.toNat % w.bits) x).Holds fl (fl.get x)
        (Flags.get (op.eval fl _ (b.toNat % w.bits)).2 x)
      generalize b.toNat % w.bits = m
      unfold shiftFate ShiftOp.eval
      by_cases h0 : m = 0
      · simp only [h0, ↓reduceIte]; rfl
      · by_cases h1 : m = 1
        · subst h1; cases op <;> cases x <;> rfl
        · simp only [h0, h1, ↓reduceIte]
          cases op <;> cases x <;> first | exact trivial | rfl
  | mul op w =>
    cases op
    · cases x <;> first | exact trivial | rfl
    · cases x <;> first | exact trivial | rfl
    · exact trivial
    · exact trivial
  | imul w => cases x <;> first | exact trivial | rfl
  | popcnt w => cases x <;> rfl

/-- Whether a flag is defined, as far as the term for the flags shows. -/
def FlagsT.defined : FlagsT → Flag → Bool
  | .lit f, x => (f.get x).isSome
  | .var _, _ => false
  | .bvar _, _ => false
  | .old, _ => false
  | .src o fl _ b _, x =>
    match o.fate b.lit? x with
    | .defines => true
    | .definesIf y => fl.defined y
    | .keeps => fl.defined x
    | .lost => false

theorem FlagsT.defined_den (ρ : Env) : (t : FlagsT) → (x : Flag) → t.defined x = true →
    ((t.den ρ).get x).isSome = true
  | .lit f, x, h => h
  | .var _, _, h => nomatch h
  | .bvar _, _, h => nomatch h
  | .old, _, h => nomatch h
  | .src o fl a b c, x, h => by
    unfold FlagsT.defined at h
    have hf := o.fate_sound b.lit? (fl.den ρ) (a.den ρ) (b.den ρ) (c.den ρ)
      (fun v hv => Val.lit?_den hv) x
    show ((o.eval (fl.den ρ) (a.den ρ) (b.den ρ) (c.den ρ)).get x).isSome = true
    cases hfate : o.fate b.lit? x with
    | defines => rw [hfate] at hf; exact hf
    | definesIf y =>
      rw [hfate] at hf h
      exact hf (FlagsT.defined_den ρ fl y h)
    | keeps =>
      rw [hfate] at hf h
      rw [show Flags.get _ x = _ from hf]
      exact FlagsT.defined_den ρ fl x h
    | lost => rw [hfate] at h; cases h

/-- The flags a condition looks at. -/
def _root_.TypedAsm.Cond.uses : Cond → List Flag
  | .o | .no => [.of]
  | .b | .ae => [.cf]
  | .e | .ne => [.zf]
  | .be | .a => [.cf, .zf]
  | .s | .ns => [.sf]
  | .l | .ge => [.sf, .of]
  | .le | .g => [.zf, .sf, .of]

/-- A condition whose flags are defined is decided. -/
theorem _root_.TypedAsm.Cond.eval_isSome (c : Cond) (f : Flags)
    (h : (c.uses.all fun x => (f.get x).isSome) = true) : (c.eval f).isSome = true := by
  obtain ⟨cf, zf, sf, of⟩ := f
  cases c <;> cases cf <;> cases zf <;> cases sf <;> cases of <;>
    first | rfl | exact Bool.noConfusion h

/-- Whether a condition can be decided, as far as the term for the flags
shows. -/
def FlagsT.decides (t : FlagsT) (c : Cond) : Bool := c.uses.all t.defined

theorem FlagsT.decides_den (ρ : Env) (t : FlagsT) (c : Cond) (h : t.decides c = true) :
    ∃ b, c.eval (t.den ρ) = some b := by
  refine Option.isSome_iff_exists.mp (c.eval_isSome _ ?_)
  unfold FlagsT.decides at h
  rw [List.all_eq_true] at h ⊢
  exact fun x hx => FlagsT.defined_den ρ t x (h x hx)

end TypedAsm.U
