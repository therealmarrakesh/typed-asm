import TypedAsm.U.Term
import TypedAsm.U.FlagFate

/-!
# What is known of the flags, from their term

Whether a flag is defined, looked up through the instructions the term
records; whether a condition can therefore be decided; and the flags an
instruction leaves, said as the flags before it where it touches none.
-/

namespace TypedAsm.U

open TypedAsm

/-- An instruction with no description does nothing that can be said to
any flag. -/
theorem fate_of_no_desc {i : Instr} (h : i.desc = none) (x : Flag) : i.fate x = .lost := by
  cases hi : i.desc1 with
  | some d₁ => rw [desc_of_desc1 hi] at h; cases h
  | none =>
    cases i with
    | jmp t => rcases t with rel | (r | m) <;> cases h
    | jcc cnd rel => cases h
    | call t => rcases t with rel | (r | m) <;> cases h
    | ret => cases h
    | ud2 => rfl
    | syscall => rfl
    | unary op w dst => cases op <;> cases hi
    | _ => cases hi

/-- Whether a flag is defined, as far as the term for the flags shows. -/
def FlagsT.defined : FlagsT → Flag → Bool
  | .lit f, x => (f.get x).isSome
  | .var _, _ => false
  | .bvar, _ => false
  | .out i _ _ _ fl _ _ _, x =>
    match i.fate x with
    | .defines => true
    | .keeps => fl.defined x
    | .lost => false

theorem FlagsT.defined_den (ρ : Env) : (t : FlagsT) → (x : Flag) → t.defined x = true →
    ((t.den ρ).get x).isSome = true
  | .lit f, x, h => h
  | .var _, _, h => nomatch h
  | .bvar, _, h => nomatch h
  | .out i a b c fl next ea cell, x, h => by
    unfold FlagsT.defined at h
    show ((effectOf i _ (fl.den ρ) next _ _).flags.get x).isSome = true
    unfold effectOf
    cases hd : i.desc with
    | none => rw [fate_of_no_desc hd] at h; cases h
    | some d =>
      have hf := desc_fate hd ([a.den ρ, b.den ρ, c.den ρ].take d.srcs.length) (fl.den ρ) next
        (ea.den ρ) (cell.den ρ) x
      cases hfate : i.fate x with
      | defines => rw [hfate] at hf; exact hf
      | keeps =>
        rw [hfate] at hf h
        show (Flags.get (d.run _ _ _ _ _).flags x).isSome = true
        rw [show Flags.get (d.run _ _ _ _ _).flags x = _ from hf]
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

/-- Whether an instruction leaves every flag as it was. -/
def _root_.TypedAsm.Instr.keepsFlags (i : Instr) : Bool :=
  i.fate .cf = .keeps && i.fate .zf = .keeps && i.fate .sf = .keeps && i.fate .of = .keeps

theorem effectOf_keepsFlags {i : Instr} (h : i.keepsFlags = true) (vals : List (BitVec 64))
    (fl : Flags) (next ea cell : BitVec 64) : (effectOf i vals fl next ea cell).flags = fl := by
  unfold effectOf
  cases hd : i.desc with
  | none => rfl
  | some d =>
    simp only [Instr.keepsFlags, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have k := fun x => desc_fate hd (vals.take d.srcs.length) fl next ea cell x
    have k1 := k .cf; have k2 := k .zf; have k3 := k .sf; have k4 := k .of
    rw [h1] at k1; rw [h2] at k2; rw [h3] at k3; rw [h4] at k4
    show (d.run _ _ _ _ _).flags = fl
    generalize (d.run _ _ _ _ _).flags = g at k1 k2 k3 k4
    cases g; cases fl
    cases k1; cases k2; cases k3; cases k4
    rfl

/-- **The flags an instruction leaves, as plainly as they can be said**: the
flags before it, where it touches none. -/
def flagsOut (i : Instr) (a b c : Val) (fl : FlagsT) (next : BitVec 64) (ea cell : Val) : FlagsT :=
  if i.keepsFlags then fl else .out i a b c fl next ea cell

theorem flagsOut_den (ρ : Env) (i : Instr) (a b c : Val) (fl : FlagsT) (next : BitVec 64)
    (ea cell : Val) :
    (flagsOut i a b c fl next ea cell).den ρ = (FlagsT.out i a b c fl next ea cell).den ρ := by
  unfold flagsOut
  split
  · next h => exact (effectOf_keepsFlags h _ _ _ _ _).symm
  · rfl

end TypedAsm.U
