import TypedAsm.U.FlagsS
import TypedAsm.U.Bridge

/-!
# What an instruction needs so as not to fault of itself

Most instructions fault only if memory they touch may not be touched. A
few can fault for a reason of their own: an operation that reads a flag,
where the flag is undefined; a divide, by its divisor. Here is which flags
each needs defined, as a table, and that an instruction whose flags are
defined does not fault of itself. A divide is not in the table: what it
needs is of its operands, and is left to be shown.
-/

namespace TypedAsm.U

open TypedAsm

/-- The flags an instruction needs defined so as not to fault of itself;
nothing where that is not all it needs. -/
def _root_.TypedAsm.Instr.needs : Instr → Option (List Flag)
  | .alu .adc _ _ | .alu .sbb _ _ => some [.cf]
  | .cmov c _ _ _ | .setcc c _ | .jcc c _ => some c.uses
  | .mulDiv .mul _ _ | .mulDiv .imul _ _ => some []
  | .mulDiv _ _ _ | .ud2 | .syscall => none
  | _ => some []

theorem all_cf {fl : Flags} (h : ([Flag.cf].all fun x => (fl.get x).isSome) = true) :
    fl.cf.isSome = true := by
  simpa [Flags.get] using h

theorem desc1_needs {i : Instr} {d : Desc1} {xs : List Flag} (hn : i.needs = some xs)
    (hd : i.desc1 = some d) (vals : List (BitVec 64)) (fl : Flags) (a c : BitVec 64)
    (hfl : (xs.all fun x => (fl.get x).isSome) = true) : d.guard vals fl a c = true := by
  cases i with
  | alu op w ops =>
    cases hd
    cases op <;> first
      | rfl
      | (cases hn
         obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (all_cf hfl)
         show (Option.map _ fl.cf).isSome = true
         rw [hb]; rfl)
  | unary op w dst => cases op <;> cases hd <;> rfl
  | mulDiv op w src =>
    cases op
    · cases hd; rfl
    · cases hd; rfl
    · cases hn
    · cases hn
  | cmov cnd w dst src => cases hd; cases hn; exact cnd.eval_isSome fl hfl
  | setcc cnd dst => cases hd; cases hn; exact cnd.eval_isSome fl hfl
  | jmp t => cases hd
  | jcc cnd rel => cases hd
  | call t => cases hd
  | ret => cases hd
  | ud2 => cases hd
  | syscall => cases hd
  | _ => cases hd; rfl

/-- **An instruction whose flags are defined does not fault of itself**,
whatever else it is run on. -/
theorem desc_needs {i : Instr} {d : Desc} {xs : List Flag} (hn : i.needs = some xs)
    (hd : i.desc = some d) (vals : List (BitVec 64)) (fl : Flags) (next a c : BitVec 64)
    (hfl : (xs.all fun x => (fl.get x).isSome) = true) : d.guard vals fl next a c = true := by
  cases hi : i.desc1 with
  | some d₁ =>
    have e : d = d₁.toDesc := Option.some.inj ((desc_of_desc1 hi).symm.trans hd).symm
    subst e
    exact desc1_needs hn hi vals fl a c hfl
  | none =>
    cases i with
    | jmp t => rcases t with rel | (r | m) <;> cases hd <;> rfl
    | jcc cnd rel => cases hd; cases hn; exact cnd.eval_isSome fl hfl
    | call t => rcases t with rel | (r | m) <;> cases hd <;> rfl
    | ret => cases hd; rfl
    | unary op w dst => cases op <;> cases hi
    | _ => first | (cases hi; done) | (cases hd; done)

/-- Whether what an instruction needs so as not to fault of itself holds, as
far as the term for the flags shows. A quotient is not yet shown to fit. -/
def GuardE.okS : GuardE → FlagsT → Bool
  | .none, _ => true
  | .cond c, fl => fl.decides c
  | .alu op _, fl => if op.carryIn then fl.defined .cf else true
  | .mul .mul _, _ | .mul .imul _, _ => true
  | .mul _ _, _ => false

theorem GuardE.okS_den (ρ : Env) {g : GuardE} {fl : FlagsT} (h : g.okS fl = true)
    (a b c : BitVec 64) : g.eval (fl.den ρ) a b c = true := by
  cases g with
  | none => rfl
  | cond cnd =>
    obtain ⟨v, hv⟩ := FlagsT.decides_den ρ fl cnd h
    show (cnd.eval (fl.den ρ)).isSome = true
    rw [hv]; rfl
  | alu op w =>
    cases op <;> first
      | rfl
      | (obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (FlagsT.defined_den ρ fl .cf h)
         have hv : (fl.den ρ).cf = some v := hv
         show (AluOp.eval _ (fl.den ρ).cf _ _).isSome = true
         rw [hv]; rfl)
  | mul op w =>
    cases op
    · rfl
    · rfl
    · cases h
    · cases h

/-- Whether an instruction does not fault of itself, as far as the term for
the flags shows. -/
def guardS (i : Instr) (fl : FlagsT) : Bool :=
  match i.sem with
  | some s => s.guard.okS fl
  | none => false

theorem guardS_den (ρ : Env) {i : Instr} {fl : FlagsT} (h : guardS i fl = true) {d : Desc}
    (hd : i.desc = some d) (vals : List (BitVec 64)) (next a c : BitVec 64) :
    d.guard vals (fl.den ρ) next a c = true := by
  unfold guardS at h
  cases hs : i.sem with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    have e : d = s.toDesc := by
      rw [← sem_desc, hs] at hd
      exact (Option.some.inj hd).symm
    subst e
    exact GuardE.okS_den ρ h _ _ _

end TypedAsm.U
