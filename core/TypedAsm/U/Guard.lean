import TypedAsm.U.FlagsS
import TypedAsm.U.Bridge

/-!
# What an instruction needs so as not to fault of itself

Most instructions fault only if memory they touch may not be touched. A
few can fault for a reason of their own: an operation that takes a flag in,
where the flag is undefined; a divide, by its divisor. An instruction's
description says which, as data. Here is whether it holds, as far as the
term for the flags shows, and that an instruction of which it holds does
not fault of itself.
-/

namespace TypedAsm.U

open TypedAsm

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
