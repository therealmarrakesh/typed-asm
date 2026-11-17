import TypedAsm.U.TyS
import TypedAsm.U.Regs
import TypedAsm.U.Mem

/-!
# Contexts as terms

A context is written as data: the term each register holds, the term for
the flags, and the regions held alone with the terms for the values in
them. Here is what such a context stands for, the address an operand names
as a term, and the terms an instruction is given and gives: those of the
registers its description uses, and one for each register it writes.
-/

namespace TypedAsm.U

open TypedAsm

/-- A context, as terms. -/
structure CtxS where
  regs : Regs Val
  flags : FlagsT
  held : List (Val × HeldS) := []
  /-- What is known of values. -/
  known : List (Val × TyS) := []
  /-- Whatever else is held, where there may be more. -/
  rest : RestS := .none


/-- The context a context written as terms stands for. -/
def CtxS.den (ρ : Env) (Γ : CtxS) : Ctx where
  val r := (Γ.regs.get r).den ρ
  flags := Γ.flags.den ρ
  held := (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest
  known := Γ.known.map fun f => (f.1.den ρ, f.2.den ρ)

/-- A context knowing more. -/
def CtxS.addKnown (Γ : CtxS) (fs : List (Val × TyS)) : CtxS := { Γ with known := fs ++ Γ.known }

/-- The address a memory operand names, as a term. -/
def eaS (regs : Regs Val) (next : BitVec 64) : Mem → Val
  | .sib base index disp =>
    let b : Val := match base with
      | some r => regs.get r
      | none => .lit 0
    let i : Val := match index with
      | some (r, scale) => .shl (regs.get r.toReg) scale.shift
      | none => .lit 0
    .add (.add b i) (.lit (disp.signExtend 64))
  | .rip disp => .lit (next + disp.signExtend 64)

theorem eaS_den (ρ : Env) (Γ : CtxS) (next : BitVec 64) (m : Mem) :
    (eaS Γ.regs next m).den ρ = eaOf (Γ.den ρ).val next m := by
  cases m with
  | sib base index disp => cases base <;> cases index <;> rfl
  | rip disp => rfl

/-- The term for the `j`th register a description uses. -/
def argAt (regs : Regs Val) (srcs : List Reg) (j : Nat) : Val :=
  match srcs[j]? with
  | some r => regs.get r
  | none => .lit 0

theorem ctx_ext {Γ Δ : Ctx} (hv : Γ.val = Δ.val) (hf : Γ.flags = Δ.flags) (hh : Γ.held = Δ.held)
    (hk : Γ.known = Δ.known) : Γ = Δ := by
  cases Γ; cases Δ
  simp only at hv hf hh hk
  subst hv hf hh hk
  rfl

theorem Steps.mono {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {i : Instr} {next : BitVec 64}
    {Γ : Ctx} {Q Q' : BitVec 64 → Ctx → Prop} (h : Steps fetch sys Ψ i next Γ Q)
    (hQ : ∀ t Δ, Q t Δ → Q' t Δ) : Steps fetch sys Ψ i next Γ Q' := by
  intro n Ψ' he hwf s hrip hw
  obtain ⟨s', hex, Γ', hq, hw'⟩ := h n Ψ' he hwf s hrip hw
  exact ⟨s', hex, Γ', hQ _ _ hq, hw'⟩

end TypedAsm.U
