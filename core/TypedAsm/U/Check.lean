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
  /-- A name for whatever else is held, where there may be more. -/
  rest : Option Nat := none


/-- The context a context written as terms stands for. -/
def CtxS.den (ρ : Env) (Γ : CtxS) : Ctx where
  val r := (Γ.regs.get r).den ρ
  flags := Γ.flags.den ρ
  held := (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest
  known := Γ.known.map fun f => (f.1.den ρ, f.2.den ρ)

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

/-- The registers with those an instruction writes given terms, the `k`th
written the term for `k`. -/
def setOuts (mk : Nat → Val) : List Reg → Nat → Regs Val → Regs Val
  | [], _, m => m
  | r :: rs, k, m => setOuts mk rs (k + 1) (m.set r (mk k))

theorem setOuts_den (ρ : Env) (mk : Nat → Val) :
    (l : List (Reg × BitVec 64)) → (k : Nat) → (m : Regs Val) → (f : Reg → BitVec 64) →
    (∀ r, (m.get r).den ρ = f r) →
    (∀ j (hj : j < l.length), (mk (k + j)).den ρ = l[j].2) →
    ∀ r, ((setOuts mk (l.map (·.1)) k m).get r).den ρ
      = l.foldl (fun f p => fun r => if r = p.1 then p.2 else f r) f r
  | [], _, _, _, hm, _, r => hm r
  | p :: l, k, m, f, hm, hmk, r => by
    refine setOuts_den ρ mk l (k + 1) (m.set p.1 (mk k)) _ (fun r' => ?_) (fun j hj => ?_) r
    · rw [Regs.get_set]
      by_cases h : r' = p.1
      · simp only [h, ↓reduceIte]
        exact hmk 0 (Nat.zero_lt_succ _)
      · simp only [h, ↓reduceIte]
        exact hm r'
    · have := hmk (j + 1) (Nat.succ_lt_succ hj)
      rw [show k + 1 + j = k + (j + 1) by omega]
      exact this

/-- Counts the registers a description uses, on operands written out. -/
macro "len3" : tactic =>
  `(tactic| (show List.length _ ≤ 3
             simp only [rmRegs, srcRegs, Operands.dst, List.length_append, List.length_cons,
               List.length_nil, List.nil_append, List.cons_append]
             omega))

/-- No description uses more than three registers. -/
theorem desc1_srcs_le {i : Instr} {d : Desc1} (hd : i.desc1 = some d) : d.srcs.length ≤ 3 := by
  cases i with
  | alu op w ops =>
    cases hd
    rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> len3
  | test w dst src => cases hd; cases dst <;> cases src <;> len3
  | unary op w dst => cases op <;> cases hd <;> cases dst <;> len3
  | shift op w dst cnt => cases hd; cases dst <;> cases cnt <;> len3
  | mulDiv op w src => cases hd; cases src <;> len3
  | imul2 w dst src => cases hd; cases src <;> len3
  | imul3 w dst src imm => cases hd; cases src <;> len3
  | popcnt w dst src => cases hd; cases src <;> len3
  | mov w ops =>
    cases hd
    rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> len3
  | movzx w dst sw src => cases hd; cases src <;> len3
  | movsx w dst sw src => cases hd; cases src <;> len3
  | movsxd dst src => cases hd; cases src <;> len3
  | cmov cnd w dst src => cases hd; cases src <;> len3
  | setcc cnd dst => cases hd; cases dst <;> len3
  | jmp t => cases hd
  | jcc cnd rel => cases hd
  | call t => cases hd
  | ret => cases hd
  | ud2 => cases hd
  | syscall => cases hd
  | _ => cases hd; len3

theorem desc_srcs_le {i : Instr} {d : Desc} (hd : i.desc = some d) : d.srcs.length ≤ 3 := by
  cases hi : i.desc1 with
  | some d₁ =>
    have e : d = d₁.toDesc := Option.some.inj ((desc_of_desc1 hi).symm.trans hd).symm
    subst e
    exact desc1_srcs_le hi
  | none =>
    cases i with
    | jmp t => rcases t with rel | (r | m) <;> cases hd <;> len3
    | jcc cnd rel => cases hd; len3
    | call t => rcases t with rel | (r | m) <;> cases hd <;> len3
    | ret => cases hd; len3
    | unary op w dst => cases op <;> cases hi
    | _ => first | (cases hi; done) | (cases hd; done)

/-- The terms for the registers a description uses stand for their values. -/
theorem args_den (ρ : Env) (Γ : CtxS) (srcs : List Reg) (h : srcs.length ≤ 3) :
    [(argAt Γ.regs srcs 0).den ρ, (argAt Γ.regs srcs 1).den ρ, (argAt Γ.regs srcs 2).den ρ].take
      srcs.length = srcs.map (Γ.den ρ).val := by
  match srcs, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => exact absurd h (by simp)

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
