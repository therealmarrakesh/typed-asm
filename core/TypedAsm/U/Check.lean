import TypedAsm.U.Term
import TypedAsm.U.Regs
import TypedAsm.U.Mem

/-!
# The checker: contexts as terms, and one step for any instruction

A context is written as data: the term each register holds, the term for
the flags, and the regions held alone with the terms for the values in
them. The checker's step for an instruction reads the instruction's
description: it takes the terms of the registers the description uses, and
gives each register the description writes the term for what the
instruction makes of them. There is no case for any particular instruction.

What the step concludes, it concludes of the machine: it is proved to be
what the one statement that types every instruction gives.
-/

namespace TypedAsm.U

open TypedAsm

/-- A region held alone, as terms: its size, and the values in it. -/
structure HeldS where
  size : Nat
  slots : List (Nat × Val)

/-- A context, as terms. -/
structure CtxS where
  regs : Regs Val
  flags : FlagsT
  held : List (Val × HeldS) := []

def HeldS.den (ρ : Env) (S : HeldS) : Held := ⟨S.size, S.slots.map fun p => (p.1, p.2.den ρ)⟩

/-- The context a context written as terms stands for. -/
def CtxS.den (ρ : Env) (Γ : CtxS) : Ctx where
  val r := (Γ.regs.get r).den ρ
  flags := Γ.flags.den ρ
  held := Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)

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
  obtain ⟨s', hex, Ψ'', he', hwf', Γ', hq, hw'⟩ := h n Ψ' he hwf s hrip hw
  exact ⟨s', hex, Ψ'', he', hwf', Γ', hQ _ _ hq, hw'⟩

/-- **The checker's step for an instruction that touches no memory**: the
context after, and where control goes. Each register the instruction writes
holds the term for what the instruction gives it. -/
def stepPure (Γ : CtxS) (next : BitVec 64) (i : Instr) : Option (CtxS × Val) :=
  match i.desc with
  | some d =>
    if d.rd.isNone && d.wr.isNone then
      let a := argAt Γ.regs d.srcs 0
      let b := argAt Γ.regs d.srcs 1
      let c := argAt Γ.regs d.srcs 2
      let ea : Val := match d.ea with
        | some m => eaS Γ.regs next m
        | none => .lit 0
      some ({ Γ with
          regs := setOuts (fun k => .out i k a b c Γ.flags next ea (.lit 0)) i.outs 0 Γ.regs
          flags := .out i a b c Γ.flags next ea (.lit 0) },
        .goes i a b c Γ.flags next ea (.lit 0))
    else none
  | none => none

/-- That an instruction does not fault for a reason of its own, in a
context, reading nothing. -/
def Guarded (ρ : Env) (Γ : CtxS) (next : BitVec 64) (i : Instr) : Prop :=
  match i.desc with
  | some d =>
    d.guard (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
      ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) 0 = true
  | none => False

theorem stepPure_sound {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {ρ : Env} {Γ Γ' : CtxS}
    {next : BitVec 64} {i : Instr} {t : Val} (h : stepPure Γ next i = some (Γ', t))
    (hg : Guarded ρ Γ next i) :
    Steps fetch sys Ψ i next (Γ.den ρ) fun t' Δ => t' = t.den ρ ∧ Δ = Γ'.den ρ := by
  unfold stepPure at h
  unfold Guarded at hg
  cases hd : i.desc with
  | none => rw [hd] at h; cases h
  | some d =>
    rw [hd] at h hg
    simp only at h hg
    split at h
    · next hno =>
      cases h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hno
      have hea : (match d.ea with
          | some m => eaS Γ.regs next m
          | none => Val.lit 0).den ρ = (d.ea.map (eaOf (Γ.den ρ).val next)).getD 0 := by
        cases d.ea with
        | none => rfl
        | some m => exact eaS_den ρ Γ next m
      have hvals := args_den ρ Γ d.srcs (desc_srcs_le hd)
      refine Steps.mono (Steps.desc (R := fun x Γr => x = 0 ∧ Γr = Γ.den ρ)
        (W := fun _ Γr Γw => Γw = Γr) hd ?_ ?_ ?_) ?_
      · rw [hno.1]; exact ⟨rfl, rfl⟩
      · intro x Γr _
        refine ⟨Γr, rfl, ?_⟩
        rw [hno.2]
      · rintro x Γr ⟨rfl, -⟩
        exact hg
      · rintro t' Δ ⟨x, Γr, Γw, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
        refine ⟨?_, ?_⟩
        · show _ = targetOf i _ _ _ _ _
          unfold targetOf
          rw [hd]
          simp only [Val.den]
          rw [hvals, hea]
          rfl
        · have he : effectOf i [(argAt Γ.regs d.srcs 0).den ρ, (argAt Γ.regs d.srcs 1).den ρ,
              (argAt Γ.regs d.srcs 2).den ρ] (Γ.flags.den ρ) next
              ((match d.ea with
                | some m => eaS Γ.regs next m
                | none => Val.lit 0).den ρ) 0
              = d.run (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
                ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) 0 := by
            unfold effectOf
            rw [hd]
            simp only
            rw [hvals, hea]
            rfl
          have houts := desc_outs hd (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
            ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) 0
          refine ctx_ext ?_ ?_ rfl rfl
          · funext r
            show List.foldl _ (Γ.den ρ).val _ r = ((setOuts _ i.outs 0 Γ.regs).get r).den ρ
            rw [← houts]
            refine (setOuts_den ρ _ _ 0 Γ.regs _ (fun _ => rfl) (fun j hj => ?_) r).symm
            show ((effectOf i _ _ next _ 0).regs.getD (0 + j) (Reg.rax, 0)).2 = _
            rw [he, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
            rfl
          · show _ = (effectOf i _ _ next _ 0).flags
            rw [he]
            rfl
    · cases h

end TypedAsm.U
