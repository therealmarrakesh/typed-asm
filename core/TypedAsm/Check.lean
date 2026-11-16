import TypedAsm.Program

/-!
# Checking by computation

The typing rules say when an instruction may run in a context and what
context it leaves. Here that is a function: given the context and the
instruction it works out the context afterwards, and says what, if
anything, is left to be shown. `straight_sound` says its answers are typing
steps. So typing a run of instructions is evaluating a function, with no
search among rules.

The function is defined on contexts as they are, not on a separate syntax
for them. Where it needs to know what a register holds it looks, and where
the context does not say, as for a register a function was handed by
whoever called it, it has no answer and the rules are used directly.

It covers the forms that work on registers alone. For an instruction with
several rules it takes the one that keeps most, in the order the rules are
tried by hand: an exactly known result where the operands are exactly
known, and otherwise a number.
-/

namespace TypedAsm

namespace Check

/-- What one instruction comes to: the context afterwards, and what is left
to be shown for the step to be a typing step. -/
structure Step where
  ctx : Ctx
  needs : Prop := True

/-- The value a type says a register holds exactly, if it says so. -/
def exactly : Ty → Option (BitVec 64)
  | .eq a => some a
  | _ => none

theorem exactly_eq {τ : Ty} {a : BitVec 64} (h : exactly τ = some a) : τ = .eq a := by
  cases τ <;> simp only [exactly, Option.some.injEq, reduceCtorEq] at h
  rw [h]

/-- What reading the carry flag asks: that it is defined. -/
def carryNeeds (Γ : Ctx) (op : AluOp) : Prop :=
  op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true

/-- A 32-bit copy between registers. -/
def mov32 (Γ : Ctx) (d s : Reg) : Option Step :=
  if d = .rsp then none
  else match exactly (Γ.regs s) with
    | some a =>
      if s = .rsp then some ⟨Γ.setReg d .int, True⟩
      else some ⟨Γ.setReg d (.eq ((a.setWidth 32).setWidth 64)), True⟩
    | none => some ⟨Γ.setReg d .int, True⟩

/-- Arithmetic between two registers. -/
def aluRR (Γ : Ctx) (op : AluOp) (w : Width) (d s : Reg) : Option Step :=
  if d = .rsp then none
  else match exactly (Γ.regs d), exactly (Γ.regs s) with
    | some a, some b =>
      if s = .rsp ∨ op.readsCarry = true then some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩
      else match w with
        | .w64 =>
          some ⟨{ (bif op.writesDst then Γ.setReg d (.eq (op.apply a b).1) else Γ) with
            flags := (· = (op.apply a b).2) }, True⟩
        | .w32 =>
          some ⟨{ (bif op.writesDst then
              Γ.setReg d (.eq ((op.apply (a.setWidth 32) (b.setWidth 32)).1.setWidth 64))
            else Γ) with
            flags := (· = (op.apply (a.setWidth 32) (b.setWidth 32)).2) }, True⟩
    | _, _ => some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩

/-- Arithmetic between a register and a constant. A register that holds a
pointer is left to the rules: what becomes of it depends on the block. -/
def aluRI (Γ : Ctx) (op : AluOp) (w : Width) (d : Reg) (imm : BitVec 32) : Option Step :=
  if d = .rsp then none
  else match Γ.regs d with
    | .eq a =>
      if op.readsCarry = true then some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩
      else match w with
        | .w64 =>
          some ⟨{ (bif op.writesDst then Γ.setReg d (.eq (op.apply a (imm.signExtend 64)).1)
            else Γ) with flags := (· = (op.apply a (imm.signExtend 64)).2) }, True⟩
        | .w32 =>
          some ⟨{ (bif op.writesDst then
              Γ.setReg d (.eq ((op.apply (a.setWidth 32) (imm.signExtend 32)).1.setWidth 64))
            else Γ) with
            flags := (· = (op.apply (a.setWidth 32) (imm.signExtend 32)).2) }, True⟩
    | .int => some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩
    | _ => none

/-- A `test` of one register against another. -/
def testRR (Γ : Ctx) (r r' : Reg) : Option Step :=
  match exactly (Γ.regs r), exactly (Γ.regs r') with
  | some a, some b =>
    if r = .rsp ∨ r' = .rsp then some ⟨{ Γ with flags := Flags.Known }, True⟩
    else some ⟨{ Γ with flags := (· = Flags.ofResult (a &&& b) false false) }, True⟩
  | _, _ => some ⟨{ Γ with flags := Flags.Known }, True⟩

/-- **The checker for one instruction that goes on to the next.** `next` is
the address of the instruction after it. -/
def straight (next : BitVec 64) (Γ : Ctx) : Instr → Option Step
  | .nop => some ⟨Γ, True⟩
  | .mov .w64 (.rm_r (.reg d) s) =>
    if d = .rsp ∨ s = .rsp then none else some ⟨Γ.setReg d (Γ.regs s), True⟩
  | .mov .w32 (.rm_r (.reg d) s) => mov32 Γ d s
  | .mov w (.rm_i (.reg d) imm) =>
    if d = .rsp then none
    else some ⟨Γ.setReg d (.eq ((imm.signExtend w.bits).setWidth 64)), True⟩
  | .movAbs d imm => if d = .rsp then none else some ⟨Γ.setReg d (.eq imm), True⟩
  | .lea .w64 d (.rip disp) =>
    if d = .rsp then none else some ⟨Γ.setReg d (.eq (next + disp.signExtend 64)), True⟩
  | .alu .xor w (.rm_r (.reg d) s) =>
    if d = s then
      if d = .rsp then none
      else some ⟨{ Γ.setReg d (.eq 0) with
        flags := (· = Flags.ofResult (0 : BitVec w.bits) false false) }, True⟩
    else aluRR Γ .xor w d s
  | .alu op w (.rm_r (.reg d) s) => aluRR Γ op w d s
  | .alu op w (.rm_i (.reg d) imm) => aluRI Γ op w d imm
  | .test .w64 (.reg r) (.reg r') => testRR Γ r r'
  | .test _ (.reg _) _ => some ⟨{ Γ with flags := Flags.Known }, True⟩
  | _ => none

variable {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx}

theorem mov32_sound {d s : Reg} {st : Step} (h : mov32 Γ d s = some st) :
    Straight Ψ next Γ (.mov .w32 (.rm_r (.reg d) s)) st.ctx := by
  unfold mov32 at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next a ha =>
      split at h
      · cases h; exact .movRR32 hd
      · next hs => cases h; exact .mov32Exact hd hs (exactly_eq ha)
    · cases h; exact .movRR32 hd

theorem aluRR_sound {op : AluOp} {w : Width} {d s : Reg} {st : Step}
    (h : aluRR Γ op w d s = some st) (hn : st.needs) :
    Straight Ψ next Γ (.alu op w (.rm_r (.reg d) s)) st.ctx := by
  unfold aluRR at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next a b ha hb =>
      split at h
      · cases h; exact .aluRR hd hn
      · next hc =>
        have hs : s ≠ .rsp := fun e => hc (.inl e)
        have hcarry : op.readsCarry = false := by
          cases hr : op.readsCarry with
          | false => rfl
          | true => exact absurd (.inr hr) hc
        split at h
        · cases h; exact .aluExactRR hd hs (exactly_eq ha) (exactly_eq hb) hcarry
        · cases h; exact .aluExactRR32 hd hs (exactly_eq ha) (exactly_eq hb) hcarry
    · cases h; exact .aluRR hd hn

theorem aluRI_sound {op : AluOp} {w : Width} {d : Reg} {imm : BitVec 32} {st : Step}
    (h : aluRI Γ op w d imm = some st) (hn : st.needs) :
    Straight Ψ next Γ (.alu op w (.rm_i (.reg d) imm)) st.ctx := by
  unfold aluRI at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next a ha =>
      split at h
      · cases h; exact .aluRI hd hn
      · next hc =>
        have hcarry : op.readsCarry = false := (Bool.not_eq_true _).mp hc
        split at h
        · cases h; exact .aluExact hd ha hcarry
        · cases h; exact .aluExact32 hd ha hcarry
    · cases h; exact .aluRI hd hn
    · cases h

theorem testRR_sound {r r' : Reg} {st : Step} (h : testRR Γ r r' = some st) :
    Straight Ψ next Γ (.test .w64 (.reg r) (.reg r')) st.ctx := by
  unfold testRR at h
  split at h
  · next a b ha hb =>
    split at h
    · cases h; exact .testRM (.reg _)
    · next hc =>
      cases h
      exact .testExact (fun e => hc (.inl e)) (fun e => hc (.inr e)) (exactly_eq ha) (exactly_eq hb)
  · cases h; exact .testRM (.reg _)

/-- **What the checker works out is a typing step.** -/
theorem straight_sound {i : Instr} {st : Step} (h : straight next Γ i = some st)
    (hn : st.needs) : Straight Ψ next Γ i st.ctx := by
  unfold straight at h
  split at h
  · cases h; exact .nop
  · split at h
    · cases h
    · next hc => cases h; exact .movRR64 (fun e => hc (.inl e)) (fun e => hc (.inr e))
  · exact mov32_sound h
  · split at h
    · cases h
    · next hd => cases h; exact .movRI hd
  · split at h
    · cases h
    · next hd => cases h; exact .movAbs hd
  · split at h
    · cases h
    · next hd => cases h; exact .leaRip hd
  · split at h
    · next hds =>
      subst hds
      split at h
      · cases h
      · next hd => cases h; exact .xorSelf hd
    · exact aluRR_sound h hn
  · exact aluRR_sound h hn
  · exact aluRI_sound h hn
  · exact testRR_sound h
  · cases h; exact .testRM (.reg _)
  · cases h

end Check

/-- A block that begins with an instruction the checker has worked out. -/
theorem BlockOk.checked {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {a : BitVec 64} {Γ : Ctx} {i : Instr} {len : BitVec 64} {st : Check.Step}
    (hf : fetch a = some (i, len)) (hc : Check.straight (a + len) Γ i = some st)
    (hn : st.needs) (hrest : BlockOk Φ fetch sys Ψ (a + len) st.ctx) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .step hf (Check.straight_sound hc hn) hrest

end TypedAsm
