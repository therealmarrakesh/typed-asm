import TypedAsm.Soundness

/-!
# Typing a program block by block

`ProgramOk` asks for a context at every instruction address. Here a context
is needed only where control can arrive from elsewhere: jump targets,
function entries, and return points. Between those, each context is the
result of the rule for the previous instruction.
-/

namespace TypedAsm

variable {Φ Φ' : CodeTy} {fetch : Fetch}

/-- `BlockOk Φ fetch a Γ`: the instructions from address `a`, entered in
context `Γ`, are well typed up to and including the first one that can
transfer control, and wherever it goes is accepted by `Φ`. -/
inductive BlockOk (Φ : CodeTy) (fetch : Fetch) : BitVec 64 → Ctx → Prop
  /-- An instruction that continues to the next one, followed by the rest of the block. -/
  | step {a : BitVec 64} {Γ Γ' : Ctx} {i : Instr} {len : BitVec 64} :
    fetch a = some (i, len) → Straight Γ i Γ' → BlockOk Φ fetch (a + len) Γ' →
    BlockOk Φ fetch a Γ
  /-- The last instruction of the block. -/
  | last {a : BitVec 64} {Γ : Ctx} {i : Instr} {len : BitVec 64} :
    fetch a = some (i, len) → HasType Φ (a + len) Γ i → BlockOk Φ fetch a Γ

/-- A program is well typed block by block if every context the code typing
allows at an address starts a well-typed block. -/
def BlocksOk (Φ : CodeTy) (fetch : Fetch) : Prop :=
  ∀ a Γ, Φ a Γ → BlockOk Φ fetch a Γ

theorem Accepts.mono (h : ∀ a Γ, Φ a Γ → Φ' a Γ) {a : BitVec 64} {Γ : Ctx}
    (hacc : Accepts Φ a Γ) : Accepts Φ' a Γ :=
  let ⟨Δ, hΔ, hsub⟩ := hacc
  ⟨Δ, h _ _ hΔ, hsub⟩

/-- Allowing more contexts keeps every instruction well typed. -/
theorem HasType.mono (h : ∀ a Γ, Φ a Γ → Φ' a Γ) {next : BitVec 64} {Γ : Ctx} {i : Instr}
    (ht : HasType Φ next Γ i) : HasType Φ' next Γ i := by
  cases ht with
  | straight hst hacc => exact .straight hst (hacc.mono h)
  | jmp hacc => exact .jmp (hacc.mono h)
  | jcc hdec hacc hfall =>
    exact .jcc hdec (fun f hf hb => (hacc f hf hb).mono h) (fun f hf hb => (hfall f hf hb).mono h)
  | jmpReg hr hΓ hsub => exact .jmpReg hr hΓ hsub
  | call hroom hret hacc => exact .call hroom (h _ _ hret) (hacc.mono h)
  | ret hst hsub => exact .ret hst hsub
  | syscall hacc => exact .syscall (hacc.mono h)

/-- A program typed block by block is well typed instruction by instruction,
taking the context at each address to be the one its block reaches there. -/
theorem BlocksOk.programOk (h : BlocksOk Φ fetch) : ProgramOk (BlockOk Φ fetch) fetch := by
  intro a Γ hb
  cases hb with
  | step hf hst hrest => exact ⟨_, _, hf, .straight hst ⟨_, hrest, CtxSub.refl _⟩⟩
  | last hf ht => exact ⟨_, _, hf, ht.mono h⟩

/-- **Soundness, block by block.** -/
theorem soundness_blocks {sys : Syscall} {Ψ : MemTy} {s : State} (hB : BlocksOk Φ fetch)
    (hΨ : Ψ.WF) (hsys : SysOk fetch sys Ψ) (hs : StateOk Φ fetch sys Ψ s) : Safe fetch sys s :=
  let ⟨Γ, hΓ, hw⟩ := hs
  soundness hB.programOk hΨ hsys ⟨Γ, hB _ _ hΓ, hw⟩

end TypedAsm
