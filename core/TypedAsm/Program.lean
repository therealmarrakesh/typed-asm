import TypedAsm.Soundness
import TypedAsm.Asm
import TypedAsm.Fn

/-!
# Typing a program block by block

`ProgramOk` asks for a context at every instruction address. Here a context
is needed only where control can arrive from elsewhere: jump targets,
function entries, and return points. Between those, each context is the
result of the rule for the previous instruction.
-/

namespace TypedAsm

variable {Φ Φ' : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- `BlockOk Φ fetch sys Ψ a Γ`: the instructions from address `a`, entered in
context `Γ`, are well typed up to and including the first one that can
transfer control, and wherever it goes is accepted by `Φ`. -/
inductive BlockOk (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) :
    BitVec 64 → Ctx → Prop
  /-- An instruction that continues to the next one, followed by the rest of the block. -/
  | step {a : BitVec 64} {Γ Γ' : Ctx} {i : Instr} {len : BitVec 64} :
    fetch a = some (i, len) → Straight (a + len) Γ i Γ' → BlockOk Φ fetch sys Ψ (a + len) Γ' →
    BlockOk Φ fetch sys Ψ a Γ
  /-- A conditional jump in the middle of a block. The target must accept;
  the block continues with the instruction after it. Each side may assume
  which way the condition went. -/
  | branch {a : BitVec 64} {Γ : Ctx} {c : Cond} {d : BitVec 32} {len : BitVec 64} :
    fetch a = some (.jcc c d, len) → (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    (∀ f, Γ.flags f → c.eval f = some true → Accepts Φ (a + len + d.signExtend 64) Γ) →
    (∀ f, Γ.flags f → c.eval f = some false → BlockOk Φ fetch sys Ψ (a + len) Γ) →
    BlockOk Φ fetch sys Ψ a Γ
  /-- The rule of consequence, between instructions: continue in any context
  that every matching state also matches. -/
  | weaken {a : BitVec 64} {Γ Γ' : Ctx} :
    (∀ n s, WellTyped fetch sys Ψ n Γ s → WellTyped fetch sys Ψ n Γ' s) →
    BlockOk Φ fetch sys Ψ a Γ' → BlockOk Φ fetch sys Ψ a Γ
  /-- A register holding exactly the address of typed code may be treated as
  a pointer to that code from here on. -/
  | codePtr {a : BitVec 64} {Γ Δ : Ctx} {r : Reg} {v : BitVec 64} :
    r ≠ .rsp → Γ.regs r = .eq v → Φ v Δ → BlockOk Φ fetch sys Ψ a (Γ.setReg r (.code Δ)) →
    BlockOk Φ fetch sys Ψ a Γ
  /-- The last instruction of the block. -/
  | last {a : BitVec 64} {Γ : Ctx} {i : Instr} {len : BitVec 64} :
    fetch a = some (i, len) → HasType Φ fetch sys Ψ (a + len) Γ i → BlockOk Φ fetch sys Ψ a Γ

/-- A program is well typed block by block if every context the code typing
allows at an address starts a well-typed block. -/
def BlocksOk (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) : Prop :=
  ∀ a Γ, Φ a Γ → BlockOk Φ fetch sys Ψ a Γ

theorem Accepts.mono (h : ∀ a Γ, Φ a Γ → Φ' a Γ) {a : BitVec 64} {Γ : Ctx}
    (hacc : Accepts Φ a Γ) : Accepts Φ' a Γ :=
  let ⟨Δ, hΔ, hsub⟩ := hacc
  ⟨Δ, h _ _ hΔ, hsub⟩

/-- Allowing more contexts keeps every instruction well typed. -/
theorem HasType.mono (h : ∀ a Γ, Φ a Γ → Φ' a Γ) {next : BitVec 64} {Γ : Ctx} {i : Instr}
    (ht : HasType Φ fetch sys Ψ next Γ i) : HasType Φ' fetch sys Ψ next Γ i := by
  induction ht with
  | straight hst hacc => exact .straight hst (hacc.mono h)
  | jmp hacc => exact .jmp (hacc.mono h)
  | jcc hdec hacc hfall =>
    exact .jcc hdec (fun f hf hb => (hacc f hf hb).mono h) (fun f hf hb => (hfall f hf hb).mono h)
  | jmpReg hr hΓ hsub => exact .jmpReg hr hΓ hsub
  | call hroom hret hacc => exact .call hroom (h _ _ hret) (hacc.mono h)
  | ret hst hsub => exact .ret hst hsub
  | syscall hacc => exact .syscall (hacc.mono h)
  | jmpInd hcode hsub => exact .jmpInd hcode hsub
  | callInd hcode hroom hret hsub => exact .callInd hcode hroom (h _ _ hret) hsub
  | unreachable hun => exact .unreachable hun
  | codePtr hr hΓ hΦ _ ih => exact .codePtr hr hΓ (h _ _ hΦ) ih
  | weaken hsem _ ih => exact .weaken hsem ih

/-- A program typed block by block is well typed instruction by instruction,
taking the context at each address to be the one its block reaches there. -/
theorem BlocksOk.programOk (h : BlocksOk Φ fetch sys Ψ) :
    ProgramOk (BlockOk Φ fetch sys Ψ) fetch sys Ψ := by
  intro a Γ hb
  induction hb with
  | step hf hst hrest _ => exact ⟨_, _, hf, .straight hst ⟨_, hrest, CtxSub.refl _⟩⟩
  | branch hf hdec hacc hrest _ =>
    exact ⟨_, _, hf, .jcc hdec (fun f hΓ hb => (hacc f hΓ hb).mono h)
      (fun f hΓ hb => ⟨_, hrest f hΓ hb, CtxSub.refl _⟩)⟩
  | weaken hsem _ ih =>
    obtain ⟨i, len, hf, ht⟩ := ih
    exact ⟨i, len, hf, .weaken hsem ht⟩
  | codePtr hr hΓ hΦ _ ih =>
    obtain ⟨i, len, hf, ht⟩ := ih
    exact ⟨i, len, hf, .codePtr hr hΓ (h _ _ hΦ) ht⟩
  | last hf ht => exact ⟨_, _, hf, ht.mono h⟩

/-- A register holding exactly the address of a field of a memory block may
be treated as a pointer to that field. This is how a computed address
becomes a typed pointer. -/
theorem BlockOk.castPtr {a : BitVec 64} {Γ : Ctx} {r : Reg} {v base : BitVec 64} {l : Layout}
    {i : Nat} {w : Bool} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq v) (hl : Ψ base = some l)
    (hv : v = base + BitVec.ofNat 64 (8 * i)) (hw : w = true → l.writable = true)
    (hrest : BlockOk Φ fetch sys Ψ a (Γ.setReg r (.ptr l.fields w i))) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun n s h => h.retype hr (hasTy_ptr.mpr ⟨base, l, hl, rfl, hw, by
    have := h.regs r hr
    rw [hΓ, hasTy_eq] at this
    rw [this, hv]⟩)) hrest

/-! ## Contexts attached to labels -/

section Labels

variable {L : Type} [DecidableEq L] {prog : List (Asm L)} {base : BitVec 64}
  {T : L → Ctx → Prop}

/-- The code typing of a labelled program, given the contexts allowed at each
label: an address may be entered in a context if it is the address of a
label that allows that context. -/
def CodeTy.ofLabels (prog : List (Asm L)) (base : BitVec 64) (T : L → Ctx → Prop) : CodeTy :=
  fun a Γ => ∃ l, Asm.addr prog base l = a ∧ T l Γ

/-- A context allowed at a label is allowed at the label's address. -/
theorem CodeTy.ofLabels.intro {l : L} {Γ : Ctx} (h : T l Γ) :
    CodeTy.ofLabels prog base T (Asm.addr prog base l) Γ :=
  ⟨l, rfl, h⟩

/-- To type a labelled program block by block, type the block at each label. -/
theorem BlocksOk.of_labels
    (h : ∀ l Γ, T l Γ →
      BlockOk (CodeTy.ofLabels prog base T) fetch sys Ψ (Asm.addr prog base l) Γ) :
    BlocksOk (CodeTy.ofLabels prog base T) fetch sys Ψ := by
  rintro a Γ ⟨l, rfl, hl⟩
  exact h l Γ hl

/-- A label that allows a signature's entry context for every caller is a
function with that signature. -/
theorem FnSig.at_label {sig : FnSig} {l : L}
    (h : ∀ saved ret rest room, sig.CallerOk saved ret rest room →
      T l (sig.entry saved ret rest room)) :
    sig.At (CodeTy.ofLabels prog base T) (Asm.addr prog base l) :=
  fun saved ret rest room hK => .intro (h saved ret rest room hK)

end Labels

/-- **Soundness, block by block.** -/
theorem soundness_blocks {s : State} (hB : BlocksOk Φ fetch sys Ψ)
    (hΨ : Ψ.WF) (hsys : SysOk fetch sys Ψ) (hs : StateOk Φ fetch sys Ψ s) : Safe fetch sys s :=
  let ⟨Γ, hΓ, hw⟩ := hs
  soundness hB.programOk hΨ hsys ⟨Γ, hB _ _ hΓ, hw⟩

end TypedAsm
