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
    fetch a = some (i, len) → Straight Ψ (a + len) Γ i Γ' → BlockOk Φ fetch sys Ψ (a + len) Γ' →
    BlockOk Φ fetch sys Ψ a Γ
  /-- A system call that returns, followed by the rest of the block. -/
  | sys {a : BitVec 64} {Γ Γ' : Ctx} {len : BitVec 64} :
    fetch a = some (.syscall, len) → SysReturns fetch sys Ψ Γ Γ' →
    BlockOk Φ fetch sys Ψ (a + len) Γ' → BlockOk Φ fetch sys Ψ a Γ
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
  /-- Case analysis on the state, between instructions: continue in each of
  a family of contexts that together cover every state matching `Γ`. -/
  | cover {ι : Type} [Nonempty ι] {a : BitVec 64} {Γ : Ctx} {Γ' : ι → Ctx} :
    (∀ n s, WellTyped fetch sys Ψ n Γ s → ∃ x, WellTyped fetch sys Ψ n (Γ' x) s) →
    (∀ x, BlockOk Φ fetch sys Ψ a (Γ' x)) → BlockOk Φ fetch sys Ψ a Γ
  /-- A register holding exactly the address of a function may be treated as
  a pointer to that function from here on. -/
  | fnPtr {a : BitVec 64} {Γ : Ctx} {r : Reg} {v : BitVec 64} {sig : FnSig} :
    r ≠ .rsp → Γ.regs r = .eq v → sig.At Φ v → BlockOk Φ fetch sys Ψ a (Γ.setReg r sig.ty) →
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
  | call hroom hret hacc => exact .call hroom (h _ _ hret) (hacc.mono h)
  | ret hst hsub => exact .ret hst hsub
  | syscall hret hacc => exact .syscall hret (hacc.mono h)
  | syscallExit hexit => exact .syscallExit hexit
  | jmpInd hcode hsub => exact .jmpInd hcode hsub
  | callInd hcode hroom hret hsub => exact .callInd hcode hroom (h _ _ hret) hsub
  | unreachable hun => exact .unreachable hun
  | fnPtr hr hΓ hat _ ih => exact .fnPtr hr hΓ (fun sv rt rs rm hK => h _ _ (hat sv rt rs rm hK)) ih
  | callFn hh hroom hret hargs hback hneed => exact .callFn hh hroom (h _ _ hret) hargs hback hneed
  | jmpFn hh hK hsub => exact .jmpFn hh hK hsub
  | cover hsem _ ih => exact .cover hsem ih
  | codePtr hr hΓ hΦ _ ih => exact .codePtr hr hΓ (h _ _ hΦ) ih
  | weaken hsem _ ih => exact .weaken hsem ih

/-- A program typed block by block is well typed instruction by instruction,
taking the context at each address to be the one its block reaches there. -/
theorem BlocksOk.programOk (h : BlocksOk Φ fetch sys Ψ) :
    ProgramOk (BlockOk Φ fetch sys Ψ) fetch sys Ψ := by
  intro a Γ hb
  induction hb with
  | step hf hst hrest _ => exact ⟨_, _, hf, .straight hst ⟨_, hrest, CtxSub.refl _⟩⟩
  | sys hf hret hrest _ => exact ⟨_, _, hf, .syscall hret ⟨_, hrest, CtxSub.refl _⟩⟩
  | branch hf hdec hacc hrest _ =>
    exact ⟨_, _, hf, .jcc hdec (fun f hΓ hb => (hacc f hΓ hb).mono h)
      (fun f hΓ hb => ⟨_, hrest f hΓ hb, CtxSub.refl _⟩)⟩
  | weaken hsem _ ih =>
    obtain ⟨i, len, hf, ht⟩ := ih
    exact ⟨i, len, hf, .weaken hsem ht⟩
  | codePtr hr hΓ hΦ _ ih =>
    obtain ⟨i, len, hf, ht⟩ := ih
    exact ⟨i, len, hf, .codePtr hr hΓ (h _ _ hΦ) ht⟩
  | @cover ι inst a Γ Γ' hsem _ ih =>
    obtain ⟨x₀⟩ := inst
    obtain ⟨i, len, hf, -⟩ := ih x₀
    refine ⟨i, len, hf, .cover hsem (fun x => ?_)⟩
    obtain ⟨i', len', hf', ht'⟩ := ih x
    cases hf.symm.trans hf'
    exact ht'
  | fnPtr hr hΓ hat _ ih =>
    obtain ⟨i, len, hf, ht⟩ := ih
    exact ⟨i, len, hf, .fnPtr hr hΓ (fun sv rt rs rm hK => h _ _ (hat sv rt rs rm hK)) ht⟩
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

/-- A register may be given a name for the value it holds: the rest of the
block is typed for every value `v`, with the register typed as exactly `v`.
Whatever else was known about the register is given up, so this is for
registers typed as integers. -/
theorem BlockOk.name {a : BitVec 64} {Γ : Ctx} {r : Reg} (hr : r ≠ .rsp)
    (hrest : ∀ v, BlockOk Φ fetch sys Ψ a (Γ.setReg r (.eq v))) : BlockOk Φ fetch sys Ψ a Γ :=
  .cover (Γ' := fun v => Γ.setReg r (.eq v))
    (fun _ s h => ⟨s.getReg r, h.retype hr (hasTy_eq.mpr rfl)⟩) hrest

/-- A stack slot may be given a name for the value it holds: the rest of
the block is typed for every value `v`, with the slot typed as exactly `v`.
Whatever else was known about the slot is given up, so this is for slots
typed as integers. -/
theorem BlockOk.nameSlot {a : BitVec 64} {Γ : Ctx} {i : Nat} (hi : i < Γ.stack.length)
    (hrest : ∀ v, BlockOk Φ fetch sys Ψ a { Γ with stack := Γ.stack.set i (.eq v) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .cover (Γ' := fun v => { Γ with stack := Γ.stack.set i (.eq v) })
    (fun n s h => ⟨s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)),
      { regs := h.regs
        flags := h.flags
        stackPerm := by
          have := h.stackPerm
          simpa only [stackBase, stackSize, List.length_set] using this
        stackSize_lt := by
          have := h.stackSize_lt
          simpa only [stackSize, List.length_set] using this
        stack := fun j τ hj => by
          by_cases hji : j = i
          · subst hji
            rw [List.getElem?_set_self hi] at hj
            cases hj
            exact hasTy_eq.mpr rfl
          · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
            exact h.stack j τ hj
        heapPerm := h.heapPerm
        heap := h.heap
        stackHeap := fun b l hl => by
          have := h.stackHeap b l hl
          simpa only [stackBase, stackSize, List.length_set] using this }⟩) hrest

/-! ## Blocks of a kind, and values that may be null -/

/-- Every block of kind `tag` has these fields. A pointer of type `Ty.ref`
says only which kind of block it points to; this is the fact that says what
such a block contains. It is a property of the memory typing, proved once
for a program. -/
def MemTy.TagFields (Ψ : MemTy) (tag : Nat) (fields : List Ty) : Prop :=
  ∀ a l, Ψ a = some l → l.tag = some tag → l.fields = fields

/-- A pointer to a block of a kind may be used as a pointer to a block with
that kind's fields. -/
theorem BlockOk.openRef {a : BitVec 64} {Γ : Ctx} {r : Reg} {tag : Nat} {w : Bool} {i : Nat}
    {fields : List Ty} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .ref tag w i)
    (ht : Ψ.TagFields tag fields)
    (hrest : BlockOk Φ fetch sys Ψ a (Γ.setReg r (.ptr fields w i))) : BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun n s h => h.retype hr (by
    have hp := h.regs r hr
    rw [hΓ] at hp
    obtain ⟨b, l, hl, htag, hw, hv⟩ := hasTy_ref.mp hp
    exact hasTy_ptr.mpr ⟨b, l, hl, ht b l hl htag, hw, hv⟩)) hrest

/-- A register holding exactly the address of a field of a block of a kind
may be treated as a pointer to a block of that kind. -/
theorem BlockOk.castRef {a : BitVec 64} {Γ : Ctx} {r : Reg} {v base : BitVec 64} {l : Layout}
    {tag i : Nat} {w : Bool} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq v) (hl : Ψ base = some l)
    (htag : l.tag = some tag) (hv : v = base + BitVec.ofNat 64 (8 * i))
    (hw : w = true → l.writable = true)
    (hrest : BlockOk Φ fetch sys Ψ a (Γ.setReg r (.ref tag w i))) : BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun n s h => h.retype hr (hasTy_ref.mpr ⟨base, l, hl, htag, hw, by
    have := h.regs r hr
    rw [hΓ, hasTy_eq] at this
    rw [this, hv]⟩)) hrest

/-- A value that may be null is null or it is not: the rest of the block is
typed once for each case. -/
theorem BlockOk.splitNull {a : BitVec 64} {Γ : Ctx} {r : Reg} {τ : Ty} (hr : r ≠ .rsp)
    (hΓ : Γ.regs r = .nullable τ) (hnull : BlockOk Φ fetch sys Ψ a (Γ.setReg r (.eq 0)))
    (hvalue : BlockOk Φ fetch sys Ψ a (Γ.setReg r τ)) : BlockOk Φ fetch sys Ψ a Γ :=
  .cover (ι := Bool) (Γ' := fun b => if b then Γ.setReg r (.eq 0) else Γ.setReg r τ)
    (fun n s h => by
      have hp := h.regs r hr
      rw [hΓ, hasTy_nullable] at hp
      rcases hp with h0 | hτ
      · exact ⟨true, h.retype hr (hasTy_eq.mpr h0)⟩
      · exact ⟨false, h.retype hr hτ⟩)
    (fun b => by cases b <;> assumption)

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

/-- In a program typed block by block, the address of a function is a
function pointer, at every step count. This is what lets a function's
address sit in the program's data from the start. -/
theorem BlocksOk.hasTy_fn (hB : BlocksOk Φ fetch sys Ψ) (hΨ : Ψ.WF) {sig : FnSig} {v : BitVec 64}
    (hat : sig.At Φ v) (n : Nat) : HasTy fetch sys Ψ n sig.ty v := by
  rw [TypedAsm.hasTy_fn]
  intro k hk saved ret rest room hK s hs hw
  exact safeUpTo hB.programOk hΨ k k (Nat.le_refl k) v _ (hB _ _ (hat saved ret rest room hK)) s hs hw

/-- **Soundness, block by block.** -/
theorem soundness_blocks {s : State} (hB : BlocksOk Φ fetch sys Ψ)
    (hΨ : Ψ.WF) (hs : StateOk Φ fetch sys Ψ s) : Safe fetch sys s :=
  let ⟨Γ, hΓ, hw⟩ := hs
  soundness hB.programOk hΨ ⟨Γ, hB _ _ hΓ, hw⟩

end TypedAsm
