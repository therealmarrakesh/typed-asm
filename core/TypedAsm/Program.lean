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
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF →
      ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → WellTyped fetch sys Ψ₁ n Γ' s) →
    BlockOk Φ fetch sys Ψ a Γ' → BlockOk Φ fetch sys Ψ a Γ
  /-- A register holding exactly the address of typed code may be treated as
  a pointer to that code from here on. -/
  | codePtr {a : BitVec 64} {Γ Δ : Ctx} {r : Reg} {v : BitVec 64} :
    r ≠ .rsp → Γ.regs r = .eq v → Φ v Δ → BlockOk Φ fetch sys Ψ a (Γ.setReg r (.code Δ)) →
    BlockOk Φ fetch sys Ψ a Γ
  /-- Case analysis on the state, between instructions: continue in each of
  a family of contexts that together cover every state matching `Γ`. -/
  | cover {ι : Type} [Nonempty ι] {a : BitVec 64} {Γ : Ctx} {Γ' : ι → Ctx} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF →
      ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → ∃ x, WellTyped fetch sys Ψ₁ n (Γ' x) s) →
    (∀ x, BlockOk Φ fetch sys Ψ a (Γ' x)) → BlockOk Φ fetch sys Ψ a Γ
  /-- The memory typing may be found larger than it was, between
  instructions: continue in each of a family of contexts that together cover
  every state matching `Γ`, once some blocks are added to the memory typing. -/
  | grow {ι : Type} [Nonempty ι] {a : BitVec 64} {Γ : Ctx} {Γ' : ι → Ctx} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, WellTyped fetch sys Ψ₁ n Γ s →
      ∃ Ψ₂ : MemTy, Ψ₁.Ext Ψ₂ ∧ Ψ₂.WF ∧ ∃ x, WellTyped fetch sys Ψ₂ n (Γ' x) s) →
    (∀ x, BlockOk Φ fetch sys Ψ a (Γ' x)) → BlockOk Φ fetch sys Ψ a Γ
  /-- A register holding exactly the address of a function may be treated as
  a pointer to that function from here on. -/
  | fnPtr {a : BitVec 64} {Γ : Ctx} {r : Reg} {v : BitVec 64} {sig : FnSig} :
    r ≠ .rsp → Γ.regs r = .eq v → sig.At Φ v → BlockOk Φ fetch sys Ψ a (Γ.setReg r sig.ty) →
    BlockOk Φ fetch sys Ψ a Γ
  /-- The same for a function whose results depend on a value it chooses. -/
  | fnPtrAll {ι : Type} [Chosen ι] {a : BitVec 64} {Γ : Ctx} {r : Reg} {v : BitVec 64}
      {sig : FnSigEx ι} :
    r ≠ .rsp → Γ.regs r = .eq v → sig.At Φ v → BlockOk Φ fetch sys Ψ a (Γ.setReg r sig.ty) →
    BlockOk Φ fetch sys Ψ a Γ
  /-- An instruction shown, by an argument about states, to continue at the
  next one in one of a family of contexts, followed by the rest of the block
  in each of them. -/
  | sem {ι : Type} {a : BitVec 64} {Γ : Ctx} {Γ' : ι → Ctx} {i : Instr} {len : BitVec 64} :
    fetch a = some (i, len) → StepsTo fetch sys Ψ (a + len) Γ i Γ' →
    (∀ x, BlockOk Φ fetch sys Ψ (a + len) (Γ' x)) → BlockOk Φ fetch sys Ψ a Γ
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
  | callAll hroom hret hacc => exact .callAll hroom (fun x => h _ _ (hret x)) (hacc.mono h)
  | ret hst hsub => exact .ret hst hsub
  | syscall hret hacc => exact .syscall hret (hacc.mono h)
  | syscallExit hexit => exact .syscallExit hexit
  | jmpInd hcode hsub => exact .jmpInd hcode hsub
  | callInd hcode hroom hret hsub => exact .callInd hcode hroom (h _ _ hret) hsub
  | unreachable hun => exact .unreachable hun
  | sem hs hacc => exact .sem hs (fun x => (hacc x).mono h)
  | fnPtr hr hΓ hat _ ih => exact .fnPtr hr hΓ (fun sv rt rs rm hK => h _ _ (hat sv rt rs rm hK)) ih
  | callFn hh hroom hret hargs hsp hback hneed hgives hown =>
    exact .callFn hh hroom (h _ _ hret) hargs hsp hback hneed hgives hown
  | jmpFn hh hK hsub => exact .jmpFn hh hK hsub
  | fnPtrAll hr hΓ hat _ ih =>
    exact .fnPtrAll hr hΓ (fun sv rt rs rm fr ab hK => h _ _ (hat sv rt rs rm fr ab hK)) ih
  | callFnAll hh hroom hret hargs hsp hback hneed hgives hframe hown =>
    exact .callFnAll hh hroom (fun x => h _ _ (hret x)) hargs hsp hback hneed hgives hframe hown
  | jmpFnAll hh hK hsub => exact .jmpFnAll hh hK hsub
  | cover hsem _ ih => exact .cover hsem ih
  | grow hsem _ ih => exact .grow hsem ih
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
  | sem hf hs hrest _ => exact ⟨_, _, hf, .sem hs (fun x => ⟨_, hrest x, CtxSub.refl _⟩)⟩
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
  | @grow ι inst a Γ Γ' hsem _ ih =>
    obtain ⟨x₀⟩ := inst
    obtain ⟨i, len, hf, -⟩ := ih x₀
    refine ⟨i, len, hf, .grow hsem (fun x => ?_)⟩
    obtain ⟨i', len', hf', ht'⟩ := ih x
    cases hf.symm.trans hf'
    exact ht'
  | fnPtr hr hΓ hat _ ih =>
    obtain ⟨i, len, hf, ht⟩ := ih
    exact ⟨i, len, hf, .fnPtr hr hΓ (fun sv rt rs rm hK => h _ _ (hat sv rt rs rm hK)) ht⟩
  | fnPtrAll hr hΓ hat _ ih =>
    obtain ⟨i, len, hf, ht⟩ := ih
    exact ⟨i, len, hf,
      .fnPtrAll hr hΓ (fun sv rt rs rm fr ab hK => h _ _ (hat sv rt rs rm fr ab hK)) ht⟩
  | last hf ht => exact ⟨_, _, hf, ht.mono h⟩

/-- A register holding exactly the address of a byte of a memory block may
be treated as a pointer to that byte. This is how a computed address
becomes a typed pointer. -/
theorem BlockOk.castPtr {a : BitVec 64} {Γ : Ctx} {r : Reg} {v base : BitVec 64} {l : Layout}
    {i : Nat} {w : Bool} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq v) (hl : Ψ base = some l)
    (hv : v = base + BitVec.ofNat 64 i) (hw : w = true → l.writable = true)
    (hrest : BlockOk Φ fetch sys Ψ a (Γ.setReg r (.ptr l.shape w i))) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ he _ n s h => h.retype hr (hasTy_ptr.mpr ⟨base, l, he.blocks _ _ hl, rfl, hw, by
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
    (fun _ _ _ _ s h => ⟨s.getReg r, h.retype hr (hasTy_eq.mpr rfl)⟩) hrest

/-- The stack pointer's value may be given a name. With it, the address of
anything on the stack is a known value too. -/
theorem BlockOk.nameSp {a : BitVec 64} {Γ : Ctx}
    (hrest : ∀ v, BlockOk Φ fetch sys Ψ a (Γ.setReg .rsp (.eq v))) : BlockOk Φ fetch sys Ψ a Γ :=
  .cover (Γ' := fun v => Γ.setReg .rsp (.eq v))
    (fun _ _ _ n s h => ⟨s.getReg .rsp,
      h.setSp (fun r hr => by simp only [CtxOf.setReg, hr, ↓reduceIte]) rfl rfl rfl (by
        simp only [CtxOf.setReg, ↓reduceIte]
        exact hasTy_eq.mpr rfl)⟩) hrest

/-- Eight bytes of the stack may be given a name for the value they hold:
the rest of the block is typed for every value `v`, with those bytes typed
as exactly `v`. Whatever else was known of them is given up, so this is for
plain bytes. -/
theorem BlockOk.nameSlot {a : BitVec 64} {Γ : Ctx} {k i : Nat} {S : Shape}
    (hk : Γ.stack[k]? = some S) (hi : i + 8 ≤ S.size)
    (hrest : ∀ v, BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.set k (S.set i (.eq v)) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .cover (Γ' := fun v => { Γ with stack := Γ.stack.set k (S.set i (.eq v)) })
    (fun _ _ hΨ₁ n s h =>
      ⟨s.load64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i)),
        h.writeStack hΨ₁ hk (S' := S.set i (.eq _)) (i := i) (cnt := 0) (by omega) rfl
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hi
            · exact h.stackFits S (List.mem_of_getElem? hk) p (ShapeOf.mem_clear hp).1)
          rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp
            · exact .inr (hasTy_eq.mpr rfl)
            · have := ShapeOf.mem_clear hp
              exact .inl ⟨this.1, by omega⟩)⟩) hrest

/-! ## Blocks of a kind, and values that may be null -/

/-- A pointer to a block of a kind may be used as a pointer to a block with
that kind's shape. A pointer of type `Ty.ref` says only which kind of block
it points to; the memory typing's list of kinds says what such a block
contains, for blocks there from the start and blocks allocated later alike. -/
theorem BlockOk.openRef {a : BitVec 64} {Γ : Ctx} {r : Reg} {tag : Nat} {w : Bool} {i : Nat}
    {S : Shape} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .ref tag w i)
    (ht : Ψ.kinds tag = some S)
    (hrest : BlockOk Φ fetch sys Ψ a (Γ.setReg r (.ptr S w i))) : BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun Ψ₁ he hΨ₁ n s h => h.retype hr (by
    have hp := h.regs r hr
    rw [hΓ] at hp
    obtain ⟨b, l, hl, htag, hw, hv⟩ := hasTy_ref.mp hp
    have hk := hΨ₁.kinds b l hl tag htag
    rw [he.kinds, ht] at hk
    exact hasTy_ptr.mpr ⟨b, l, hl, (Option.some.inj hk).symm, hw, hv⟩)) hrest

/-- A register holding exactly the address of a byte of a block of a kind
may be treated as a pointer to a block of that kind. -/
theorem BlockOk.castRef {a : BitVec 64} {Γ : Ctx} {r : Reg} {v base : BitVec 64} {l : Layout}
    {tag i : Nat} {w : Bool} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq v) (hl : Ψ base = some l)
    (htag : l.tag = some tag) (hv : v = base + BitVec.ofNat 64 i)
    (hw : w = true → l.writable = true)
    (hrest : BlockOk Φ fetch sys Ψ a (Γ.setReg r (.ref tag w i))) : BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ he _ n s h => h.retype hr (hasTy_ref.mpr ⟨base, l, he.blocks _ _ hl, htag, hw, by
    have := h.regs r hr
    rw [hΓ, hasTy_eq] at this
    rw [this, hv]⟩)) hrest

/-- A value that may be null is null or it is not: the rest of the block is
typed once for each case. -/
theorem BlockOk.splitNull {a : BitVec 64} {Γ : Ctx} {r : Reg} {τ : Ty} (hr : r ≠ .rsp)
    (hΓ : Γ.regs r = .nullable τ) (hnull : BlockOk Φ fetch sys Ψ a (Γ.setReg r (.eq 0)))
    (hvalue : BlockOk Φ fetch sys Ψ a (Γ.setReg r τ)) : BlockOk Φ fetch sys Ψ a Γ :=
  .cover (ι := Bool) (Γ' := fun b => if b then Γ.setReg r (.eq 0) else Γ.setReg r τ)
    (fun _ _ _ n s h => by
      have hp := h.regs r hr
      rw [hΓ, hasTy_nullable] at hp
      rcases hp with h0 | hτ
      · exact ⟨true, h.retype hr (hasTy_eq.mpr h0)⟩
      · exact ⟨false, h.retype hr hτ⟩)
    (fun b => by cases b <;> assumption)

/-- What a system call handed back is an error number or it is not: the
rest of the block is typed once for every error number, with the register
typed as exactly that number, and once for a value. -/
theorem BlockOk.splitErr {a : BitVec 64} {Γ : Ctx} {r : Reg} {τ : Ty} (hr : r ≠ .rsp)
    (hΓ : Γ.regs r = .orErr τ)
    (herr : ∀ e, SysErr e → BlockOk Φ fetch sys Ψ a (Γ.setReg r (.eq e)))
    (hvalue : BlockOk Φ fetch sys Ψ a (Γ.setReg r τ)) : BlockOk Φ fetch sys Ψ a Γ :=
  .cover (ι := Option { e : BitVec 64 // SysErr e })
    (Γ' := fun x => match x with
      | some e => Γ.setReg r (.eq e.1)
      | none => Γ.setReg r τ)
    (fun _ _ _ n s h => by
      have hp := h.regs r hr
      rw [hΓ, hasTy_orErr] at hp
      rcases hp with he | hτ
      · exact ⟨some ⟨_, he⟩, h.retype hr (hasTy_eq.mpr rfl)⟩
      · exact ⟨none, h.retype hr hτ⟩)
    (fun x => by
      cases x with
      | some e => exact herr e.1 e.2
      | none => exact hvalue)

/-! ## Reading text -/

/-- Reading the byte of text a register points at, into another register:
the byte is zero, or it is not, and then the text goes on. -/
theorem strByte_steps {next : BitVec 64} {Γ : Ctx} {d r : Reg} {more : Bool} {w : Width}
    (hd : d ≠ .rsp) (hr : r ≠ .rsp) (hdr : d ≠ r) (hΓ : Γ.regs r = .str more) :
    StepsTo fetch sys Ψ next Γ (.movzx w d .w8 (.mem (.sib (some r) none 0)))
      (fun x : Option { b : BitVec 64 // b ≠ 0 ∧ b < 256 } =>
        match x with
        | none => Γ.setReg d (.eq 0)
        | some b => (Γ.setReg d (.eq b.1)).setReg r (.str true)) := by
  intro Ψ₁ he hΨ n s h hrip
  have hp := h.regs r hr
  rw [hΓ] at hp
  obtain ⟨a, l, off, hl, hoff, hva⟩ := hasTy_str.mp hp
  have hoff' : off < l.text := by cases more <;> simp at hoff <;> omega
  have hea : s.ea (.sib (some r) none 0) = s.getReg r := by simp [State.ea]
  have hc := h.canRead_text hr hΓ
  rw [hea] at hc
  have hex : exec sys (.movzx w d .w8 (.mem (.sib (some r) none 0))) s
      = .next (s.writeReg w d ((s.load8 (s.getReg r)).setWidth w.bits)) := by
    simp only [exec, State.readNarrow, State.read8]
    rw [hea]
    simp [hc]
  have hs' : s.writeReg w d ((s.load8 (s.getReg r)).setWidth w.bits)
      = s.setReg d (((s.load8 (s.getReg r)).setWidth w.bits).setWidth 64) := rfl
  rw [hs'] at hex
  by_cases hz : s.load8 (s.getReg r) = 0
  · have hB : ((s.load8 (s.getReg r)).setWidth w.bits).setWidth 64 = (0 : BitVec 64) := by
      rw [hz]; cases w <;> rfl
    rw [hB] at hex
    exact ⟨_, none, hex, rfl, Ψ₁, .refl _, hΨ, h.setReg hd (hasTy_eq.mpr rfl)⟩
  · have hB : ((s.load8 (s.getReg r)).setWidth w.bits).setWidth 64 ≠ (0 : BitVec 64) ∧
        ((s.load8 (s.getReg r)).setWidth w.bits).setWidth 64 < (256 : BitVec 64) := by
      generalize s.load8 (s.getReg r) = m at hz
      cases w <;> (constructor <;> (simp only [Width.bits]; bv_omega))
    -- a byte that is not zero is not the text's last
    have hmore : off + 1 < l.text := by
      apply Classical.byContradiction
      intro hcon
      have hlast : s.getReg r = a + BitVec.ofNat 64 (l.size - 1) := by
        rw [hva]
        congr 2
        simp only [Layout.size]
        omega
      have hzero := h.text a l hl (by omega)
      rw [← hlast] at hzero
      exact hz hzero
    refine ⟨_, some ⟨_, hB⟩, hex, rfl, Ψ₁, .refl _, hΨ, ?_⟩
    refine (h.setReg hd (hasTy_eq.mpr rfl)).retype hr (hasTy_str.mpr ⟨a, l, off, hl, by
      simpa using hmore, ?_⟩)
    rw [State.getReg_setReg_other _ _ _ _ (Ne.symm hdr), hva]

/-- Reading a byte of text is a step with two outcomes. The rest of the
block is typed once with the byte exactly zero, and once for every byte `b`
that is not zero, with the byte exactly `b` and the pointer known not to be
at the text's end, so that it may be stepped forward. -/
theorem BlockOk.strByte {a : BitVec 64} {Γ : Ctx} {d r : Reg} {more : Bool} {w : Width}
    {len : BitVec 64} (hf : fetch a = some (.movzx w d .w8 (.mem (.sib (some r) none 0)), len))
    (hd : d ≠ .rsp) (hr : r ≠ .rsp) (hdr : d ≠ r) (hΓ : Γ.regs r = .str more)
    (hzero : BlockOk Φ fetch sys Ψ (a + len) (Γ.setReg d (.eq 0)))
    (hmore : ∀ b : BitVec 64, b ≠ 0 → b < 256 →
      BlockOk Φ fetch sys Ψ (a + len) ((Γ.setReg d (.eq b)).setReg r (.str true))) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .sem hf (strByte_steps hd hr hdr hΓ) (fun x =>
    match x with
    | none => hzero
    | some b => hmore b.1 b.2.1 b.2.2)

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

/-- The same for a function whose results depend on a value it chooses. -/
theorem FnSigEx.at_label {ι : Type} [Chosen ι] {sig : FnSigEx ι} {l : L}
    (h : ∀ saved ret rest room frame above, sig.CallerOk saved ret rest room frame above →
      T l (sig.entry saved ret rest room frame above)) :
    sig.At (CodeTy.ofLabels prog base T) (Asm.addr prog base l) :=
  fun saved ret rest room frame above hK => .intro (h saved ret rest room frame above hK)

end Labels

/-- In a program typed block by block, the address of a function is a
function pointer, at every step count. This is what lets a function's
address sit in the program's data from the start. -/
theorem BlocksOk.hasTy_fn (hB : BlocksOk Φ fetch sys Ψ) {sig : FnSig} {v : BitVec 64}
    (hat : sig.At Φ v) (n : Nat) : HasTy fetch sys Ψ n sig.ty v := by
  rw [TypedAsm.hasTy_fn]
  intro k hk Ψ' he hΨ' saved ret rest room hK s hs hw
  exact safeUpTo hB.programOk k k (Nat.le_refl k) Ψ' he hΨ' v _
    (hB _ _ (hat saved ret rest room hK)) s hs hw

/-- The same for a function whose results depend on a value it chooses. -/
theorem BlocksOk.hasTy_fnAll (hB : BlocksOk Φ fetch sys Ψ) {ι : Type} [Chosen ι]
    {sig : FnSigEx ι} {v : BitVec 64} (hat : sig.At Φ v) (n : Nat) :
    HasTy fetch sys Ψ n sig.ty v := by
  rw [TypedAsm.hasTy_fnAll]
  intro k hk Ψ' he hΨ' saved ret rest room frame above hK s hs hw
  refine safeUpTo hB.programOk k k (Nat.le_refl k) Ψ' he hΨ' v _
    (hB _ _ (hat saved (fun x => ret (Chosen.enc x)) rest room frame above hK.ofRaw)) s hs ?_
  exact hw.sub ⟨fun _ _ => .refl _,
    .cons (.slot (.codeAllMap ret fun q => Chosen.enc (Chosen.dec (ι := ι) q))) (.refl _), rfl,
    fun _ hf => hf, .refl _, rfl, rfl⟩

/-- **Soundness, block by block.** -/
theorem soundness_blocks {s : State} (hB : BlocksOk Φ fetch sys Ψ)
    (hΨ : Ψ.WF) (hs : StateOk Φ fetch sys Ψ s) : Safe fetch sys s :=
  let ⟨Γ, hΓ, hw⟩ := hs
  soundness hB.programOk hΨ ⟨Γ, hB _ _ hΓ, hw⟩

end TypedAsm
