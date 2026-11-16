import TypedAsm.Program

/-!
# Register types, one after another

A context gives each register a type by a function, and every rule that
changes a register's type wraps that function in a test: this register gets
the new type, the others what they had. After many instructions the function
is a long chain of tests in which most are dead. `RegMap` is the same
function written out as its sixteen values, which is how a context is kept
between instructions: it does not grow, and it reads as a table.
-/

namespace TypedAsm

/-- A value for each register. -/
structure RegMap (α : Type) where
  rax : α
  rcx : α
  rdx : α
  rbx : α
  rsp : α
  rbp : α
  rsi : α
  rdi : α
  r8 : α
  r9 : α
  r10 : α
  r11 : α
  r12 : α
  r13 : α
  r14 : α
  r15 : α

/-- The function a table of values stands for. -/
@[reducible] def RegMap.get {α : Type} (m : RegMap α) : Reg → α
  | .rax => m.rax
  | .rcx => m.rcx
  | .rdx => m.rdx
  | .rbx => m.rbx
  | .rsp => m.rsp
  | .rbp => m.rbp
  | .rsi => m.rsi
  | .rdi => m.rdi
  | .r8 => m.r8
  | .r9 => m.r9
  | .r10 => m.r10
  | .r11 => m.r11
  | .r12 => m.r12
  | .r13 => m.r13
  | .r14 => m.r14
  | .r15 => m.r15

/-- Every function on registers is the table of its values. -/
theorem RegMap.eta {α : Type} (f : Reg → α) :
    f = RegMap.get ⟨f .rax, f .rcx, f .rdx, f .rbx, f .rsp, f .rbp, f .rsi, f .rdi, f .r8, f .r9, f .r10, f .r11, f .r12, f .r13, f .r14, f .r15⟩ :=
  funext fun r => by cases r <;> rfl

/-- A block may be typed with its context's register types written out as a
table. -/
theorem BlockOk.regsEta {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {a : BitVec 64}
    {Γ : Ctx}
    (h : BlockOk Φ fetch sys Ψ a
      { Γ with regs := RegMap.get ⟨Γ.regs .rax, Γ.regs .rcx, Γ.regs .rdx, Γ.regs .rbx, Γ.regs .rsp, Γ.regs .rbp, Γ.regs .rsi, Γ.regs .rdi, Γ.regs .r8, Γ.regs .r9, Γ.regs .r10, Γ.regs .r11, Γ.regs .r12, Γ.regs .r13, Γ.regs .r14, Γ.regs .r15⟩ }) :
    BlockOk Φ fetch sys Ψ a Γ := by
  rw [← RegMap.eta] at h
  exact h

/-- The same for one instruction. -/
theorem Straight.regsEta {Ψ : MemTy} {next : BitVec 64} {Γ Γ' : Ctx} {i : Instr}
    (h : Straight Ψ next
      { Γ with regs := RegMap.get ⟨Γ.regs .rax, Γ.regs .rcx, Γ.regs .rdx, Γ.regs .rbx, Γ.regs .rsp, Γ.regs .rbp, Γ.regs .rsi, Γ.regs .rdi, Γ.regs .r8, Γ.regs .r9, Γ.regs .r10, Γ.regs .r11, Γ.regs .r12, Γ.regs .r13, Γ.regs .r14, Γ.regs .r15⟩ } i Γ') :
    Straight Ψ next Γ i Γ' := by
  rw [← RegMap.eta] at h
  exact h

/-- And for the context an instruction leaves. -/
theorem Straight.regsEtaAfter {Ψ : MemTy} {next : BitVec 64} {Γ Γ' : Ctx} {i : Instr}
    (h : Straight Ψ next Γ i
      { Γ' with regs := RegMap.get ⟨Γ'.regs .rax, Γ'.regs .rcx, Γ'.regs .rdx, Γ'.regs .rbx, Γ'.regs .rsp, Γ'.regs .rbp, Γ'.regs .rsi, Γ'.regs .rdi, Γ'.regs .r8, Γ'.regs .r9, Γ'.regs .r10, Γ'.regs .r11, Γ'.regs .r12, Γ'.regs .r13, Γ'.regs .r14, Γ'.regs .r15⟩ }) :
    Straight Ψ next Γ i Γ' := by
  rw [← RegMap.eta] at h
  exact h

/-- Whatever holds of a context holds of it with its register types written
out as a table. -/
theorem Ctx.asTable {P : Ctx → Prop} {Γ : Ctx} (h : P Γ) :
    P { Γ with regs := RegMap.get ⟨Γ.regs .rax, Γ.regs .rcx, Γ.regs .rdx, Γ.regs .rbx, Γ.regs .rsp, Γ.regs .rbp, Γ.regs .rsi, Γ.regs .rdi, Γ.regs .r8, Γ.regs .r9, Γ.regs .r10, Γ.regs .r11, Γ.regs .r12, Γ.regs .r13, Γ.regs .r14, Γ.regs .r15⟩ } := by
  rw [← RegMap.eta]
  exact h

/-- The other way: a block typed as it stands is typed with the table. For
closing a goal the tactics have put in table form with a fact that was not
stated in it. -/
theorem BlockOk.asTable {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {a : BitVec 64}
    {Γ : Ctx} (h : BlockOk Φ fetch sys Ψ a Γ) :
    BlockOk Φ fetch sys Ψ a
      { Γ with regs := RegMap.get ⟨Γ.regs .rax, Γ.regs .rcx, Γ.regs .rdx, Γ.regs .rbx, Γ.regs .rsp, Γ.regs .rbp, Γ.regs .rsi, Γ.regs .rdi, Γ.regs .r8, Γ.regs .r9, Γ.regs .r10, Γ.regs .r11, Γ.regs .r12, Γ.regs .r13, Γ.regs .r14, Γ.regs .r15⟩ } := by
  rw [← RegMap.eta]
  exact h

end TypedAsm
