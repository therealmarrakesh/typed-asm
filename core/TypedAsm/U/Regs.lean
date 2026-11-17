import TypedAsm.Instr

/-!
# Something for each register, as a table

Sixteen values written out, one for each register: how a checker keeps what
a context says of the registers. It does not grow as registers are given
new values, and it reads as a table.
-/

namespace TypedAsm.U

structure Regs (α : Type) where
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
  deriving DecidableEq, Repr

namespace Regs

variable {α : Type}

def get (m : Regs α) : Reg → α
  | .rax => m.rax | .rcx => m.rcx | .rdx => m.rdx | .rbx => m.rbx
  | .rsp => m.rsp | .rbp => m.rbp | .rsi => m.rsi | .rdi => m.rdi
  | .r8 => m.r8 | .r9 => m.r9 | .r10 => m.r10 | .r11 => m.r11
  | .r12 => m.r12 | .r13 => m.r13 | .r14 => m.r14 | .r15 => m.r15

def set (m : Regs α) (r : Reg) (v : α) : Regs α :=
  match r with
  | .rax => { m with rax := v } | .rcx => { m with rcx := v }
  | .rdx => { m with rdx := v } | .rbx => { m with rbx := v }
  | .rsp => { m with rsp := v } | .rbp => { m with rbp := v }
  | .rsi => { m with rsi := v } | .rdi => { m with rdi := v }
  | .r8 => { m with r8 := v } | .r9 => { m with r9 := v }
  | .r10 => { m with r10 := v } | .r11 => { m with r11 := v }
  | .r12 => { m with r12 := v } | .r13 => { m with r13 := v }
  | .r14 => { m with r14 := v } | .r15 => { m with r15 := v }

theorem get_set (m : Regs α) (r r' : Reg) (v : α) :
    (m.set r v).get r' = if r' = r then v else m.get r' := by
  cases r <;> cases r' <;> rfl

/-- The table with each value changed. -/
def map {β : Type} (f : α → β) (m : Regs α) : Regs β :=
  ⟨f m.rax, f m.rcx, f m.rdx, f m.rbx, f m.rsp, f m.rbp, f m.rsi, f m.rdi,
    f m.r8, f m.r9, f m.r10, f m.r11, f m.r12, f m.r13, f m.r14, f m.r15⟩

theorem get_map {β : Type} (f : α → β) (m : Regs α) (r : Reg) : (m.map f).get r = f (m.get r) := by
  cases r <;> rfl

end Regs

end TypedAsm.U
