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

/-- The table with one register's value changed. It is written by taking
the table apart, so that the others are the values they were and not each a
looking up in the table before: a check that Lean's kernel runs would
otherwise look back through every table there has been. -/
def set (m : Regs α) (r : Reg) (v : α) : Regs α :=
  match m, r with
  | ⟨_, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, .rax =>
    ⟨v, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, _, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, .rcx =>
    ⟨a0, v, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, _, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, .rdx =>
    ⟨a0, a1, v, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, _, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, .rbx =>
    ⟨a0, a1, a2, v, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, _, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, .rsp =>
    ⟨a0, a1, a2, a3, v, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, _, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, .rbp =>
    ⟨a0, a1, a2, a3, a4, v, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, _, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩, .rsi =>
    ⟨a0, a1, a2, a3, a4, a5, v, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, _, a8, a9, a10, a11, a12, a13, a14, a15⟩, .rdi =>
    ⟨a0, a1, a2, a3, a4, a5, a6, v, a8, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, a7, _, a9, a10, a11, a12, a13, a14, a15⟩, .r8 =>
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, v, a9, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, _, a10, a11, a12, a13, a14, a15⟩, .r9 =>
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, v, a10, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, _, a11, a12, a13, a14, a15⟩, .r10 =>
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, v, a11, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, _, a12, a13, a14, a15⟩, .r11 =>
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, v, a12, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, _, a13, a14, a15⟩, .r12 =>
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, v, a13, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _, a14, a15⟩, .r13 =>
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, v, a14, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, _, a15⟩, .r14 =>
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, v, a15⟩
  | ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, _⟩, .r15 =>
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, v⟩

theorem get_set (m : Regs α) (r r' : Reg) (v : α) :
    (m.set r v).get r' = if r' = r then v else m.get r' := by
  cases m; cases r <;> cases r' <;> rfl

/-- The table with each value changed. -/
def map {β : Type} (f : α → β) (m : Regs α) : Regs β :=
  ⟨f m.rax, f m.rcx, f m.rdx, f m.rbx, f m.rsp, f m.rbp, f m.rsi, f m.rdi,
    f m.r8, f m.r9, f m.r10, f m.r11, f m.r12, f m.r13, f m.r14, f m.r15⟩

theorem get_map {β : Type} (f : α → β) (m : Regs α) (r : Reg) : (m.map f).get r = f (m.get r) := by
  cases r <;> rfl

end Regs

end TypedAsm.U
