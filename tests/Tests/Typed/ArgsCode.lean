import Tests.Typed.Why

/-!
# The checker's tests: a program started with arguments, going through a table of code

A program started with arguments may say of its static data, as any
program may, that it holds the addresses of code wanting given contexts.
That is read off the program's bytes, and rests on the code at those
addresses being typed: which is the labels' typing. Checked by the kernel
as this file is compiled, with what is refused.
-/

open TypedAsm TypedAsm.U

namespace Tests.ArgsCode

/-- Labels mark where control can arrive from elsewhere. -/
inductive L
  | start | bad | zero | one | table
  deriving DecidableEq

/-- An index, compared with the table's length; a jump through the table;
and at each of the table's two addresses, the program ending. -/
def code : List (Asm L) := [
  .label .start,
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.mov .w32 (.rm_i (.reg .rcx) 1)),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rcx) 2)),
  .jcc .ae .bad,
  .ins (.jmp (.ind (.mem (.sib (some .rbx) (some (.rcx, .s8)) 0)))),
  .label .bad,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 2)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .zero,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 0)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .one,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .segment .ro,
  .label .table, .quad .zero, .quad .one]

/-- The blocks: the table, two addresses each of this type, not to be
written. -/
def blocks (τ : TyS) : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start
    [(Asm.addr code (Asm.base code) .table,
      { shape := .mk 16 (.cons 0 τ (.cons 8 τ .nil)), writable := false })]

def pg (τ : TyS) : Prog :=
  { code := progCode (Asm.table (Asm.base code) code)
    statics := staticIn (blocks τ) (Asm.addr code (Asm.base code) .table) }

/-- The labels: the start, and the two places the table leads to, each
wanting what a program started with arguments has when it starts. -/
def labels : List U.Label :=
  [⟨Asm.addr code (Asm.base code) .start, inProgram 0⟩,
   ⟨Asm.addr code (Asm.base code) .zero, inProgram 0⟩,
   ⟨Asm.addr code (Asm.base code) .one, inProgram 0⟩]

/-- **The check**: the table holds the addresses of code wanting what the
two labels want. -/
theorem checked :
    wholeOkWith code .start 0 [] (blocks (codeOf (inProgram 0))) (pg (codeOf (inProgram 0))) labels 40 = true := by
  decide +kernel

/-- So the program is safe, whatever its arguments and whatever the world
outside it holds. -/
theorem safe_in (args : List (List Byte)) (w : World) :
    SafeMem linux (startIn code .start 0 args w) :=
  whole_safe checked rfl (LawsHold.nil _) args w

-- said to hold the addresses of functions, which the code there is not: refused
example : wholeOkWith code .start 0 [] (blocks (codeOf inFunction)) (pg (codeOf inFunction))
    labels 40 = false := by decide +kernel

end Tests.ArgsCode
