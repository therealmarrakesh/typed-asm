import Tests.Typed.ArgsCode

/-!
# The checker's tests: a program started with arguments that uses its stack

A program started with arguments has a stack below them, as any program
has: it may push, and call a function, which is typed once for every
caller as any function is. Checked by the kernel as this file is compiled,
with what is refused.
-/

open TypedAsm TypedAsm.U

namespace Tests.ArgsStack

/-- Labels mark where control can arrive from elsewhere. -/
inductive L
  | start | back | keep
  deriving DecidableEq, Hashable

/-- The count of arguments is pushed, a function called that pushes and
pops a register of its own, the count popped again, and the program ends
with it. -/
def code : List (Asm L) := [
  .label .start,
  .ins (.mov .w64 (.r_m .rbx (.sib (some .rsp) none 0))),
  .ins (.push .rbx),
  .call .keep,
  .label .back,
  .ins (.pop .rdi),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .keep,
  .ins (.push .r12),
  .ins (.pop .r12),
  .ins .ret]

def pg : Prog := { code := progCode (Asm.table (Asm.base code) code) }

/-- The labels: the start, with two slots of stack; where the call returns
to, one slot pushed; and the function, which wants eight bytes of stack. -/
def labels (n : Nat) : List U.Label :=
  [⟨Asm.addr code (Asm.base code) .start, inProgram n⟩,
   ⟨Asm.addr code (Asm.base code) .back, inProgram n (pushed := [.any])⟩,
   ⟨Asm.addr code (Asm.base code) .keep, inFunction (room := 8)⟩]

/-- **The check.** -/
theorem checked : wholeOkWith code .start 2 [] (blocksOf code .start) pg (labels 2) 40 = true := by
  decide +kernel

/-- So the program is safe, whatever its arguments and whatever the world
outside it holds. -/
theorem safe_in (args : List (List Byte)) (w : World) :
    SafeMem linux (startIn code .start 2 args w) :=
  whole_safe checked rfl (LawsHold.nil _) args w

-- with no stack below the arguments, the push is refused
example : wholeOkWith code .start 0 [] (blocksOf code .start) pg (labels 0) 40 = false := by
  decide +kernel

end Tests.ArgsStack
