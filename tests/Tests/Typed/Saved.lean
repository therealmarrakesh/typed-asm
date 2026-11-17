import Tests.Typed.ArgsStack

/-!
# The checker's tests: a label inside a function that has pushed

A label inside a function may say the function has pushed registers it
keeps for its caller: they are held in the stack as they were when the
function was entered, and the function is to give them back so. Checked by
the kernel as this file is compiled, with what is refused.
-/

open TypedAsm TypedAsm.U

namespace Tests.Saved

/-- Labels mark where control can arrive from elsewhere. -/
inductive L
  | start | f | loop
  deriving DecidableEq

/-- A function that pushes a register it keeps, uses it in a loop, and
ends as given. -/
def code (ending : List (Asm L)) : List (Asm L) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 5)),
  .call .f,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 0)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .f,
  .ins (.push .r12),
  .ins (.mov .w64 (.rm_r (.reg .r12) .rdi)),
  .label .loop,
  .ins (.alu .sub .w64 (.rm_i (.reg .r12) 1)),
  .jcc .ne .loop] ++ ending

/-- The register popped, and the return. -/
def restored : List (Asm L) := [.ins (.pop .r12), .ins .ret]

/-- The stack pointer moved past what was pushed, the register left as the
loop left it, and the return. -/
def dropped : List (Asm L) := [.ins (.alu .add .w64 (.rm_i (.reg .rsp) 8)), .ins .ret]

def pg (e : List (Asm L)) : Prog := { code := progCode (Asm.table (Asm.base (code e)) (code e)) }

/-- The labels: the start; the function, wanting eight bytes of stack; and
its loop, where it has pushed `r12`. -/
def labels (e : List (Asm L)) (saved : List Reg) : List U.Label :=
  [⟨Asm.addr (code e) (Asm.base (code e)) .start, entryOf 2⟩,
   ⟨Asm.addr (code e) (Asm.base (code e)) .f, inFunction (room := 8)⟩,
   ⟨Asm.addr (code e) (Asm.base (code e)) .loop, inFunction (room := 8) (saved := saved)⟩]

-- the register pushed, used, and popped before the return: typed
example : wholeOk (code restored) .start 2 (pg restored) (labels restored [.r12]) 40 = true := by
  decide +kernel

-- the register not given back as it was: refused
example : wholeOk (code dropped) .start 2 (pg dropped) (labels dropped [.r12]) 40 = false := by
  decide +kernel

-- the loop's label not saying the push: the loop is not reached as it says, refused
example : wholeOk (code restored) .start 2 (pg restored) (labels restored []) 40 = false := by
  decide +kernel

end Tests.Saved
