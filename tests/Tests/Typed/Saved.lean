import Tests.Typed.ArgsStack
import TypedAsm.U.Checked
import LengthsProgram

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
  deriving DecidableEq, Hashable

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
  [⟨Asm.addr (code e) (Asm.base (code e)) .start, inProgram 2⟩,
   ⟨Asm.addr (code e) (Asm.base (code e)) .f, inFunction (room := 8)⟩,
   ⟨Asm.addr (code e) (Asm.base (code e)) .loop, inFunction (room := 8) (pushed := saved.map .saved)⟩]

-- the register pushed, used, and popped before the return: typed
example : wholeOk (code restored) .start 2 (pg restored) (labels restored [.r12]) 40 = true := by
  decide +kernel

-- the register not given back as it was: refused
example : wholeOk (code dropped) .start 2 (pg dropped) (labels dropped [.r12]) 40 = false := by
  decide +kernel

-- the loop's label not saying the push: the loop is not reached as it says, refused
example : wholeOk (code restored) .start 2 (pg restored) (labels restored []) 40 = false := by
  decide +kernel

/-! ## What a pushed slot holds, said at a label of the program's own -/

inductive M
  | start | loop
  deriving DecidableEq, Hashable

/-- A number pushed, a loop that leaves the stack alone, and the number
popped to end with. -/
def kept : List (Asm M) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rbx) 7)),
  .ins (.push .rbx),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 3)),
  .label .loop,
  .ins (.alu .sub .w64 (.rm_i (.reg .rcx) 1)),
  .jcc .ne .loop,
  .ins (.pop .rdi),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

def pgKept : Prog :=
  { code := progCode (Asm.table (Asm.base kept) kept), pre := preExits (· == 7) }

def keptLabels (p : Pushed) : List U.Label :=
  [⟨Asm.addr kept (Asm.base kept) .start, inProgram 1⟩,
   ⟨Asm.addr kept (Asm.base kept) .loop, inProgram 1 (pushed := [p])⟩]

-- the loop's label says the slot holds seven: the program ends with seven
example : wholeOk kept .start 1 pgKept (keptLabels (.val 7)) 40 = true := by decide +kernel

-- the label saying only that eight bytes are pushed: what is popped is not known, refused
example : wholeOk kept .start 1 pgKept (keptLabels .any) 40 = false := by decide +kernel

-- the label saying the slot holds another number: not what is there, refused
example : wholeOk kept .start 1 pgKept (keptLabels (.val 8)) 40 = false := by decide +kernel

/-! ## What the command says of a program it refuses -/

-- of a program that checks, nothing
example : wholeWhy kept .start 1 [] (blocksOf kept .start) pgKept (keptLabels (.val 7))
    (needFuel pgKept (keptLabels (.val 7)) []) = none := by decide +kernel

-- of one whose labels are refused, the refusals
example : (wholeWhy kept .start 1 [] (blocksOf kept .start) pgKept (keptLabels .any)
    (needFuel pgKept (keptLabels .any) [])).isSome = true := by decide +kernel

-- of one with no label where it starts, that
example : (wholeWhy kept .start 1 [] (blocksOf kept .start) pgKept [] 40).map
    (·.startsWith "no label is at") = some true := by decide +kernel

-- of one with no label on its loop, that the loop is to have one
example : (tidy [] (explain { code := progCode (Asm.table Lengths.base Lengths.code) }
    [⟨Lengths.entry, inProgram 4⟩] 27)).map (·.why) = [againSay] := by decide +kernel

-- a loop that goes round a number of times that is written out needs none, where the check
-- is let go far enough: it is walked each time round
example : explain pgKept [⟨Asm.addr kept (Asm.base kept) .start, inProgram 1⟩] 20 = [] := by
  decide +kernel

end Tests.Saved
