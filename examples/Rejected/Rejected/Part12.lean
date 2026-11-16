import Rejected.Common

/-!
# Calls and jumps through a value, the other two ways

A call through a pointer to code that is no function: the code wants one
context, which has the return address on its stack, and that says where it
returns to. And a jump through a pointer to a function, made by a function
on behalf of its own caller: a tail call. Both type with nothing said.
-/

open TypedAsm

namespace Rejected.Helper

inductive Label
  | start | back | helper
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rcx (.rip 0)) .helper,
  .ins (.call (.ind (.reg .rcx))),
  .label .back,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .helper,
  .ins (.mov .w32 (.rm_i (.reg .rax) 3)),
  .ins .ret]

asm_program code start .start stack 1

#guard exitsWith 3 (run fetch linux 100 start)

/-- Back from the helper: nothing is known of any register. -/
def backCtx : Ctx := ⟨fun _ => .int, [], 8, Flags.Any, [], 0⟩

/-- In the helper: the return address is that of code wanting `backCtx`. -/
def helperCtx : Ctx := ⟨fun _ => .int, [.slot (.code backCtx)], 0, Flags.Any, [], 0⟩

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | back : At .back backCtx
  | helper : At .helper helperCtx

asm_typing At

example : BlocksOk Φ fetch linux Ψ := by ty_program

end Rejected.Helper

namespace Rejected.Tail

inductive Label
  | start | back | first | second
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rcx (.rip 0)) .second,
  .call .first,
  .label .back,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  -- `first` does nothing itself: it goes on to the function `rcx` points to,
  -- which returns to `first`'s caller
  .label .first,
  .ins (.jmp (.ind (.reg .rcx))),
  .label .second,
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)),
  .ins .ret]

asm_program code start .start stack 1

#guard exitsWith 9 (run fetch linux 100 start)

/-- `second` takes nothing and returns a number. -/
def secondSig : FnSig where
  args := fun _ => .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- `first` takes a pointer to such a function in `rcx`. -/
def firstSig : FnSig where
  args := fun r => if r = .rcx then secondSig.ty else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

def backCtx : Ctx := ⟨fun _ => .int, [], 8, Flags.Any, [], 0⟩

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | back : At .back backCtx
  | first (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    firstSig.CallerOk saved ret rest room → At .first (firstSig.entry saved ret rest room)
  | second (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    secondSig.CallerOk saved ret rest room → At .second (secondSig.entry saved ret rest room)

asm_typing At

example : BlocksOk Φ fetch linux Ψ := by ty_program

end Rejected.Tail
