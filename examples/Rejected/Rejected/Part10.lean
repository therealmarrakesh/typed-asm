import Rejected.Common

/-!
# Loop parameters found by arithmetic

A loop over an array that stands sixteen bytes into its block. The loop's
context has the pointer at byte `16 + 8 * i`, for `i` elements consumed; the
block comes round with the pointer eight bytes on. That this is the loop's
context for `i + 1` is found by arithmetic on the two offsets, however they
are written, and the program types with nothing said beyond its contexts.
-/

open TypedAsm

namespace Rejected.Header

inductive Label
  | start | afterCall | sum | loop | done | array
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .array,
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 16)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 5)),
  .call .sum,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .sum,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.test .w64 (.reg .rsi) (.reg .rsi)),
  .jcc .e .done,
  .label .loop,
  .ins (.alu .add .w64 (.r_m .rax (.sib (some .rdi) none 0))),
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 8)),
  .ins (.alu .sub .w64 (.rm_i (.reg .rsi) 1)),
  .jcc .ne .loop,
  .label .done,
  .ins .ret,
  .align 8,
  .label .array, .bytes (List.replicate 16 0 ++ [3, 1, 4, 1, 5].flatMap le64)]

asm_program code start .start stack 1

-- sixteen bytes of header are passed over, and the five numbers come to 14
#guard exitsWith 14 (run fetch linux 100 start)

/-- A pointer to element `i` of `n` integers that follow a header of sixteen
bytes. -/
def elem (n i : Nat) : Ty := .ptr (.raw (16 + 8 * n)) false (16 + 8 * i)

def left (n i : Nat) : BitVec 64 := BitVec.ofNat 64 (n - i)

def sumRegs (n i : Nat) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if calleeSaved r then saved r
    else if r = .rdi then elem n i else if r = .rsi then .eq (left n i) else .int

def sumSig (n : Nat) : FnSig where
  args := sumRegs n 0 (fun _ => .int)
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

def fin : Ctx := ⟨fun _ => .int, [], 8, Flags.Any, [], 0⟩

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | afterCall : At .afterCall fin
  | sum (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → At .sum ((sumSig n).entry saved ret rest room)
  | loop (n i : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → i < n →
    At .loop ⟨sumRegs n i saved, .slot (.code ret) :: rest, room, Flags.Any, ret.owned, ret.above⟩
  | done (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → At .done ((sumSig n).exit saved ret rest room)

asm_typing At

example : BlocksOk Φ fetch linux Ψ := by ty_program

end Rejected.Header
