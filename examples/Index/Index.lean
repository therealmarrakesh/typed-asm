import IndexProgram
import TypedAsm.Tactic

/-!
# Index: typing and safety

The program is in `IndexProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Index

/-! ## The typing -/

/-- A pointer to a read-only array of `n` integers. -/
def arr (n : Nat) : Ty := .ptr (.raw (8 * n)) false 0

/-- `get` takes the array in `rdi`, exactly its length in `rsi`, and any
integer at all as the index in `rdx`. -/
def getSig (n : Nat) : FnSig where
  args := fun r =>
    if r = .rdi then arr n else if r = .rsi then .eq (BitVec.ofNat 64 n) else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- Nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 8, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | afterCall : At .afterCall fin
  | get (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (getSig n).CallerOk saved ret rest room → n < 2 ^ 64 →
    At .get ((getSig n).entry saved ret rest room)

asm_typing At

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program
  case start =>
    -- lea rdi, [rip + array]
    ty_call (getSig 5)

/-! ## Safety -/

asm_safety At.start

end Index

