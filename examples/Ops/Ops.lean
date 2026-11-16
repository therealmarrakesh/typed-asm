import OpsProgram
import TypedAsm.Tactic

/-!
# Ops: typing and safety

The program is in `OpsProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Ops

/-! ## The typing -/

/-- A pointer to a writable record of sixteen plain bytes: two numbers. -/
def pair : Ty := .ptr (.raw 16) true 0

/-- `compute` takes the pointer in `rdi`, uses two stack slots, and
preserves the callee-saved registers. -/
def computeSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 16

/-- After the call: nothing is known about any register, and the slot that
held the function pointer is still allocated. -/
def afterCtx : Ctx := ⟨fun _ => .int, [.raw 8], 24, Flags.Any, [], 0⟩

/-- Nothing is known about any register, and the stack is empty. -/
def fin : Ctx := ⟨fun _ => .int, [], 32, Flags.Any, [], 0⟩

/-- What the function pointer in `_start` points to: `compute`, entered by a
caller with one slot on its stack that returns to `afterCall`. -/
def computeCtx : Ctx := computeSig.entry (fun _ => .int) afterCtx [.raw 8] 16

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 4)
  | afterCall : At .afterCall afterCtx
  | finish : At .finish fin
  | compute (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    computeSig.CallerOk saved ret rest room → At .compute (computeSig.entry saved ret rest room)

def recordLayout : Layout := ⟨.raw 16, true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, recordLayout)]

asm_typing At blocks blocks room 4

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + record]
    ty_step
    -- `rdi` holds exactly the record's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .rdi) (base := dataBase) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    -- lea rax, [rip + compute]
    ty_step
    -- `rax` holds exactly the address of `compute`, so it is a pointer to that function
    ty_code_ptr .rax to computeCtx
    -- the pointer is stored in a stack slot and called through it
    ty_steps
    ty_call computeSig
  | afterCall =>
    ty_steps
    -- `rcx` holds exactly the address of `finish`
    ty_code_ptr .rcx to fin
    ty_block
  | finish => ty_block
  | compute saved ret rest room hK =>
    -- make the two slots the signature guarantees visible, so the frame can be allocated
    obtain ⟨m, rfl⟩ := hK.room_split
    ty_block

/-! ## Safety -/

asm_safety At.start

end Ops

