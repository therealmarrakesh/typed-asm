import FrameProgram
import TypedAsm.Tactic

/-!
# Frame: typing and safety

The program is in `FrameProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Frame

/-! ## The typing -/

/-- A pointer to a writable record of sixteen plain bytes: two numbers. -/
def pair : Ty := .ptr (.raw 16) true 0

/-- `pick` takes the pointer in `rdi`, uses two stack slots, and preserves
the callee-saved registers. -/
def pickSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 16

/-- Nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 24, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 3)
  | afterCall : At .afterCall fin
  | pick (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    pickSig.CallerOk saved ret rest room → At .pick (pickSig.entry saved ret rest room)

def recordLayout : Layout := ⟨.raw 16, true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, recordLayout)]

asm_typing At blocks blocks room 3

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + record]
    ty_step
    ty_block
    ty_call pickSig
  | afterCall => ty_block
  | pick saved ret rest room hK =>
    -- make the two slots the signature guarantees visible, so the frame can be allocated
    obtain ⟨m, rfl⟩ := hK.room_split
    ty_block

/-! ## Safety -/

asm_safety At.start

end Frame

