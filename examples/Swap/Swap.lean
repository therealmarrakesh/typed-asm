import SwapProgram
import TypedAsm.Tactic

/-!
# Swap: typing and safety

The program is in `SwapProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Swap

/-! ## The typing -/

/-- A pointer to a writable record of sixteen plain bytes: two numbers. -/
def pair : Ty := .ptr (.raw 16) true 0

/-- `swap` takes the pointer in `rdi`, promises nothing about the registers
it uses, and preserves the callee-saved registers. -/
def swapSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- Register types with the pointer in one register and nothing known about the rest. -/
def only (reg : Reg) : Reg → Ty := fun r => if r = reg then pair else .int

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 2)
  /-- After the first call the pointer is still in `rbx`. -/
  | afterFirst : At .afterFirst ⟨only .rbx, [], 16, Flags.Any, [], 0⟩
  | afterSecond : At .afterSecond ⟨only .rbx, [.slot pair], 8, Flags.Any, [], 0⟩
  | swap (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    swapSig.CallerOk saved ret rest room → At .swap (swapSig.entry saved ret rest room)

asm_typing At

/-! ## Safety -/

-- And it ends only with status 0.
asm_safety At.start exits (· = 0)

end Swap

