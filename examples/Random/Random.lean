import RandomProgram
import TypedAsm.Tactic

/-!
# Random: typing and safety

The program is in `RandomProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the
tactics.
-/

open TypedAsm

namespace Random

-- Where the buffer is loaded.
asm_label dataBase .buffer

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and the program uses no stack. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

/-- The buffer: 512 plain bytes, writable. -/
def bufferLayout : Layout := ⟨.raw 512, true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, bufferLayout)]

asm_typing At blocks blocks room 0

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + buffer]
    -- the `getrandom`, the test of its result, the `write` of that many bytes, and `exit`
    ty_block

/-! ## Safety -/

asm_safety At.start

end Random

