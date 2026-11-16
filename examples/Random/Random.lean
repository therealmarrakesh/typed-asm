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

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and the program uses no stack. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | fail : At .fail (entryCtx 0)

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
    ty_step
    -- `rdi` holds exactly the buffer's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .rdi) (base := dataBase) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    -- the `getrandom`, the test of its result, the `write` of that many bytes, and `exit`
    ty_block
  | fail => ty_block

/-! ## Safety -/

asm_safety At.start

end Random

