import StatProgram
import TypedAsm.Tactic

/-!
# Stat: typing and safety

The program is in `StatProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Stat

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | fail : At .fail (entryCtx 0)

/-- The buffer: 144 plain bytes, writable. That is the
size of what `fstat` stores, the largest of the three things stored here. -/
def bufferLayout : Layout := ⟨.raw 144, true, none, 0⟩

/-- One memory block, the buffer. The file's name before it needs no type. -/
def blocks : List (BitVec 64 × Layout) := [(bufferAt, bufferLayout)]

asm_typing At blocks blocks room 0

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- the arguments and the `openat`, then the test of what it answered
    ty_steps
    ty_branch
    -- mov r12, rax; lea r13, [rip + buffer]
    ty_step
    ty_step
    -- `r13` holds exactly the buffer's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .r13) (base := bufferAt) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    -- the rest: each call that stores into the buffer finds room for what it stores
    ty_block
  | fail => ty_block

/-! ## Safety -/

asm_safety At.start

end Stat

