import BufferProgram
import TypedAsm.Tactic

/-!
# Buffer: typing and safety

The program is in `BufferProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Buffer

/-! ## The typing -/

/-- In the loop the buffer is allocated: sixteen plain bytes of stack. -/
def looping : Ctx := ⟨fun _ => .int, [.raw 16], 0, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 2)
  | loop : At .loop looping

/-- No memory blocks. -/
def blocks : List (BitVec 64 × Layout) := []

asm_typing At blocks blocks room 2

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- sub rsp, 16
    ty_step
    -- from here on as in the loop
    ty_name .rsp as sp
    ty_block
  | loop =>
    -- the stack pointer's value is called `sp`, so `lea rsi, [rsp]` yields
    -- a known address and the `read` is checked against the two slots there
    ty_name .rsp as sp
    ty_block

/-! ## Safety -/

asm_safety At.start

end Buffer

