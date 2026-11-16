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

/-! ## Safety -/

asm_safety At.start

end Buffer

