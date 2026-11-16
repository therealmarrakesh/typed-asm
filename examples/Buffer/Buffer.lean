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

asm_typing At

/-! ## Safety -/

-- And it ends only with status 0.
asm_safety At.start exits (· = 0)

end Buffer

