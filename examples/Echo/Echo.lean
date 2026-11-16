import EchoProgram
import TypedAsm.Tactic

/-!
# Echo: typing and safety

The program is in `EchoProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Echo

-- Where the buffer is loaded.
asm_label dataBase .buffer

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and the program uses no stack. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

/-- The buffer: sixteen plain bytes, writable. -/
def bufferLayout : Layout := ⟨.raw 16, true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, bufferLayout)]

asm_typing At blocks blocks room 0

/-! ## Safety -/

asm_safety At.start

end Echo

