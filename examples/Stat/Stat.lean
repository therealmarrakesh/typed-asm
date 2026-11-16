import StatProgram
import TypedAsm.Tactic

/-!
# Stat: typing and safety

The program is in `StatProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Stat

-- Where the buffer is.
asm_label bufferAt .buffer

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

/-- The buffer: 144 plain bytes, writable. That is the
size of what `fstat` stores, the largest of the three things stored here. -/
def bufferLayout : Layout := ⟨.raw 144, true, none, 0⟩

/-- One memory block, the buffer. The file's name before it needs no type. -/
def blocks : List (BitVec 64 × Layout) := [(bufferAt, bufferLayout)]

asm_typing At blocks blocks room 0

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program

/-! ## Safety -/

asm_safety At.start

end Stat

