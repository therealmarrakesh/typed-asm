import KeepProgram
import TypedAsm.Tactic

/-!
# Keep: typing and safety

The program is in `KeepProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Keep

/-! ## The typing -/

/-- `pause` preserves the callee-saved registers and also the stack pointer:
when it has returned, `rsp` is where it was before the call. -/
def pauseSig : FnSig where
  args := fun _ => .int
  results := fun _ => .int
  preserved := fun r => calleeSaved r || r == .rsp
  need := 0

/-- Back from the call: the stack pointer is exactly `sp`, as before it,
and `rbx` holds the address of the buffer, which is where `rsp` points. -/
def kept (sp : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rsp then .eq sp else if r = .rbx then .eq sp else .int, [.raw 16], 8, Flags.Any, [], 0⟩

/-- Nothing is known about any register; the buffer is still allocated. -/
def ending : Ctx := ⟨fun _ => .int, [.raw 16], 8, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 3)
  | back (sp : BitVec 64) : At .back (kept sp)
  | pause (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    pauseSig.CallerOk saved ret rest room → At .pause (pauseSig.entry saved ret rest room)

/-- No memory blocks. -/
def blocks : List (BitVec 64 × Layout) := []

asm_typing At blocks blocks room 3

/-! ## Safety -/

asm_safety At.start

end Keep

