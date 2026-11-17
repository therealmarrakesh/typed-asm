import SwapProgram
import TypedAsm.U.Say
import TypedAsm.EndToEnd

/-!
# Swap: typing and safety

The program is in `SwapProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Swap

/-! ## What the labels want -/

/-- The program for the checker: its instructions; that the record is in
the segment it was written in; and that it is to end with status nought. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn (blocksOf code .start) (Asm.addr code base .record)
    pre := preExits (· == 0) }

/-- The labels. `swap` takes in `rdi` a pointer to memory it may write, and
gives back the registers a function must as it found them. That the
pointer is still in `rbx` after each call follows; it is not said. -/
def labels : List U.Label :=
  [⟨entry, entryOf 2⟩,
   ⟨Asm.addr code base .swap, inFunction [] [(.was .rdi, .ptr (.mk 4096 .nil) true 0)]⟩]

/-! ## The check -/

theorem checked : wholeOk code .start 2 pg labels 20 = true := by decide +kernel

/-! ## What it shows -/

/-- The state `SwapProgram` starts the program in is the one the check is
of, in the world it has. -/
theorem start_eq : start = startIn code .start 2 start.world := by
  have e : start = startOf code .start 2 := by
    unfold start prepared startOf entry base stackStretch
    rfl
  rw [e]
  rfl

/-- **Swap is safe, on the machine that decodes its instructions from
memory, and ends only with status nought: whatever the world outside it
holds.** -/
theorem safe_exits (w : World) :
    SafeMem linux (startIn code .start 2 w) ∧ ExitsOnly fetch (· = 0) (startIn code .start 2 w) :=
  whole_exits checked (Q := fun c => c = 0) (q := fun c => c == 0) (fun c h => by simpa using h)
    rfl (KindsOk.none _) w

/-- So the program as `lake exe swap` runs it is safe. -/
theorem safe : SafeMem linux start := start_eq ▸ (safe_exits start.world).1

/-- And it ends only with status nought. -/
theorem exits : ExitsOnly fetch (· = 0) start := start_eq ▸ (safe_exits start.world).2

end Swap
