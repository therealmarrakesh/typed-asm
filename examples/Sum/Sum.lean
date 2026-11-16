import SumProgram
import TypedAsm.Tactic

/-!
# Sum: typing and safety

The program is in `SumProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Sum

/-! ## The typing -/

/-- A pointer to element `i` of a read-only array of `n` integers. -/
def elem (n i : Nat) : Ty := .ptr (.raw (8 * n)) false (8 * i)

/-- The counter after `i` of `n` elements have been consumed. -/
def left (n i : Nat) : BitVec 64 := BitVec.ofNat 64 (n - i)

/-- Register types inside `sum` after `i` elements: the pointer is at element
`i`, the counter is exactly `n - i`, and the callee-saved registers have
whatever types the caller gave them. -/
def sumRegs (n i : Nat) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if calleeSaved r then saved r
    else if r = .rdi then elem n i else if r = .rsi then .eq (left n i) else .int

/-- `sum` takes a pointer to `n` integers in `rdi` and exactly `n` in `rsi`,
and preserves the callee-saved registers. -/
def sumSig (n : Nat) : FnSig where
  args := sumRegs n 0 (fun _ => .int)
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- After the call: nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 8, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | afterCall : At .afterCall fin
  | sum (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → At .sum ((sumSig n).entry saved ret rest room)
  /-- The loop invariant, for `i < n` elements consumed. -/
  | loop (n i : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → i < n →
    At .loop ⟨sumRegs n i saved, .slot (.code ret) :: rest, room, Flags.Any, ret.owned, ret.above⟩
  | done (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → At .done ((sumSig n).exit saved ret rest room)

asm_typing At

/-! ## Arithmetic facts the loop relies on -/

theorem left_ne_zero {n i : Nat} (h : left n i ≠ 0) : i < n := by
  apply Nat.lt_of_sub_ne_zero
  intro h0
  exact h (by simp [left, h0])

/-- Decrementing the counter gives the counter for one more element consumed. -/
theorem decr {n i : Nat} (hi : i < n) :
    (AluOp.apply .sub (left n i) ((1 : BitVec 32).signExtend 64)).1 = left n (i + 1) := by
  have h1 : ((1 : BitVec 32).signExtend 64) = 1 := by decide
  simp only [AluOp.apply, subBorrow_fst, h1, left]
  bv_omega

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program
  case sum n saved ret rest room hK =>
    ty_block
    -- entering the loop: the count is not zero, so the invariant holds with `i = 0`
    apply left_ne_zero
    intro h0
    simp [Cond.eval, Flags.ofResult, h0] at hcond
  case loop n i saved ret rest room hK hi =>
    ty_block
    -- going round again: the counter is the one for `i + 1` elements consumed,
    · exact Sub.of_eq (decr hi)
    -- and it is not zero, so `i + 1 < n`
    · apply left_ne_zero
      intro h0
      rw [← decr hi] at h0
      simp [Cond.eval, AluOp.apply, subBorrow_zf] at hcond
      exact hcond (by simpa [AluOp.apply] using h0)

/-! ## Safety -/

asm_safety At.start

end Sum

