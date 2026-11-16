import FactProgram
import TypedAsm.Tactic

/-!
# Fact: typing, safety, and what it computes

The program is in `FactProgram.lean`. This file types it and proves it safe,
and proves that it ends with the factorial of five as its status: the
function's signature says its result is exactly the factorial of its
argument, and the typing against a system that lets the program end only
with status 120 is the proof. It is kept separate so that running the
program does not link the tactics.
-/

open TypedAsm

namespace Fact

/-! ## The typing -/

/-- The number `n` as a machine value. -/
def num (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

/-- The factorial of `n`. -/
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

/-- `fact` called with exactly `n` in `rdi` uses two stack slots for each of
the `n` calls it makes to itself, and returns with exactly the factorial of
`n` in `rax`, as far as it fits in 64 bits. -/
def factSig (n : Nat) : FnSig where
  args := fun r => if r = .rdi then .eq (num n) else .int
  results := fun r => if r = .rax then .eq (num (fac n)) else .int
  preserved := calleeSaved
  need := 16 * n

/-- After the call: `rax` holds exactly the factorial of five. -/
def fin : Ctx := ⟨fun r => if r = .rax then .eq (num (fac 5)) else .int, [], 88, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 11)
  | afterCall : At .afterCall fin
  /-- The argument is a number a register holds: below `2 ^ 64`. -/
  | fact (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (factSig n).CallerOk saved ret rest room → n < 2 ^ 64 →
    At .fact ((factSig n).entry saved ret rest room)
  /-- Reached only with an argument that is not zero. -/
  | again (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (factSig n).CallerOk saved ret rest room → 0 < n → n < 2 ^ 64 →
    At .again ((factSig n).entry saved ret rest room)
  /-- Back from the inner call: `rax` holds the factorial of one less, and the
  argument is on the stack, above this call's own return address. -/
  | afterAgain (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (m : Nat) :
    (factSig n).CallerOk saved ret rest (m + 16) → 0 < n →
    At .afterAgain ⟨fun r => if r = .rax then .eq (num (fac (n - 1)))
        else if calleeSaved r then saved r else .int,
      .slot (.eq (num n)) :: .slot (.code ret) :: rest, m + 8, Flags.Any, ret.owned, ret.above⟩

asm_typing At

/-! ## The program is well typed -/

/-- What the multiply at the end of a call computes: the argument times the
factorial of one less is the factorial of the argument. -/
theorem fac_step {n : Nat} (hn : 0 < n) : num (fac (n - 1)) * num n = num (fac n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [fac, num, BitVec.ofNat_mul, BitVec.mul_comm]

/-- The program is well typed where it may end only with status 120. Two
facts of arithmetic are all that is said by hand: what the function returns
for zero, and what its multiply computes. -/
theorem blocksOk : BlocksOk Φ fetch (linux.exitsOnly (· = 120)) Ψ := by
  ty_program
  case fact n saved ret rest room hK h64 =>
    ty_block
    -- returning 1: the test found the argument zero, and the factorial of
    -- zero is 1
    obtain rfl : n = 0 := by simp only [num] at hz; bv_omega
    exact Sub.refl _
  case afterAgain n saved ret rest m hK hn =>
    ty_block
    -- returning the product: the argument times the factorial of one less
    exact Sub.of_eq (by simpa [imulTrunc_fst] using fac_step hn)
  case again n saved ret rest room hK hn h64 =>
    -- the argument is not zero, so the caller left at least sixteen bytes
    have hroom : 16 * n ≤ room := hK.room
    obtain ⟨m, rfl⟩ : ∃ m, room = m + 16 := ⟨room - 16, by omega⟩
    -- the inner call gets exactly one less
    ty_call (factSig (n - 1))

/-! ## Safety, and the result -/

-- Safe, and it ends only with status 120, the factorial of five.
asm_safety At.start exits (· = 120)

end Fact

