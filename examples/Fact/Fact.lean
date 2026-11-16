import FactProgram
import TypedAsm.Tactic

/-!
# Fact: typing and safety

The program is in `FactProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Fact

/-! ## The typing -/

/-- The number `n` as a machine value. -/
def num (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

/-- `fact` called with exactly `n` in `rdi` uses two stack slots for each of
the `n` calls it makes to itself. -/
def factSig (n : Nat) : FnSig where
  args := fun r => if r = .rdi then .eq (num n) else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 16 * n

/-- Nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 88, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 11)
  | afterCall : At .afterCall fin
  | fact (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (factSig n).CallerOk saved ret rest room → At .fact ((factSig n).entry saved ret rest room)
  /-- Reached only with an argument that is not zero. -/
  | again (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (factSig n).CallerOk saved ret rest room → 0 < n →
    At .again ((factSig n).entry saved ret rest room)
  /-- Back from the inner call: the argument is on the stack, above this
  call's own return address. -/
  | afterAgain (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (m : Nat) :
    (factSig n).CallerOk saved ret rest (m + 16) →
    At .afterAgain ⟨fun r => if calleeSaved r then saved r else .int,
      .slot (.eq (num n)) :: .slot (.code ret) :: rest, m + 8, Flags.Any, ret.owned, ret.above⟩

asm_typing At

/-! ## Arithmetic facts the recursion relies on -/

/-- One less than a number that is not zero. -/
theorem decr {n : Nat} (hn : 0 < n) :
    (AluOp.apply .sub (num n) ((1 : BitVec 32).signExtend 64)).1 = num (n - 1) := by
  have h1 : ((1 : BitVec 32).signExtend 64) = 1 := by decide
  simp only [AluOp.apply, subBorrow_fst, h1, num]
  bv_omega

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program
  case start =>
    ty_call (factSig 5)
  case fact n saved ret rest room hK =>
    ty_block
    -- going on to recurse: the test found the argument not to be zero
    refine Nat.pos_of_ne_zero (fun h0 => ?_)
    subst h0
    simp [Cond.eval, Flags.ofResult, num] at hcond
  case again n saved ret rest room hK hn =>
    -- the argument is not zero, so the caller left at least sixteen bytes
    have hroom : 16 * n ≤ room := hK.room
    obtain ⟨m, rfl⟩ : ∃ m, room = m + 16 := ⟨room - 16, by omega⟩
    ty_call (factSig (n - 1))
    -- the inner call gets exactly one less
    exact Sub.of_eq (decr hn)

/-! ## Safety -/

asm_safety At.start

end Fact

