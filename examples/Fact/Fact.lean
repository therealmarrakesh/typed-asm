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
def fin : Ctx := ⟨fun _ => .int, [], 88, Flags.Any, []⟩

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
      .slot (.eq (num n)) :: .slot (.code ret) :: rest, m + 8, Flags.Any, ret.owned⟩

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- No memory blocks. -/
def blocks : List (BitVec 64 × Layout) := []

def Ψ : MemTy := .ofList blocks []

/-! ## Arithmetic facts the recursion relies on -/

/-- One less than a number that is not zero. -/
theorem decr {n : Nat} (hn : 0 < n) :
    (AluOp.apply .sub (num n) ((1 : BitVec 32).signExtend 64)).1 = num (n - 1) := by
  have h1 : ((1 : BitVec 32).signExtend 64) = 1 := by decide
  simp only [AluOp.apply, subBorrow_fst, h1, num]
  bv_omega

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    ty_steps
    ty_call (factSig 5)
  | afterCall => ty_block
  | fact n saved ret rest room hK =>
    ty_block
    -- going on to recurse: the test found the argument not to be zero
    refine Nat.pos_of_ne_zero (fun h0 => ?_)
    subst h0
    simp [Cond.eval, Flags.ofResult, num] at hcond
  | again n saved ret rest room hK hn =>
    -- the argument is not zero, so the caller left at least sixteen bytes
    have hroom : 16 * n ≤ room := hK.room
    obtain ⟨m, rfl⟩ : ∃ m, room = m + 16 := ⟨room - 16, by omega⟩
    ty_steps
    ty_call (factSig (n - 1))
    -- the inner call gets exactly one less
    exact Sub.of_eq (decr hn)
  | afterAgain n saved ret rest m hK => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory and eleven writable stack slots below `rsp`. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry parts blocks 11 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck
and never faults: in particular the recursion never runs past the stack it
was given. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

end Fact

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Fact.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fact.safeMem
