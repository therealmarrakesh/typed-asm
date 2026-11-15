import PairProgram
import TypedAsm.Tactic

/-!
# Pair: typing and safety

The program is in `PairProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Pair

/-! ## The typing -/

/-- A page of plain bytes. -/
abbrev words : Shape := .raw 4096

/-- `two` takes nothing and uses one stack slot. Whatever pair of addresses
`x` it returns in `rax` and `rdx`, it hands its caller a page of plain bytes at
each. -/
def twoSig : FnSigEx (BitVec 64 × BitVec 64) where
  args := fun _ => .int
  preserved := calleeSaved
  need := 8
  results := fun x r => if r = .rax then .eq x.1 else if r = .rdx then .eq x.2 else .int
  gives := fun x => [(x.1, words), (x.2, words)]

/-- Back from the call with the pair `x` in `rax` and `rdx`: the pages at
both addresses are the program's. -/
def backCtx (x : BitVec 64 × BitVec 64) : Ctx :=
  ⟨fun r => if r = .rax then .eq x.1 else if r = .rdx then .eq x.2 else .int, [], 16, Flags.Any,
    [(x.1, words), (x.2, words)], 0⟩

/-- The contexts allowed at each label. The return point `back` allows one
for every pair of addresses; `fail` can be reached from anywhere. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 2)
  | back (x : BitVec 64 × BitVec 64) : At .back (backCtx x)
  | two (saved : Reg → Ty) (ret : BitVec 64 × BitVec 64 → Ctx) (rest : List Shape) (room : Nat)
      (frame : List (BitVec 64 × Shape)) (above : Nat) :
    twoSig.CallerOk saved ret rest room frame above →
    At .two (twoSig.entry saved ret rest room frame above)
  | fail (Γ : Ctx) : At .fail Γ

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- No memory blocks: the pages are the program's own. -/
def blocks : List (BitVec 64 × Layout) := []

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea r12, [rip + two]: `r12` holds exactly the function's address
    ty_step
    -- so it is a pointer to the function, and the call is through it
    ty_fn_ptr .r12 to twoSig
    ty_call twoSig returning backCtx
  | back x =>
    -- each store gives a first word the type of the other page's address;
    -- each load finds it, and the second leads back to the first page
    ty_steps
    ty_munmap
    ty_steps
    ty_munmap
    ty_block
  | two saved ret rest room frame above hK =>
    -- the caller left a slot for the page kept across the second request
    obtain ⟨m, rfl⟩ := hK.room_split
    ty_steps
    ty_mmap_own as p
    · ty_block
    · ty_step
      ty_branch
      -- push rax, and the second request
      ty_steps
      ty_mmap_own as q
      · ty_block
      · ty_step
        ty_branch
        -- mov rdx, rax; pop rax
        ty_step
        ty_step
        -- the pair the function returns with, its pages in that order
        ty_return_as (p, q)
        ty_own_first .rax
        ty_block
  | fail Γ => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory and two writable stack slots below `rsp`. Nothing is asked
of how its requests for memory are answered. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry parts blocks 2 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, wherever the kernel puts
the pages, the program is safe on the machine that fetches instructions by
decoding memory.** It never gets stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe however its requests for memory are answered. -/
theorem safeMem (place : Nat → Option (BitVec 64)) : SafeMem linux (startWith place) :=
  safeMem_of_entry (start_entry.withWorld _)

end Pair

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Pair.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pair.safeMem
