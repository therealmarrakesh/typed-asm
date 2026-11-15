import FreshProgram
import TypedAsm.Tactic

/-!
# Fresh: typing and safety

The program is in `FreshProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the
tactics.
-/

open TypedAsm

namespace Fresh

/-! ## The typing -/

/-- A page of plain bytes. -/
abbrev words : Shape := .raw 4096

/-- `page` takes nothing and uses no stack. Whatever address `x` it returns
in `rax`, it hands its caller a page of plain bytes there. -/
def pageSig : FnSigEx (BitVec 64) where
  args := fun _ => .int
  preserved := calleeSaved
  need := 0
  results := fun x r => if r = .rax then .eq x else .int
  gives := fun x => [(x, words)]

/-- Back from the call with `x` in `rax`: the page at `x` is the program's. -/
def backCtx (x : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rax then .eq x else .int, [], 8, Flags.Any, [(x, words)]⟩

/-- In the loop: `rbx` holds the page's address, and the page is all numbers. -/
def loopCtx (p : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .eq p else .int, [], 8, Flags.Any, [(p, words)]⟩

/-- The contexts allowed at each label. The return point `back` allows one
for every address the page could be at; `fail` can be reached from anywhere. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | back (x : BitVec 64) : At .back (backCtx x)
  | loop (p : BitVec 64) : At .loop (loopCtx p)
  | done (p : BitVec 64) : At .done (loopCtx p)
  | page (saved : Reg → Ty) (ret : BitVec 64 → Ctx) (rest : List Shape) (room : Nat)
      (frame : List (BitVec 64 × Shape)) :
    pageSig.CallerOk saved ret rest room frame →
    At .page (pageSig.entry saved ret rest room frame)
  | fail (Γ : Ctx) : At .fail Γ

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- No memory blocks: the page is the program's own. -/
def blocks : List (BitVec 64 × Layout) := []

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- the instruction after the call is ready for a page at any address
    ty_call pageSig returning backCtx
  | back x =>
    -- the store makes the first word an address; the `read` makes it a number again
    iterate 7 ty_step
    -- xor ecx, ecx, and on into the loop
    ty_into At.loop x
  | loop p =>
    -- the index, whatever it is, is called `i`; past the test it is less than 4096
    ty_name .rcx as i
    ty_block
  | done p =>
    ty_steps
    ty_munmap
    ty_block
  | page saved ret rest room frame hK =>
    ty_steps
    ty_mmap_own as p
    -- an error number is negative: the test sends control to `fail`
    · ty_block
    -- a page at `p`: that is the address the function returns with
    · ty_step
      ty_branch
      ty_return_as p
      ty_block
  | fail Γ => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory and one writable stack slot below `rsp`. Nothing is asked
of the input, or of how the request for memory is answered. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase [] blocks 1 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, whatever it is given to
read and wherever the kernel puts the page, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck
and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe whatever input it is given and however its
request for memory is answered. -/
theorem safeMem (input : List Byte) (place : Nat → Option (BitVec 64)) :
    SafeMem linux (startWith input place) :=
  safeMem_of_entry (start_entry.withWorld _)

end Fresh

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Fresh.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fresh.safeMem
