import DoubleProgram
import TypedAsm.Tactic

/-!
# Double: typing and safety

The program is in `DoubleProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the
tactics.
-/

open TypedAsm

namespace Double

/-! ## The typing -/

/-- A page of plain bytes. -/
abbrev words : Shape := .raw 4096

/-- `double` called with exactly `p` in `rdi` takes the page at `p` and gives
it back, still a page of plain bytes. It uses no stack. -/
def doubleSig (p : BitVec 64) : FnSig where
  args := fun r => if r = .rdi then .eq p else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0
  takes := [(p, words)]
  gives := [(p, words)]

/-- Back from the call: `rbx` still holds the page's address, and the page
is the program's again. -/
def backCtx (p : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .eq p else .int, [], 1, Flags.Any, [(p, words)]⟩

/-- Inside the function: `rdi` holds the page's address, the page is the
function's, and after it come whatever blocks the caller owns besides. -/
def inside (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) : Ctx :=
  ⟨fun r => if r = .rdi then .eq p else if calleeSaved r then saved r else .int,
    .code ret :: rest, room, Flags.Any, (p, words) :: ret.owned.drop 1⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | back (p : BitVec 64) : At .back (backCtx p)
  | fail : At .fail (entryCtx 1)
  | double (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (doubleSig p).CallerOk saved ret rest room →
    At .double ((doubleSig p).entry saved ret rest room)
  | loop (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (doubleSig p).CallerOk saved ret rest room → At .loop (inside p saved ret rest room)
  | done (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (doubleSig p).CallerOk saved ret rest room → At .done (inside p saved ret rest room)

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
    -- the arguments, then the `mmap` for a page to own, at an address called `p`
    ty_steps
    ty_mmap_own as p
    -- an error number is negative: the test sends control to `fail`
    · ty_block
    -- a page: the `read` is into it, and it is handed to `double`
    · ty_step
      ty_branch
      ty_steps
      ty_call (doubleSig p)
  | back p =>
    -- written out, and given back
    ty_steps
    ty_munmap
    ty_block
  | fail => ty_block
  | double p saved ret rest room hK => ty_into At.loop p saved ret rest room hK
  | loop p saved ret rest room hK =>
    -- the index, whatever it is, is called `i`; past the test it is less than 512
    ty_name .rcx as i
    ty_block
  | done p saved ret rest room hK => ty_block

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
and never faults: in particular the function never reaches past the page it
was handed. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.fieldsInt (by simp [blocks]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe whatever input it is given and however its
request for memory is answered. -/
theorem safeMem (input : List Byte) (place : Nat → Option (BitVec 64)) :
    SafeMem linux (startWith input place) :=
  safeMem_of_entry (start_entry.withWorld _)

end Double

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Double.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Double.safeMem
