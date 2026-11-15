import IndexProgram
import TypedAsm.Tactic

/-!
# Index: typing and safety

The program is in `IndexProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Index

/-! ## The typing -/

/-- A pointer to a read-only array of `n` integers. -/
def arr (n : Nat) : Ty := .ptr (.raw (8 * n)) false 0

/-- `get` takes the array in `rdi`, exactly its length in `rsi`, and any
integer at all as the index in `rdx`. -/
def getSig (n : Nat) : FnSig where
  args := fun r =>
    if r = .rdi then arr n else if r = .rsi then .eq (BitVec.ofNat 64 n) else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- Nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 8, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | afterCall : At .afterCall fin
  | get (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (getSig n).CallerOk saved ret rest room → n < 2 ^ 64 →
    At .get ((getSig n).entry saved ret rest room)
  /-- Reached only with the index, here called `v`, below the length. -/
  | inbounds (n : Nat) (v : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape)
      (room : Nat) :
    (getSig n).CallerOk saved ret rest room → v.toNat < n →
    At .inbounds ⟨fun r => if calleeSaved r then saved r
        else if r = .rdi then arr n else if r = .rdx then .eq v else .int,
      .slot (.code ret) :: rest, room, Flags.Any, ret.owned, ret.above⟩

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

def arrayLayout : Layout := ⟨.raw 40, false, none, 0⟩

/-- One memory block: the array. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, arrayLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + array]
    ty_step
    -- `rdi` holds exactly the array's address, so it is a pointer to its first element
    refine BlockOk.castPtr (r := .rdi) (base := dataBase) (i := 0) (w := false) (by decide) rfl rfl
      (by decide) (fun h => absurd h (by decide)) ?_
    ty_steps
    ty_call (getSig 5)
  | afterCall => ty_block
  | get n saved ret rest room hK hn =>
    -- the index is any integer; call it `v`
    ty_name .rdx as v
    -- entering `inbounds`, the comparison has found `v` below the length
    ty_block
  | inbounds n v saved ret rest room hK hv => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, the array readable, and one writable stack slot below `rsp` that
does not overlap it. This is the contract with whatever loads the program;
for the ELF file, with the Linux kernel. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry parts blocks 1 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck,
never faults: no page fault, no invalid opcode and no divide error. In particular the
indexed load never reads outside the array, whatever index `get` is given. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks, arrayLayout]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

/-- It is also safe on the table machine, which is what the type system reasons about. -/
theorem safe : Safe fetch linux start :=
  start_entry.safe blocksOk memOk At.start (Entry.plain (by simp [blocks, arrayLayout]))

end Index

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Index.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Index.safeMem
