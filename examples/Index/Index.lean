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
def arr (n : Nat) : Ty := .ptr (List.replicate n .int) false 0

/-- `get` takes the array in `rdi`, exactly its length in `rsi`, and any
integer at all as the index in `rdx`. -/
def getSig (n : Nat) : FnSig where
  args := fun r =>
    if r = .rdi then arr n else if r = .rsi then .eq (BitVec.ofNat 64 n) else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- Nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 1, Flags.Any⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | afterCall : At .afterCall fin
  | get (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (getSig n).CallerOk saved ret rest room → n < 2 ^ 64 →
    At .get ((getSig n).entry saved ret rest room)
  /-- Reached only with the index, here called `v`, below the length. -/
  | inbounds (n : Nat) (v : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty)
      (room : Nat) :
    (getSig n).CallerOk saved ret rest room → v.toNat < n →
    At .inbounds ⟨fun r => if calleeSaved r then saved r
        else if r = .rdi then arr n else if r = .rdx then .eq v else .int,
      .code ret :: rest, room, Flags.Any⟩

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

def arrayLayout : Layout := ⟨List.replicate 5 .int, false⟩

/-- One memory block: the array. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, arrayLayout)]

def Ψ : MemTy := .ofList blocks

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
    ty_block
    -- entering `inbounds`: the comparison found `v` below the length
    have hlt := cmp_below hcond
    simpa [Nat.mod_eq_of_lt hn] using hlt
  | inbounds n v saved ret rest room hK hv => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, the array readable, and one writable stack slot below `rsp` that
does not overlap it. This is the contract with whatever loads the program;
for the ELF file, with the Linux kernel. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase arrayBytes blocks 1

/-- Any state meeting the entry contract is well typed. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s :=
  ⟨entryCtx 1, by rw [h.rip]; exact .intro At.start,
    fun _ => h.matchesInt HasTy.int (by simp [blocks, arrayLayout])⟩

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck,
never faults: no page fault, no invalid opcode and no divide error. In particular the
indexed load never reads outside the array, whatever index `get` is given. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk h.stateOk)

theorem image_length : image.length = 48 := by decide

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start :=
  Entry.ofLoad (by rw [image_length]; decide) (by decide)
    ((State.hasData_loadData _ _ _ _ (by decide)).congr rfl) (by rw [image_length]; decide)
    (by decide) (by decide) (by decide)
    (by simp only [image_length]; decide) (by rw [image_length]; decide)

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

/-- It is also safe on the table machine, which is what the type system reasons about. -/
theorem safe : Safe fetch linux start :=
  soundness_blocks blocksOk memOk start_entry.stateOk

end Index
