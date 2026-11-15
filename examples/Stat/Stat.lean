import StatProgram
import TypedAsm.Tactic

/-!
# Stat: typing and safety

The program is in `StatProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Stat

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | fail : At .fail (entryCtx 0)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- The buffer: eighteen integer fields, 144 bytes, writable. That is the
size of what `fstat` stores, the largest of the three things stored here. -/
def bufferLayout : Layout := ⟨List.replicate 18 .int, true, none, 0⟩

/-- One memory block, the buffer. The file's name before it needs no type. -/
def blocks : List (BitVec 64 × Layout) := [(bufferAt, bufferLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- the arguments and the `openat`, then the test of what it answered
    ty_steps
    ty_branch
    -- mov r12, rax; lea r13, [rip + buffer]
    ty_step
    ty_step
    -- `r13` holds exactly the buffer's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .r13) (base := bufferAt) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    -- the rest: each call that stores into the buffer finds room for what it stores
    ty_block
  | fail => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, and its data readable and writable. Nothing is asked of
the files there are, of the time, or of what the random bytes are. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase dataBytes blocks 0 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, whatever the outside world
is like, the program is safe on the machine that fetches instructions by
decoding memory.** It never gets stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.fieldsInt (by simp [blocks, bufferLayout]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe whatever files it is given. -/
theorem safeMem (files : List File) : SafeMem linux (startWith files) :=
  safeMem_of_entry (start_entry.withWorld _)

end Stat
