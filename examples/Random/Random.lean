import RandomProgram
import TypedAsm.Tactic

/-!
# Random: typing and safety

The program is in `RandomProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the
tactics.
-/

open TypedAsm

namespace Random

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and the program uses no stack. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | fail : At .fail (entryCtx 0)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- The buffer: 512 plain bytes, writable. -/
def bufferLayout : Layout := ⟨.raw 512, true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, bufferLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + buffer]
    ty_step
    -- `rdi` holds exactly the buffer's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .rdi) (base := dataBase) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    -- the `getrandom`, the test of its result, the `write` of that many bytes, and `exit`
    ty_block
  | fail => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, and the buffer readable and writable. Nothing is asked of
the kernel: this holds whatever it does with the call for randomness. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry parts blocks 0 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, and whatever the kernel
answers, the program is safe on the machine that fetches instructions by
decoding memory.** It never gets stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks, bufferLayout]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- So does that state whatever the kernel is set to do. -/
theorem startWith_entry (fates : List Fate) (random : Nat → Byte) :
    Entry (startWith fates random) :=
  start_entry.withWorld _

/-- The simulator's run is safe whatever the kernel does: deliver
everything, stop early, or refuse. -/
theorem safeMem (fates : List Fate) (random : Nat → Byte) :
    SafeMem linux (startWith fates random) :=
  safeMem_of_entry (startWith_entry fates random)

end Random

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Random.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Random.safeMem
