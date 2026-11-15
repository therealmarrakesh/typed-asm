import EchoProgram
import TypedAsm.Tactic

/-!
# Echo: typing and safety

The program is in `EchoProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Echo

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and the program uses no stack. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | done : At .done (entryCtx 0)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- The buffer: two integer fields, sixteen bytes, writable. -/
def bufferLayout : Layout := ⟨[.int, .int], true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, bufferLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- xor eax, eax; xor edi, edi; lea rsi, [rip + buffer]
    ty_step
    ty_step
    ty_step
    -- `rsi` holds exactly the buffer's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .rsi) (base := dataBase) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    -- the `read`, the test of its result, the `write`, and round again
    ty_block
  | done => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, and the buffer readable and writable. Nothing is asked of
the input: this holds whatever there is to read. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase bufferBytes blocks 0 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, and whatever it is given to
read, the program is safe on the machine that fetches instructions by
decoding memory.** It never gets stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.fieldsInt (by simp [blocks, bufferLayout]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- So does that state with any input waiting. -/
theorem startWith_entry (input : List ReadEvent) : Entry (startWith input) :=
  start_entry.withWorld _

/-- The simulator's run is safe whatever input it is given. -/
theorem safeMem (input : List ReadEvent) : SafeMem linux (startWith input) :=
  safeMem_of_entry (startWith_entry input)

end Echo

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Echo.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Echo.safeMem
