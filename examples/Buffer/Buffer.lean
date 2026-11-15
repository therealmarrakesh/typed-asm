import BufferProgram
import TypedAsm.Tactic

/-!
# Buffer: typing and safety

The program is in `BufferProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Buffer

/-! ## The typing -/

/-- In the loop the buffer is allocated: two stack slots holding integers. -/
def looping : Ctx := ⟨fun _ => .int, [.int, .int], 0, Flags.Any, []⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 2)
  | loop : At .loop looping
  | done : At .done looping

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- No memory blocks. -/
def blocks : List (BitVec 64 × Layout) := []

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- sub rsp, 16
    ty_step
    -- from here on as in the loop
    ty_name .rsp as sp
    ty_block
  | loop =>
    -- the stack pointer's value is called `sp`, so `lea rsi, [rsp]` yields
    -- a known address and the `read` is checked against the two slots there
    ty_name .rsp as sp
    ty_block
  | done => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory and two writable stack slots below `rsp`. Nothing is asked
of the input. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase [] blocks 2 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, and whatever it is given to
read, the program is safe on the machine that fetches instructions by
decoding memory.** It never gets stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.fieldsInt (by simp [blocks]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- So does that state with any input waiting. -/
theorem startWith_entry (input : List ReadEvent) : Entry (startWith input) :=
  start_entry.withWorld _

/-- The simulator's run is safe whatever input it is given. -/
theorem safeMem (input : List ReadEvent) : SafeMem linux (startWith input) :=
  safeMem_of_entry (startWith_entry input)

end Buffer

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Buffer.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Buffer.safeMem
