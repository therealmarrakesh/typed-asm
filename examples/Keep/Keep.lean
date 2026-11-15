import KeepProgram
import TypedAsm.Tactic

/-!
# Keep: typing and safety

The program is in `KeepProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Keep

/-! ## The typing -/

/-- `pause` preserves the callee-saved registers and also the stack pointer:
when it has returned, `rsp` is where it was before the call. -/
def pauseSig : FnSig where
  args := fun _ => .int
  results := fun _ => .int
  preserved := fun r => calleeSaved r || r == .rsp
  need := 0

/-- Back from the call: the stack pointer is exactly `sp`, as before it,
and `rbx` holds the address of the buffer, which is where `rsp` points. -/
def kept (sp : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rsp then .eq sp else if r = .rbx then .eq sp else .int, [.int, .int], 1, Flags.Any, []⟩

/-- Nothing is known about any register; the buffer is still allocated. -/
def ending : Ctx := ⟨fun _ => .int, [.int, .int], 1, Flags.Any, []⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 3)
  | back (sp : BitVec 64) : At .back (kept sp)
  | done : At .done ending
  | pause (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    pauseSig.CallerOk saved ret rest room → At .pause (pauseSig.entry saved ret rest room)

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
    -- the stack pointer's value is called `sp`; `lea rbx, [rsp]` is then known
    ty_name .rsp as sp
    ty_step
    ty_call pauseSig
  | back sp =>
    -- the `read` is into the address taken before the call
    ty_block
  | done => ty_block
  | pause saved ret rest room hK => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory and three writable stack slots below `rsp`. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase [] blocks 3 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, and whatever it is given to
read, the program is safe on the machine that fetches instructions by
decoding memory.** It never gets stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.fieldsInt (by simp [blocks]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe whatever input it is given. -/
theorem safeMem (input : List ReadEvent) : SafeMem linux (startWith input) :=
  safeMem_of_entry (start_entry.withWorld _)

end Keep
