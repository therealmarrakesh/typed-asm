import TypedAsm.Tactic
import LendProgram

/-!
# The typing of the program that hands a function a pointer to a local

See `LendProgram.lean` for the program. Its safety theorem is at the end.
-/

open TypedAsm

namespace Lend

/-! ## Signatures and contexts -/

/-- `fill` called with exactly `p` in `rdi` takes the sixteen bytes at `p`
and gives them back. It uses no stack, and leaves the stack pointer where it
found it. -/
def fillSig (p : BitVec 64) : FnSig where
  args := fun r => if r = .rdi then .eq p else .int
  results := fun _ => .int
  preserved := fun r => calleeSaved r || r == .rsp
  need := 0
  takes := [(p, .raw 16)]
  gives := [(p, .raw 16)]

/-- `work` uses twenty-four bytes of stack below its return address: its
local, and the return address of its call. It leaves a number in `rax`. -/
def workSig : FnSig where
  args := fun _ => .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 24

/-- Back from `work`. -/
def fin : Ctx := ⟨fun _ => .int, [], 32, Flags.Any, [], 0⟩

/-- In `work` with its local allocated and the stack pointer's value known
to be `sp`: sixteen bytes, then the return address, then the caller's part
of the stack. -/
def framed (sp : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (m : Nat) : Ctx :=
  ⟨fun r => if r = .rsp then .eq sp else if calleeSaved r then saved r else .int,
    .raw 16 :: .slot (.code ret) :: rest, m + 8, Flags.Any, ret.owned, ret.above⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 4)
  | done : At .done fin
  | work (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    workSig.CallerOk saved ret rest room → At .work (workSig.entry saved ret rest room)
  /-- Back from `fill`: the whole stack is still detached, the local first. -/
  | filled (sp : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (m : Nat) :
    workSig.CallerOk saved ret rest (m + 24) → At .filled ((framed sp saved ret rest m).detach sp 0)
  | fill (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (fillSig p).CallerOk saved ret rest room → At .fill ((fillSig p).entry saved ret rest room)

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
  | start => ty_call workSig
  | done => ty_block
  | work saved ret rest room hK =>
    -- make the room the signature guarantees visible, so the local can be allocated
    obtain ⟨m, rfl⟩ := hK.room_split
    -- sub rsp, 16
    ty_step
    -- the stack pointer's value is called `sp`; `lea rdi, [rsp]` is then the local's address
    ty_name .rsp as sp
    ty_step
    -- the local, and everything above it, become blocks: the local is handed to `fill`
    ty_stack_detach at 0
    ty_call (fillSig (sp + 0))
  | filled sp saved ret rest m hK =>
    -- everything is attached again: the local is a piece of the stack as before
    ty_stack_attach
    ty_block
  | fill p saved ret rest room hK => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory and four writable stack slots below `rsp`. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry parts blocks 4 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck
and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

end Lend

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Lend.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lend.safeMem
