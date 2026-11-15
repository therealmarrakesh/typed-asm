import DispatchProgram
import TypedAsm.Tactic

/-!
# Dispatch: typing and safety

The program is in `DispatchProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Dispatch

/-! ## The typing -/

/-- Both functions take an integer in `rdi`, return one in `rax`, use no
stack, and preserve the callee-saved registers. -/
def unary : FnSig where
  args := fun _ => .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- A pointer to the table: two pointers to functions of that kind. -/
def tablePtr : Ty := .ptr [unary.ty, unary.ty] false 0

/-- After the first call: `rbx` still points to the table. -/
def withTable : Ctx := ⟨fun r => if r = .rbx then tablePtr else .int, [], 1, Flags.Any, []⟩

/-- After the later calls: `r12` also still holds a function pointer. -/
def withFn : Ctx :=
  ⟨fun r => if r = .rbx then tablePtr else if r = .r12 then unary.ty else .int, [], 1, Flags.Any, []⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | afterFirst : At .afterFirst withTable
  | afterSecond : At .afterSecond withFn
  | afterThird : At .afterThird withFn
  | bad : At .bad (entryCtx 1)
  | double (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    unary.CallerOk saved ret rest room → At .double (unary.entry saved ret rest room)
  | square (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    unary.CallerOk saved ret rest room → At .square (unary.entry saved ret rest room)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

def tableLayout : Layout := ⟨[unary.ty, unary.ty], false, none, 0⟩

/-- One memory block: the table. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, tableLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rbx, [rip + table]
    ty_step
    -- `rbx` holds exactly the table's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .rbx) (base := dataBase) (i := 0) (w := false) (by decide) rfl rfl
      (by decide) (fun h => absurd h (by decide)) ?_
    -- the index is checked, then the call goes through the table
    ty_block
    ty_call unary
  | afterFirst =>
    -- a function pointer is loaded from the table into `r12` and called
    ty_steps
    ty_call unary
  | afterSecond =>
    -- `r12` was preserved by the call, and is still a function pointer
    ty_steps
    ty_call unary
  | afterThird => ty_block
  | bad => ty_block
  | double saved ret rest room hK => ty_block
  | square saved ret rest room hK => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, the table in readable memory, and one writable stack slot. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase tableBytes blocks 1 0

/-- Any state meeting the entry contract is well typed. The table's entries
are function pointers because the data holds the addresses of two
functions, and those functions are well typed. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s :=
  ⟨entryCtx 1, by rw [h.rip]; exact .intro At.start, fun n => h.matches HasTy.int (by
    intro x hx i τ hi
    simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    match i, hi with
    | 0, hi =>
      cases hi
      have e : word64 tableBytes (8 * 0) = Asm.addr code base .double := by decide +kernel
      rw [h.data.load64 (i := 8 * 0) (by decide), e]
      exact blocksOk.hasTy_fn (FnSig.at_label At.double) n
    | 1, hi =>
      cases hi
      have e : word64 tableBytes (8 * 1) = Asm.addr code base .square := by decide +kernel
      rw [h.data.load64 (i := 8 * 1) (by decide), e]
      exact blocksOk.hasTy_fn (FnSig.at_label At.square) n
    | i + 2, hi => simp [tableLayout] at hi)⟩

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck
and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk h.stateOk)

theorem image_length : image.length = 77 := by decide +kernel

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start :=
  Entry.ofLoad (by rw [image_length]; decide) (by decide)
    ((State.hasData_loadData _ _ _ _ (by decide)).congr rfl) (by rw [image_length]; decide)
    (by decide) (by decide) (by decide)
    (by simp only [image_length]; decide) (by rw [image_length]; decide)

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

end Dispatch
