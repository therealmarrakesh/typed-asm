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
def tablePtr : Ty := .ptr ⟨16, [(0, unary.ty), (8, unary.ty)]⟩ false 0

/-- After the first call: `rbx` still points to the table. -/
def withTable : Ctx := ⟨fun r => if r = .rbx then tablePtr else .int, [], 8, Flags.Any, [], 0⟩

/-- After the later calls: `r12` also still holds a function pointer. -/
def withFn : Ctx :=
  ⟨fun r => if r = .rbx then tablePtr else if r = .r12 then unary.ty else .int, [], 8, Flags.Any, [], 0⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | afterFirst : At .afterFirst withTable
  | afterSecond : At .afterSecond withFn
  | afterThird : At .afterThird withFn
  | bad : At .bad (entryCtx 1)
  | double (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    unary.CallerOk saved ret rest room → At .double (unary.entry saved ret rest room)
  | square (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    unary.CallerOk saved ret rest room → At .square (unary.entry saved ret rest room)

def tableLayout : Layout := ⟨⟨16, [(0, unary.ty), (8, unary.ty)]⟩, false, none, 0⟩

/-- One memory block: the table. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, tableLayout)]

asm_typing At blocks blocks room 1

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

/-- The data has the types the blocks claim. The table's entries are
function pointers because the data holds the addresses of two functions,
and those functions are well typed. -/
theorem Entry.valuesOk {s : State} (h : Entry s) (n : Nat) :
    ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy fetch linux Ψ n p.2 (s.load64 (x.1 + BitVec.ofNat 64 p.1)) := by
  intro x hx p hp
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  simp only [tableLayout, List.mem_cons, List.not_mem_nil, or_false] at hp
  have hd : s.HasData dataBase tableBytes := h.hasData (by decide +kernel)
  rcases hp with rfl | rfl
  · have e : word64 tableBytes 0 = Asm.addr code base .double := by decide +kernel
    rw [hd.load64 (i := 0) (by decide), e]
    exact blocksOk.hasTy_fn (FnSig.at_label At.double) n
  · have e : word64 tableBytes 8 = Asm.addr code base .square := by decide +kernel
    rw [hd.load64 (i := 8) (by decide), e]
    exact blocksOk.hasTy_fn (FnSig.at_label At.square) n

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck
and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start h.valuesOk

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

end Dispatch

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Dispatch.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dispatch.safeMem
