import DispatchProgram
import TypedAsm.Tactic

/-!
# Dispatch: typing and safety

The program is in `DispatchProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Dispatch

-- Where the table is loaded.
asm_label dataBase .table

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
  | double (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    unary.CallerOk saved ret rest room → At .double (unary.entry saved ret rest room)
  | square (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    unary.CallerOk saved ret rest room → At .square (unary.entry saved ret rest room)

def tableLayout : Layout := ⟨⟨16, [(0, unary.ty), (8, unary.ty)]⟩, false, none, 0⟩

/-- One memory block: the table. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, tableLayout)]

asm_typing At blocks blocks

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program
  case start =>
    -- lea rbx, [rip + table]
    -- the index is checked, then the call goes through the table
    ty_block
    ty_call unary
  case afterFirst =>
    -- a function pointer is loaded from the table into `r12` and called
    ty_steps
    ty_call unary
  case afterSecond =>
    -- `r12` was preserved by the call, and is still a function pointer
    ty_steps
    ty_call unary

/-! ## Safety -/

-- The table holds the addresses of `double` and `square`, which are function
-- pointers because those functions are typed: read from the program's bytes.
asm_safety At.start

end Dispatch
