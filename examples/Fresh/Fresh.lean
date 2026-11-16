import FreshProgram
import TypedAsm.Tactic

/-!
# Fresh: typing and safety

The program is in `FreshProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the
tactics.
-/

open TypedAsm

namespace Fresh

/-! ## The typing -/

/-- A page of plain bytes. -/
abbrev words : Shape := .raw 4096

/-- `page` takes nothing and uses no stack. Whatever address `x` it returns
in `rax`, it hands its caller a page of plain bytes there. -/
def pageSig : FnSigEx (BitVec 64) where
  args := fun _ => .int
  preserved := calleeSaved
  need := 0
  results := fun x r => if r = .rax then .eq x else .int
  gives := fun x => [(x, words)]

/-- Back from the call with `x` in `rax`: the page at `x` is the program's. -/
def backCtx (x : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rax then .eq x else .int, [], 8, Flags.Any, [(x, words)], 0⟩

/-- In the loop: `rbx` holds the page's address, and the page is all numbers. -/
def loopCtx (p : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .eq p else .int, [], 8, Flags.Any, [(p, words)], 0⟩

/-- The contexts allowed at each label. The return point `back` allows one
for every address the page could be at; `fail` can be reached from anywhere. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | back (x : BitVec 64) : At .back (backCtx x)
  | loop (p : BitVec 64) : At .loop (loopCtx p)
  | done (p : BitVec 64) : At .done (loopCtx p)
  | page (saved : Reg → Ty) (ret : BitVec 64 → Ctx) (rest : List Shape) (room : Nat)
      (frame : List (BitVec 64 × Shape)) (above : Nat) :
    pageSig.CallerOk saved ret rest room frame above →
    At .page (pageSig.entry saved ret rest room frame above)

/-- No memory blocks: the page is the program's own. -/
def blocks : List (BitVec 64 × Layout) := []

asm_typing At blocks blocks room 1

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- the instruction after the call is ready for a page at any address
    ty_call pageSig returning backCtx
  | back x =>
    -- the store makes the first word an address; the `read` makes it a number again
    iterate 7 ty_step
    -- xor ecx, ecx, and on into the loop
    ty_into At.loop x
  | loop p =>
    -- the index, whatever it is, is called `i`; past the test it is less than 4096
    ty_name .rcx as i
    ty_block
  | done p =>
    ty_steps
    ty_munmap
    ty_block
  | page saved ret rest room frame above hK =>
    ty_steps
    ty_mmap_own as p
    -- an error number is negative: the test sends control to `fail`
    · ty_block
    -- a page at `p`: that is the address the function returns with
    · ty_step
      ty_branch
      ty_return_as p
      ty_block

/-! ## Safety -/

asm_safety At.start

end Fresh

