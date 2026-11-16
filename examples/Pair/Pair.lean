import PairProgram
import TypedAsm.Tactic

/-!
# Pair: typing and safety

The program is in `PairProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Pair

/-! ## The typing -/

/-- A page of plain bytes. -/
abbrev words : Shape := .raw 4096

/-- `two` takes nothing and uses one stack slot. Whatever pair of addresses
`x` it returns in `rax` and `rdx`, it hands its caller a page of plain bytes at
each. -/
def twoSig : FnSigEx (BitVec 64 × BitVec 64) where
  args := fun _ => .int
  preserved := calleeSaved
  need := 8
  results := fun x r => if r = .rax then .eq x.1 else if r = .rdx then .eq x.2 else .int
  gives := fun x => [(x.1, words), (x.2, words)]

/-- Back from the call with the pair `x` in `rax` and `rdx`: the pages at
both addresses are the program's. -/
def backCtx (x : BitVec 64 × BitVec 64) : Ctx :=
  ⟨fun r => if r = .rax then .eq x.1 else if r = .rdx then .eq x.2 else .int, [], 16, Flags.Any,
    [(x.1, words), (x.2, words)], 0⟩

/-- The contexts allowed at each label. The return point `back` allows one
for every pair of addresses; `fail` can be reached from anywhere. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 2)
  | back (x : BitVec 64 × BitVec 64) : At .back (backCtx x)
  | two (saved : Reg → Ty) (ret : BitVec 64 × BitVec 64 → Ctx) (rest : List Shape) (room : Nat)
      (frame : List (BitVec 64 × Shape)) (above : Nat) :
    twoSig.CallerOk saved ret rest room frame above →
    At .two (twoSig.entry saved ret rest room frame above)

/-- No memory blocks: the pages are the program's own. -/
def blocks : List (BitVec 64 × Layout) := []

asm_typing At blocks blocks room 2

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program
  case start =>
    -- lea r12, [rip + two]: `r12` holds exactly the function's address
    ty_step
    -- so it is a pointer to the function, and the call is through it
    ty_fn_ptr .r12 to twoSig
    ty_call twoSig returning backCtx
  case back x =>
    -- each store gives a first word the type of the other page's address;
    -- each load finds it, and the second leads back to the first page
    ty_steps
    ty_munmap
    ty_steps
    ty_munmap
    ty_block
  case two saved ret rest room frame above hK =>
    -- the caller left a slot for the page kept across the second request
    obtain ⟨m, rfl⟩ := hK.room_split
    ty_steps
    ty_mmap_own as p
    · ty_block
    · ty_step
      ty_branch
      -- push rax, and the second request
      ty_steps
      ty_mmap_own as q
      · ty_block
      · ty_step
        ty_branch
        -- mov rdx, rax; pop rax
        ty_step
        ty_step
        -- the pair the function returns with, its pages in that order
        ty_return_as (p, q)
        ty_own_first .rax
        ty_block

/-! ## Safety -/

asm_safety At.start

end Pair

