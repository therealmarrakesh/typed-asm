import Rejected.Common

/-!
# Rejections, part 7

See `Rejected.lean`. The tests are spread over the parts so that they are
checked side by side; which part a test is in means nothing.
-/

open TypedAsm

namespace Rejected

/-- error: at address 3: cannot type `mov rax, qword ptr [rdi+16]` in the current context
• loadField: no typed value of the block starts at that offset
• loadInt: the access would reach past the end of the block. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i1) Γ := by ty_step

/-- error: at address 24: cannot type `mov rsp, rax` in the current context
• movRR64: `rsp` cannot be this operand -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i8) Γ := by ty_step

/-- error: at address 27: cannot type `mov qword ptr [rdx+8], rdi` in the current context
• storeField: a value of type `pointer to 16 bytes` cannot be stored where `read-only pointer to 8 bytes` is required. The memory would no longer hold what its type says, and a later use of the value there could fault
• storeInt: a typed value of the block reaches into those bytes, and plain bytes may not be stored over it. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i9) Γ := by ty_step

/-- error: at address 49: cannot type `not qword ptr [rdx+8]` in the current context
• notRM: a typed value of the block reaches into those bytes, and plain bytes may not be stored over it. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i16) Γ := by ty_step

/-! ### Handing over a piece of the stack -/

/-- error: ty_stack_detach: the stack pointer's value must be known here (name it with `ty_name .rsp as sp`), and a piece of the stack must begin at that byte -/
#guard_msgs in
example (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : plain.CallerOk saved ret rest room) :
    BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) (plain.entry saved ret rest room) := by
  ty_stack_detach at 8

/-- error: at address 0: cannot type `mov rsi, qword ptr [rsp+rax*8+8]` in the current context
• loadStackIndexed: those bytes are not known to be inside one piece of the stack. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φy argFetch linux Ψ (Asm.addr argLoads 0 .unknown) (argsCtx 0 2) := by ty_block

/-- error: at address 9: cannot type `mov byte ptr [rdi], al` in the current context
• store8RM: `rdi` must hold a writable pointer, but its type is `pointer into text`. Used as an address, an arbitrary number is a general-protection fault where the processor has no such address, and a page fault where there is no memory for it -/
#guard_msgs in
example : BlockOk Φy textFetch linux Ψ (Asm.addr texts 0 .store) atText := by ty_block

/-- error: at address 25: cannot type `mov rdx, qword ptr [rax]` in the current context
• loadField: `rax` must hold a pointer, but its type is `pointer to 16 bytes or an error number`: it must be tested for an error first, and `ty_err` then gives the two cases. An error number used as an address is in the kernel's half: a page fault -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .unchecked) bare := by
  ty_steps
  ty_mmap (.raw 16)
  ty_block

/-- error: ty_join: the register must hold exactly the address of a block the context owns, and the context must own the block that starts where that one ends -/
#guard_msgs in
example : BlockOk Φm ownFetch linux Ψ (Asm.addr owning 0 .afterFree) bare := by
  ty_steps
  ty_mmap_own as p
  · ty_block
  · ty_step
    ty_branch
    ty_step
    ty_join .rbx
    ty_block

/--
error: ty_split: could not show
  4097 ≤ 4096
-/
#guard_msgs in
example : BlockOk Φm ownFetch linux Ψ (Asm.addr owning 0 .afterFree) bare := by
  ty_steps
  ty_mmap_own as p
  · ty_block
  · ty_step
    ty_branch
    ty_step
    ty_split .rbx at 4097
    ty_block

/-- error: `ret`: the blocks owned here are not the ones the function gives back, followed by the caller's own; a function must hand back what its signature says and dispose of anything else it took -/
#guard_msgs in
example (saved : Reg → Ty) (ret : BitVec 64 → Ctx) (rest : List Shape) (room : Nat)
    (frame : List (BitVec 64 × Shape)) (above : Nat) (hK : makeSig.CallerOk saved ret rest room frame above) :
    BlockOk Φk makingFetch linux Ψ (Asm.addr making 0 .make)
      (makeSig.entry saved ret rest room frame above) := by
  ty_name .rax as v
  ty_return_as v
  ty_block

example : ∃ Γ', Straight Ψ 10 Γ₃ (.store16 (.sib (some .rsp) none 2) .rax) Γ' :=
  ⟨_, by ty_straight⟩

example (i : BitVec 64) (h : BlockOk Φ fetch linux Ψ 0 (frame i [.raw 104])) :
    BlockOk Φ fetch linux Ψ 0 (frame i [.raw 100, .raw 4]) := by
  ty_stack_join at 100
  exact h.asTable

/-- error: cannot type `mov rax, qword ptr [rsp+96]` in the current context
• loadStack: no typed value of that piece of the stack starts at that offset
• loadInt: the access would reach past the end of the piece of the stack it starts in. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (i : BitVec 64) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.mov .w64 (.r_m .rax (.sib (some .rsp) none 96))) Γ' :=
  ⟨_, by ty_straight⟩

-- A `push` there is a stack fault: the processor has no such address, and
-- the access is through the stack.
#guard match exec linux (.push .rax) nowhere with
  | .fault .stackFault => true
  | _ => false

end Rejected
