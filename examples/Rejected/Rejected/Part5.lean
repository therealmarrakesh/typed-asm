import Rejected.Common

/-!
# Rejections, part 5

See `Rejected.lean`. The tests are spread over the parts so that they are
checked side by side; which part a test is in means nothing.
-/

open TypedAsm

namespace Rejected

/-- error: at address 7: cannot type `mov qword ptr [rsi], rcx` in the current context
• storeField: `rsi` must hold a writable pointer, but its type is `read-only pointer to 16 bytes`. A store to memory that is read-only is a page fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i2) Γ := by ty_step

/-- error: at address 11: cannot type `mov dword ptr [rdx+8], ecx` in the current context
• storeInt: a typed value of the block reaches into those bytes, and plain bytes may not be stored over it. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i4) Γ := by ty_step

/-- error: `ret` can transfer control, so it ends the block and is not typed by `ty_step` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i10) Γ := by ty_step

/-- error: at address 39: cannot type `add dword ptr [rsp+8], eax` in the current context
• aluStoreR: those bytes are not known to be inside one piece of the stack. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i13) Γ := by ty_step

/-- error: at address 45: cannot type `imul eax, dword ptr [rdi+14]` in the current context
• imul2RM: the access would reach past the end of the block. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i15) Γ := by ty_step

/-- error: ty_call: the instruction here is `ret`, not a call -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) bare := by ty_call plain

example : BlockOk Φf flaggedFetch linux Ψ (Asm.addr flagged 0 .carry) bare := by ty_block

/-- error: `read` could overwrite something that is not plain bytes: the buffer in `rsi` does not have room for the count in `rdx` in plain bytes of its block
`rdx` was given its type by `mov edx, 16` at address 29 -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .overPointer)
    (buffer ⟨16, [(8, .ptr (.raw 8) false 0)]⟩) := by
  ty_block

/-- error: `mmap`: the block does not fit in the length in `rsi` -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .tooShort) bare := by
  ty_steps
  ty_mmap (.raw 16)

/-- error: `ret`: the return address here is ready for a family of contexts, one for each value the function may hand back; say which the function returns into with `ty_return_as` -/
#guard_msgs in
example (saved : Reg → Ty) (ret : BitVec 64 → Ctx) (rest : List Shape) (room : Nat)
    (frame : List (BitVec 64 × Shape)) (above : Nat) (hK : makeSig.CallerOk saved ret rest room frame above) :
    BlockOk Φk makingFetch linux Ψ (Asm.addr making 0 .make)
      (makeSig.entry saved ret rest room frame above) := by
  ty_block

/-! A 16-bit store, into a field and into a stack slot. -/

example : ∃ Γ', Straight Ψ 10 Γ₃ (.store16 (.sib (some .rdi) none 6) .rax) Γ' :=
  ⟨_, by ty_straight⟩

example (i : BitVec 64) (h : BlockOk Φ fetch linux Ψ 0 (frame i [.raw 100, .raw 4])) :
    BlockOk Φ fetch linux Ψ 0 (frame i [.raw 104]) := by
  ty_stack_split at 100
  exact h.asTable

example (i : BitVec 64) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.mov .w64 (.r_m .rax (.sib (some .rsp) none 3))) Γ' :=
  ⟨_, by ty_straight⟩

/-- Marking the memory writable changed nothing. -/
example : nowhere.canWrite (0x0200000000000000 - 8) 8 = false := by decide

end Rejected
