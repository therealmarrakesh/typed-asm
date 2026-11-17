import Rejected.Common

/-!
# Rejections, part 4

See `Rejected.lean`. The tests are spread over the parts so that they are
checked side by side; which part a test is in means nothing.
-/

open TypedAsm

namespace Rejected

/-- error: at address 17: cannot type `adc rax, rcx` in the current context
• the operation reads the carry flag, which is not known to be defined here. The processor leaves it undefined after some instructions, and the result would then not be determined -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i6) Γ := by ty_step

/-- error: at address 3: cannot type `mov rax, qword ptr [rdi+16]` in the current context
• `rdi` must hold a pointer, but its type is `read-only pointer to 24 bytes or null`: it must be tested for null first, and `ty_null` then gives the two cases. An access through null is a page fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i1) maybe := by ty_step

/-- error: `call rax`: the operand does not hold a pointer to a function with this signature, or there is no room on the stack for the return address. A register holding the exact address of a function becomes a pointer to it with `ty_fn_ptr` -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .indirect) roomy := by ty_call plain

/-- error: at address 12: cannot type `jo 8` in the current context
• the flags known here do not decide the condition. The processor leaves some flags undefined after some instructions, and which way this goes would then not be determined
the flags were last set by `shl ecx, 3` at address 9 -/
#guard_msgs in
example : BlockOk Φf flaggedFetch linux Ψ (Asm.addr flagged 0 .overflow) bare := by ty_block

/-- error: `read` could overwrite something that is not plain bytes: the buffer in `rsi` does not have room for the count in `rdx` in plain bytes of its block
`rdx` was given its type by `mov edx, 17` at address 20 -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .tooLong) (buffer (.raw 16)) := by
  ty_block

/-- error: at address 4: cannot type `movzx eax, byte ptr [rdi]` in the current context
• `rdi` must hold a pointer, but its type is `int`. Used as an address, an arbitrary number is a general-protection fault where the processor has no such address, and a page fault where there is no memory for it
`rdi` was given its type by `add rdi, 1` at address 0 -/
#guard_msgs in
example : BlockOk Φy textFetch linux Ψ (Asm.addr texts 0 .onward) atText := by ty_block

/-- error: `mmap`: every typed value of the new block must admit zero, since that is what fresh memory holds: a value that may be null -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .notZero) bare := by
  ty_steps
  ty_mmap ⟨16, [(8, .ptr (.raw 8) true 0)]⟩

/-- error: at address 13: cannot type `mov rax, qword ptr [rdi+rcx*8]` in the current context
• the bytes are not known to be inside the block: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : (pageSig p).CallerOk saved ret rest room) :
    BlockOk Φh handedFetch linux Ψ (Asm.addr handed 0 .reaches)
      ((pageSig p).entry saved ret rest room) := by
  ty_name .rcx as i
  ty_block

example : ∃ Γ', Straight Ψ 10 Γ₃ (.mov .w32 (.rm_r (.mem (.sib (some .rsp) none 4)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: cannot type `mov byte ptr [rbx+rcx*1+16], al` in the current context
• the bytes are not known to be inside the block: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (i : BitVec 64) (hlt : i.toNat < 65) :
    Straight Ψ 10 (filling i) (.store8 (.sib (some .rbx) (some (.rcx, .s1)) 16) .rax)
      (filling i) := by
  ty_straight

/-- error: cannot type `mov byte ptr [rbx+8], al` in the current context
• the bytes are not known to be clear of the typed values the block holds. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example (n k : Nat) (hk : k < n) :
    Straight Ψ 10 (walking n k) (.store8 (.sib (some .rbx) none 8) .rax) (walking n k) := by
  ty_straight

/-! An array of `n` pointers, reached through an index known only to be
below `n`. -/

example (n : Nat) (i : BitVec 64) (hi : i.toNat < n) :
    Straight Ψ 10
      ⟨fun r => if r = .rsi then .ptr ((ShapeOf.mk 8 [(0, .ptr (.raw 16) true 0)]).rep n) false 0
        else if r = .rcx then .eq i else .int, [], 0, Flags.Any, [], 0⟩
      (.mov .w64 (.r_m .rax (.sib (some .rsi) (some (.rcx, .s8)) 0)))
      ((⟨fun r => if r = .rsi then .ptr ((ShapeOf.mk 8 [(0, .ptr (.raw 16) true 0)]).rep n) false 0
        else if r = .rcx then .eq i else .int, [], 0, Flags.Any, [], 0⟩ : Ctx).setReg .rax
          (.ptr (.raw 16) true 0)) := by
  ty_straight

/-- No entry contract is met by a state whose stack pointer is at such an
address, whatever the program and however the state was made. -/
example (entry : BitVec 64) (parts : List (Nat × Perm × List Byte))
    (blocks : List (BitVec 64 × Layout)) (s : State)
    (hsp : s.getReg .rsp = 0x0200000000000000) : ¬ Entry entry parts blocks 11 0 s := by
  intro h
  have := h.stack_top (by decide)
  rw [hsp] at this
  exact absurd this (by decide)

/-- The page is writable to its last byte, and the next one is not. -/
example : sixteen.canWrite 0x10ff8 8 = true ∧ sixteen.canWrite 0x11000 1 = false := by
  decide

end Rejected
