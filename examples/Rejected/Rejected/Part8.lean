import Rejected.Common

/-!
# Rejections, part 8

See `Rejected.lean`. The tests are spread over the parts so that they are
checked side by side; which part a test is in means nothing.
-/

open TypedAsm

namespace Rejected

/-- error: at address 14: cannot type `div rcx` in the current context
• `rdx` must hold an exactly known value for a divide, but its type is `pointer to 16 bytes with read-only pointer to 8 bytes at byte 8`: a divide is typed only when it is known not to raise a divide error -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i5) Γ := by ty_step

/-- error: at address 14: cannot type `div rcx` in the current context
• `rdx`, the upper half of the dividend, is not known to be zero: clear it before the divide. Otherwise the quotient may not fit, which is a divide error -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i5) bare := by ty_step

/-- error: at address 20: cannot type `mov rax, qword ptr [rdi+12]` in the current context
• the access would reach past the end of the block. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i7) Γ := by ty_step

/-- error: at address 32: cannot type `mov rax, qword ptr [rdi+rcx*8]` in the current context
• the bytes are not known to be inside the block: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i11) Γ := by ty_step

/-- error: at address 36: cannot type `cmovg eax, ecx` in the current context
• the flags are not known here, so they do not decide the condition. The processor leaves them undefined after some instructions, and what this one does would then not be determined -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i12) Γ := by ty_step

/-- error: at address 53: cannot type `neg qword ptr [rdi+rcx*8]` in the current context
• the bytes are not known to be inside the block: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i17) Γ := by ty_step

/-- error: ty_stack_attach: the first block the context owns is not one detached from the stack that lies where the stack now ends; the stack pointer's value must be known too -/
#guard_msgs in
example (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : plain.CallerOk saved ret rest room) :
    BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) (plain.entry saved ret rest room) := by
  ty_stack_attach

/-- error: at address 12: cannot type `mov rsi, qword ptr [rsp+rax*8+8]` in the current context
• those bytes are not known to be inside one piece of the stack: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φy argFetch linux Ψ (Asm.addr argLoads 0 .beyond) (argsCtx 0 2) := by ty_block

/-- error: `mmap` is typed only where the kernel chooses the place: `rdi` must hold exactly 0, but its type is `exactly 0x800000000000`. Asked for an address, the kernel may put the memory where it would not of its own accord, such as in the reach of the stack -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .highHint) bare := by
  ty_steps
  ty_mmap (.raw 16)

/-- error: at address 52: cannot type `mov rcx, qword ptr [rbx]` in the current context
• the address is not known to be inside a block the context owns. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed
the blocks owned were last changed by `syscall` at address 50 -/
#guard_msgs in
example : BlockOk Φm ownFetch linux Ψ (Asm.addr owning 0 .afterFree) bare := by
  ty_steps
  ty_mmap_own as p
  · ty_block
  · ty_step
    ty_branch
    ty_steps
    ty_munmap
    ty_block

/--
error: no context allowed at label `done` accepts the current one
• done: the blocks owned do not match: a block taken here must be given back or frozen before control goes there
-/
#guard_msgs in
example : BlockOk Φm ownFetch linux Ψ (Asm.addr owning 0 .leak) bare := by
  ty_steps
  ty_mmap_own as p
  · ty_block
  · ty_step
    ty_branch
    ty_block

/-- error: ty_call: the operand does not hold a pointer to a function with this signature. A register holding the exact address of a function becomes a pointer to it with `ty_fn_ptr` -/
#guard_msgs in
example : BlockOk Φk callingFetch linux Ψ (Asm.addr calling 0 .make) roomy := by
  ty_call makeSig returning fun x => ⟨fun _ => .int, [], 1, Flags.Any, [(x, .raw 4096)], 0⟩

example : ∃ Γ', Straight Ψ 10 Γ₄
    (.mov .w64 (.rm_r (.mem (.sib (some .rdi) (some (.rcx, .s8)) 0)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

example (n k : Nat) (hk : k < n) :
    Straight Ψ 10 (walking n k) (.store8 (.sib (some .rbx) none 16) .rax) (walking n k) := by
  ty_straight

/-- error: at address 4: cannot type `mov rax, qword ptr [rsp+4]` in the current context
• the access would reach past the end of its piece of the stack. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed
the stack was last changed by `sub rsp, 8` at address 0 -/
#guard_msgs in
example : BlockOk Φy framedFetch linux Ψ (Asm.addr framed 0 .start) roomy := by ty_block

theorem divide_ok : BlocksOk Φd divideFetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | check =>
    -- mov rcx, [rdi]
    ty_step
    ty_name .rcx as v
    ty_name .rax as a
    -- entering `start`: the test found `v` not to be zero
    ty_block
  -- the divisor is not zero: the tactic finds `hv` among the hypotheses
  | start a v hv => ty_block
  | out => ty_block

-- A load from there through another register is a general-protection fault.
#guard match exec linux (.mov .w64 (.r_m .rax (.sib (some .rcx) none 0)))
    (nowhere.setReg .rcx 0x0200000000000000) with
  | .fault .generalProtection => true
  | _ => false

/-! A fact the checker is given. The field holds exactly `n * (n + 1)`, and
what is stored there is exactly twice the sum of the numbers up to `n`.
That the two are the same is no arithmetic the checker does for itself: it
is a theorem, marked for it to use. Without the mark the store is refused. -/

/-- The sum of the numbers up to `n`. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

theorem tri_twice (n : Nat) : tri n * 2 = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [tri, Nat.add_mul, ih]; simp only [Nat.mul_add]; omega

/-- `rdi` points to a record whose second field is exactly `n * (n + 1)`,
and `rax` holds exactly twice the sum up to `n`. -/
def summed (n : Nat) : Ctx :=
  ⟨fun r => if r = .rdi then .ptr ⟨16, [(8, .eq (BitVec.ofNat 64 (n * (n + 1))))]⟩ true 0
    else if r = .rax then .eq (BitVec.ofNat 64 (tri n * 2)) else .int, [], 0, Flags.Any, [], 0⟩

/-- error: cannot type `mov qword ptr [rdi+8], rax` in the current context
• a value of type `exactly BitVec.ofNat 64 (tri n * 2)` cannot be stored where `exactly BitVec.ofNat 64 (n * (n + 1))` is required. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example (n : Nat) : ∃ Γ', Straight Ψ 10 (summed n)
    (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 8)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

attribute [asm_fact] tri_twice

example (n : Nat) : ∃ Γ', Straight Ψ 10 (summed n)
    (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 8)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

end Rejected
