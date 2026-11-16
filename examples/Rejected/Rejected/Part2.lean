import Rejected.Common

/-!
# Rejections, part 2

See `Rejected.lean`. The tests are spread over the parts so that they are
checked side by side; which part a test is in means nothing.
-/

open TypedAsm

namespace Rejected

/-- error: at address 10: cannot type `push rax` in the current context
• push: there is not enough free stack: the context has room for 0. Below the stack the program was given there may be no memory, which is a page fault, or other data, which would be overwritten -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i3) Γ := by ty_step

/-- error: at address 59: cannot type `add dword ptr [rip+100], 1` in the current context
• aluStoreI: the address is not inside any memory block. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i19) Γ := by ty_step

/-- error: `ret` needs a return address on top of the stack, but the context does not have one there. Control would go to whatever number is there: a general-protection fault where the processor has no such address, a page fault where there is no code -/
#guard_msgs in
example : BlockOk Φj jumpFetch linux Ψ (Asm.addr jumps 0 .needsSlot) oneSlot := by ty_block

/-- error: `munmap` is typed for a block the context owns: `rax` must hold exactly 11, `rdi` exactly the address of an owned block, and `rsi` an exactly known length -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .unmodelled) bare := by ty_block

/-- error: `getrandom` needs the count in `rsi` to be exactly known, but its type is `int` -/
#guard_msgs in
example : BlockOk Φy fillFetch linux Ψ (Asm.addr fills 0 .randomUnknown) (twoAt .rdi) := by
  ty_block

/-- error: `mmap` is typed only where the kernel chooses the place: `rdi` must hold exactly 0, but its type is `int`. Asked for an address, the kernel may put the memory where it would not of its own accord, such as in the reach of the stack -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .noHint) bare := by
  ty_steps
  ty_mmap (.raw 16)

/-! A block that was split is two blocks: the whole page can no longer be
given back in one call, until the two are joined again. And only blocks that
lie end to end can be joined. -/

/-- error: `munmap`: the length in `rsi` must cover exactly the owned block; a block that was split must be joined again first, or its parts given back one by one -/
#guard_msgs in
example : BlockOk Φm ownFetch linux Ψ (Asm.addr owning 0 .afterFree) bare := by
  ty_steps
  ty_mmap_own as p
  · ty_block
  · ty_step
    ty_branch
    ty_step
    ty_split .rbx at 8
    ty_steps
    ty_munmap
    ty_block

example : ∃ Γ', Straight Ψ 10 Γ₃ (.mulDiv .imul .w64 (.mem (.sib (some .rsp) none 0))) Γ' :=
  ⟨_, by ty_straight⟩

example (p q : BitVec 64)
    (h : BlockOk Φ fetch linux Ψ 0 { Γo p q with owned := [(q, .raw 16), (p, .raw 8)] }) :
    BlockOk Φ fetch linux Ψ 0 (Γo p q) := by
  ty_own_first .rbx
  exact h.asTable

example : ∃ Γ', Straight Ψ 10 Γ (.store16 (.sib (some .rdx) none 6) .rax) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: cannot type `mov byte ptr [rbx+rcx*1+7], al` in the current context
• store8RM: the bytes are not known to be clear of the typed values the block holds. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example (i : BitVec 64) (hlt : i.toNat < 64) :
    Straight Ψ 10 (filling i) (.store8 (.sib (some .rbx) (some (.rcx, .s1)) 7) .rax)
      (filling i) := by
  ty_straight

example (n k : Nat) (hk : k < n) :
    Straight Ψ 10 ((walking n k).setReg .rax (.ptr (.raw 16) true 0))
      (.mov .w64 (.rm_r (.mem (.sib (some .rbx) none 8)) .rax))
      ((walking n k).setReg .rax (.ptr (.raw 16) true 0)) := by
  ty_straight

/-! ## Memory where there can be none

A processor with 48-bit addresses refuses any access from `2 ^ 47` up to the
kernel's half of the address space, whatever a page table says, and the
kernel keeps its half and the page before it. No state of the model has
accessible memory there, so a starting state cannot be given a stack there,
and a program that is pointed there faults. -/

/-- No state has a writable byte at an address the processor refuses. -/
example (s : State) : s.canWrite 0x0200000000000000 1 = false := by
  cases h : s.canWrite 0x0200000000000000 1 with
  | false => rfl
  | true => exact absurd (State.canWrite_top h (by decide)) (by decide)

#guard match exec linux (.mov .w64 (.r_m .rax (.sib (some .rcx) none 0)))
    { nowhere.setReg .rcx 0x800000000000 with wide := true } with
  | .fault .pageFault => true
  | _ => false

end Rejected
