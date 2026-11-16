import Rejected.Common

/-!
# Rejections, part 6

See `Rejected.lean`. The tests are spread over the parts so that they are
checked side by side; which part a test is in means nothing.
-/

open TypedAsm

namespace Rejected

/-- error: at address 0: cannot type `mov qword ptr [rax], rcx` in the current context
• storeField: `rax` must hold a writable pointer, but its type is `int`. Used as an address, an arbitrary number is a general-protection fault where the processor has no such address, and a page fault where there is no memory for it -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i0) Γ := by ty_step

/-- error: `jmp rax`: the operand does not hold a pointer to code here. Control would go to whatever number it holds: a general-protection fault where the processor has no such address, a page fault where there is no code. A register holding the exact address of a label becomes a pointer to code with `ty_fn_ptr` (a function) or `ty_code_ptr` (any other label) -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i18) Γ := by ty_block

/-- error: cannot type `mov word ptr [rdx+7], ax` in the current context
• store16RM: a typed value of the block reaches into those bytes, and plain bytes may not be stored over it. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example : ∃ Γ', Straight Ψ 10 Γ (.store16 (.sib (some .rdx) none 7) .rax) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: no context allowed at label `needsPtr` accepts the current one
• needsPtr: `rdi` has type `int`, but `pointer to 8 bytes` is required -/
#guard_msgs in
example : BlockOk Φj jumpFetch linux Ψ (Asm.addr jumps 0 .far) bare := by ty_block

example : BlockOk Φf flaggedFetch linux Ψ (Asm.addr flagged 0 .zero) bare := by ty_block

/-- error: `syscall`: the call number in `rax` must be exactly known, but its type is `int` -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .unknown) bare := by ty_block

/-- error: `clock_gettime` needs `rsi` to hold a writable pointer to the buffer, the address of stack slots taken with `lea` once `rsp` has a name, or the address of a byte of a block the context owns, but its type is `int` -/
#guard_msgs in
example : BlockOk Φy fillFetch linux Ψ (Asm.addr fills 0 .clockInt) bare := by ty_block

/-- error: `mmap` is typed only for private memory that is not a file: `r10` must hold exactly 0x22, but its type is `exactly 0x21` -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .shared) bare := by
  ty_steps
  ty_mmap (.raw 16)

/-- error: `ret`: the blocks owned here are not the ones the function gives back, followed by the caller's own; a function must hand back what its signature says and dispose of anything else it took -/
#guard_msgs in
example (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : (pageSig p).CallerOk saved ret rest room) :
    BlockOk Φh handedFetch linux Ψ (Asm.addr handed 0 .drops)
      ((pageSig p).entry saved ret rest room) := by
  ty_steps
  ty_munmap
  ty_block

/-! Comparing memory with a register, a one-operand signed multiply, a
sign-extending byte load from the stack, and a 32-bit store to the stack. -/

example : ∃ Γ', Straight Ψ 10 Γ₃ (.alu .cmp .w32 (.rm_r (.mem (.sib (some .rdi) none 12)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

/-! A stack slot holding an integer can be given a name, like a register. -/

example (h : ∀ v : BitVec 64, BlockOk Φ fetch linux Ψ 0
    { Γ₄ with stack := [.slot (.eq v)] }) : BlockOk Φ fetch linux Ψ 0 Γ₄ := by
  ty_name_slot 0 as v
  exact (h v).asTable

/-! A record used as a shorter one, and a stack deeper than a label cares
about, need no rule of their own: the context is stated for every tail.
Here `rdi` points to a record that starts with sixteen plain bytes and goes
on in any way at all, and the stack holds one integer above anything at all. -/

example (more : Shape) (rest : List Shape) :
    ∃ Γ', Straight Ψ 10
      ⟨fun r => if r = .rdi then .ptr ((ShapeOf.raw 16).append more) true 0 else .int, .raw 8 :: rest, 0,
        Flags.Any, [], 0⟩
      (.mov .w64 (.r_m .rax (.sib (some .rdi) none 8))) Γ' :=
  ⟨_, by ty_straight⟩

example (i : BitVec 64) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.mov .w32 (.rm_r (.mem (.sib (some .rsp) none 100)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: no context is declared at label `top`: a label that is jumped back to, called, or returned to must say what holds there -/
#guard_msgs in
example : BlockOk Φb backFetch linux Ψ (Asm.addr back 0 .start) bare := by ty_block

/-! A divide by a value in memory is typed like one by a register: the
value must be exactly known, and known not to be zero. Here it is on the
stack, and then a field reached through a pointer. -/

/-- A context for a divide: `rax` exactly 100, `rdx` zero, and one value on
the stack. -/
def dividing (τ : Ty) : Ctx :=
  ⟨fun r => if r = .rax then .eq 100 else if r = .rdx then .eq 0
    else if r = .rdi then .ptr ⟨16, [(8, .eq 7)]⟩ false 0 else .int,
    [.slot τ], 0, Flags.Any, [], 0⟩

example (c : BitVec 64) (hc : c ≠ 0) :
    ∃ Γ', Straight Ψ 10 (dividing (.eq c)) (.mulDiv .div .w64 (.mem (.sib (some .rsp) none 0))) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight Ψ 10 (dividing .int)
    (.mulDiv .div .w32 (.mem (.sib (some .rdi) none 8))) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: cannot type `div qword ptr [rsp]` in the current context
• divHeld: the value there must be exactly known, but has type `int`: a divide is typed only when its divisor is known not to be zero -/
#guard_msgs in
example : ∃ Γ', Straight Ψ 10 (dividing .int)
    (.mulDiv .div .w64 (.mem (.sib (some .rsp) none 0))) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: cannot type `div qword ptr [rsp]` in the current context
• divHeld: the divisor, `c`, is not known to be non-zero: a check is needed before the divide. Dividing by zero is a divide error -/
#guard_msgs in
example (c : BitVec 64) :
    ∃ Γ', Straight Ψ 10 (dividing (.eq c)) (.mulDiv .div .w64 (.mem (.sib (some .rsp) none 0))) Γ' :=
  ⟨_, by ty_straight⟩

-- Which addresses the processor has depends on its width. `2 ^ 47` is not
-- one with 48-bit addresses, and is one with 57-bit addresses; no program
-- has memory there either way, so only the fault differs.
#guard match exec linux (.mov .w64 (.r_m .rax (.sib (some .rcx) none 0)))
    (nowhere.setReg .rcx 0x800000000000) with
  | .fault .generalProtection => true
  | _ => false

end Rejected
