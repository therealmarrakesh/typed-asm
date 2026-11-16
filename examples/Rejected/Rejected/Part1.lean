import Rejected.Common

/-!
# Rejections, part 1

See `Rejected.lean`. The tests are spread over the parts so that they are
checked side by side; which part a test is in means nothing.
-/

open TypedAsm

namespace Rejected

/-- error: `call 2`: there is no room on the stack for the return address: the context has room for 0. Below the stack the program was given there may be no memory, which is a page fault, or other data, which would be overwritten -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .direct) bare := by ty_call plain

/-- error: `read` needs `rsi` to hold a writable pointer to the buffer, the address of stack slots taken with `lea` once `rsp` has a name, or the address of a byte of a block the context owns, but its type is `int` -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .noBuffer) bare := by ty_block

/-- error: `getrandom` could overwrite something that is not plain bytes: the buffer in `rdi` does not have room for the count in `rsi` in plain bytes of its block
`rsi` was given its type by `mov esi, 24` at address 26 -/
#guard_msgs in
example : BlockOk Φy fillFetch linux Ψ (Asm.addr fills 0 .randomLong) (twoAt .rdi) := by
  ty_block

example : ∃ Γ', Straight Ψ 10 Γ₃ (.movsx .w64 .rax .w8 (.mem (.sib (some .rsp) none 7))) Γ' :=
  ⟨_, by ty_straight⟩

example (more : Shape) (rest : List Shape) :
    ∃ Γ', Straight Ψ 10
      ⟨fun r => if r = .rdi then .ptr ((ShapeOf.raw 16).append more) true 0 else .int, .raw 8 :: rest, 0,
        Flags.Any, [], 0⟩
      (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none 0)) .rdi)) Γ' :=
  ⟨_, by ty_straight⟩

/-! Layouts are exact to the byte. Eight bytes may be read from any offset
that leaves room for them, and plain bytes may be stored wherever no typed
value reaches: here at byte 7 of sixteen plain bytes, and at byte 6 of a
block whose pointer starts at byte 8. -/

example : ∃ Γ', Straight Ψ 10 Γ (.mov .w64 (.r_m .rax (.sib (some .rdi) none 4))) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight Ψ 10 Γ (.store16 (.sib (some .rdi) none 7) .rax) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: cannot type `mov rax, qword ptr [rbx+8]` in the current context
• loadField: the block is not known to hold a typed value there: a bound on the index is needed among the hypotheses
• loadInt: the bytes are not known to be inside the block: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (n k : Nat) :
    ∃ Γ', Straight Ψ 10 (walking n k) (.mov .w64 (.r_m .rax (.sib (some .rbx) none 8))) Γ' :=
  ⟨_, by ty_straight⟩

example (i : BitVec 64) (hlt : i.toNat < 100) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.store8 (.sib (some .rsp) (some (.rcx, .s1)) 0) .rax) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: cannot type `mov byte ptr [rsp+rcx*1], al` in the current context
• store8RM: those bytes are not known to be inside one piece of the stack. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (i : BitVec 64) (hlt : i.toNat < 101) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.store8 (.sib (some .rsp) (some (.rcx, .s1)) 0) .rax) Γ' :=
  ⟨_, by ty_straight⟩

example : BlockOk Φe exactFetch linux Ψ (Asm.addr exact 0 .start) bare := by
  ty_block

/-- Nor an executable one in the kernel's half. -/
example (s : State) : s.canExec 0xffffffffff600000 1 = false := by
  cases h : s.canExec 0xffffffffff600000 1 with
  | false => rfl
  | true => exact absurd (State.canExec_top h (by decide)) (by decide)

/-! ## One permission to a page

A processor protects memory a page at a time. No state of the model has two
permissions inside one page, so asking for a few bytes gives their whole
page, as it does from the kernel. -/

/-- The bytes of a page have one permission, in every state. -/
example (s : State) : s.perm 0x10000 = s.perm 0x10fff := s.perm_page (by decide)

end Rejected
