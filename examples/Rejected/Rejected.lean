import TypedAsm
import TypedAsm.Tactic

/-!
# Instructions the type system rejects

Each instruction below is unsafe in the given context, or has no typing rule.
The messages are the ones the typing tactic reports; `#guard_msgs` fails the
build if any of them changes.
-/

open TypedAsm

namespace Rejected

/-- One label per instruction, so each can be the start of its own block. -/
inductive Label
  | i0 | i1 | i2 | i3 | i4 | i5 | i6 | i7 | i8 | i9 | i10
  | i11 | i12 | i13 | i14 | i15 | i16 | i17 | i18
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .i0, .ins (.mov .w64 (.rm_r (.mem (.sib (some .rax) none 0)) .rcx)),
  .label .i1, .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 16))),
  .label .i2, .ins (.mov .w64 (.rm_r (.mem (.sib (some .rsi) none 0)) .rcx)),
  .label .i3, .ins (.push .rax),
  .label .i4, .ins (.mov .w32 (.rm_r (.mem (.sib (some .rdx) none 8)) .rcx)),
  .label .i5, .ins (.mulDiv .div .w64 (.reg .rcx)),
  .label .i6, .ins (.alu .adc .w64 (.rm_r (.reg .rax) .rcx)),
  .label .i7, .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 4))),
  .label .i8, .ins (.mov .w64 (.rm_r (.reg .rsp) .rax)),
  .label .i9, .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdx) none 8)) .rdi)),
  .label .i10, .ins .ret,
  .label .i11, .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) (some (.rcx, .s8)) 0))),
  .label .i12, .ins (.cmov .g .w32 .rax (.reg .rcx)),
  .label .i13, .ins (.alu .add .w32 (.rm_r (.mem (.sib (some .rsp) none 8)) .rax)),
  .label .i14, .ins (.shift .shl .w32 (.mem (.sib (some .rsi) none 0)) (.imm 1)),
  .label .i15, .ins (.imul2 .w32 .rax (.mem (.sib (some .rdi) none 6))),
  .label .i16, .ins (.unary .not .w64 (.mem (.sib (some .rdx) none 8))),
  .label .i17, .ins (.unary .neg .w64 (.mem (.sib (some .rdi) (some (.rcx, .s8)) 0))),
  .label .i18, .ins (.jmp (.ind (.reg .rax)))]

def fetch : Fetch := Asm.fetch 0 code

/-- No address may be jumped to, and there are no memory blocks. -/
def Φ : CodeTy := fun _ _ => False
def Ψ : MemTy := fun _ => none

/-- `rdi`: a writable record of two integers. `rsi`: the same, read-only.
`rdx`: a writable record whose second field is a pointer. Everything else
is an integer. The stack is full. -/
def Γ : Ctx where
  regs := fun r =>
    if r = .rdi then .ptr [.int, .int] true 0
    else if r = .rsi then .ptr [.int, .int] false 0
    else if r = .rdx then .ptr [.int, .ptr [.int] false 0] true 0
    else .int
  stack := []
  room := 0
  flags := Flags.Any

/-- error: at address 0: cannot type `mov qword ptr [rax], rcx` in the current context
• storeField: `rax` must hold a writable pointer, but its type is `int`
• storeIntR: `rax` must hold a writable pointer, but its type is `int` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i0) Γ := by ty_step

/-- error: at address 3: cannot type `mov rax, qword ptr [rdi+16]` in the current context
• loadField: there is no field or stack slot at that offset -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i1) Γ := by ty_step

/-- error: at address 7: cannot type `mov qword ptr [rsi], rcx` in the current context
• storeField: `rsi` must hold a writable pointer, but its type is `read-only pointer to [int, int]`
• storeIntR: `rsi` must hold a writable pointer, but its type is `read-only pointer to [int, int]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i2) Γ := by ty_step

/-- error: at address 10: cannot type `push rax` in the current context
• push: there is not enough free stack: the context has room for 0 -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i3) Γ := by ty_step

/-- error: at address 11: cannot type `mov dword ptr [rdx+8], ecx` in the current context
• storeIntR: the field must have type `int`, but has type `read-only pointer to [int]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i4) Γ := by ty_step

/-- error: at address 17: cannot type `adc rax, rcx` in the current context
• aluExactRR: this rule does not cover operations that read the carry flag
• aluRR: the operation reads the carry flag, which is not known to be defined here -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i6) Γ := by ty_step

/-- error: at address 20: cannot type `mov rax, qword ptr [rdi+4]` in the current context
• loadField: the displacement must be a non-negative multiple of 8 -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i7) Γ := by ty_step

/-- error: at address 24: cannot type `mov rsp, rax` in the current context
• movRR64: `rsp` cannot be this operand -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i8) Γ := by ty_step

/-- error: at address 27: cannot type `mov qword ptr [rdx+8], rdi` in the current context
• storeField: a value of type `pointer to [int, int]` cannot be stored where `read-only pointer to [int]` is required
• storeIntR: the field must have type `int`, but has type `read-only pointer to [int]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i9) Γ := by ty_step

/-- error: `ret` can transfer control, so it ends the block and is not typed by `ty_step` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i10) Γ := by ty_step

/-- error: at address 32: the type system has no rule for `mov rax, qword ptr [rdi+rcx*8]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i11) Γ := by ty_step

/-- error: at address 36: cannot type `cmovg eax, ecx` in the current context
• cmovRM: the flags are not known here, so they do not decide the condition -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i12) Γ := by ty_step

/-- error: at address 39: cannot type `add dword ptr [rsp+8], eax` in the current context
• aluStoreR: there is no field or stack slot at that offset -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i13) Γ := by ty_step

/-- error: at address 43: cannot type `shl dword ptr [rsi], 1` in the current context
• shiftRM: `rsi` must hold a writable pointer, but its type is `read-only pointer to [int, int]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i14) Γ := by ty_step

/-- error: at address 45: cannot type `imul eax, dword ptr [rdi+6]` in the current context
• imul2RM: the access would cross the end of an 8-byte field -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i15) Γ := by ty_step

/-- error: at address 49: cannot type `not qword ptr [rdx+8]` in the current context
• notRM: the field must have type `int`, but has type `read-only pointer to [int]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i16) Γ := by ty_step

/-- error: at address 53: cannot type `neg qword ptr [rdi+rcx*8]` in the current context
• negRM: this form of operand has no rule: a memory operand must be `[register + displacement]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i17) Γ := by ty_step

/-- error: `jmp rax`: the operand does not hold a code pointer here. A register holding the exact address of a label becomes one with `ty_code_ptr` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i18) Γ := by ty_block

/-! ## Control transfers

A small labelled program, for jumps and returns the tactic refuses. -/

inductive Target
  | start | far | needsSlot | needsPtr
  deriving DecidableEq

def jumps : List (Asm Target) := [
  .label .start, .jmp .needsSlot,
  .label .far, .jmp .needsPtr,
  .label .needsSlot, .ins .ret,
  .label .needsPtr, .ins .ret]

def jumpFetch : Fetch := Asm.fetch 0 jumps

/-- Nothing is known, and the stack is empty. -/
def bare : Ctx := ⟨fun _ => .int, [], 0, Flags.Any⟩

/-- One integer on the stack. -/
def oneSlot : Ctx := ⟨fun _ => .int, [.int], 0, Flags.Any⟩

inductive AtTarget : Target → Ctx → Prop
  | start : AtTarget .start bare
  | far : AtTarget .far bare
  | needsSlot : AtTarget .needsSlot oneSlot
  | needsPtr :
    AtTarget .needsPtr ⟨fun r => if r = .rdi then .ptr [.int] true 0 else .int, [], 0, Flags.Any⟩

def Φj : CodeTy := .ofLabels jumps 0 AtTarget

/-- error: no context allowed at label `needsSlot` accepts the current one
• needsSlot: the stack, the free room or the flags do not match -/
#guard_msgs in
example : BlockOk Φj jumpFetch linux Ψ (Asm.addr jumps 0 .start) bare := by ty_block

/-- error: no context allowed at label `needsPtr` accepts the current one
• needsPtr: `rdi` has type `int`, but `pointer to [int]` is required -/
#guard_msgs in
example : BlockOk Φj jumpFetch linux Ψ (Asm.addr jumps 0 .far) bare := by ty_block

/-- error: `ret` needs a return address on top of the stack, but the context does not have one there -/
#guard_msgs in
example : BlockOk Φj jumpFetch linux Ψ (Asm.addr jumps 0 .needsSlot) oneSlot := by ty_block

/-! ## Accepted, for contrast

Storing a writable pointer into a field typed as a read-only pointer is
allowed: a writable pointer may be used as a read-only one. -/

def Γ₂ : Ctx where
  regs := fun r =>
    if r = .rdx then .ptr [.int, .ptr [.int] false 0] true 0
    else if r = .rdi then .ptr [.int] true 0
    else .int
  stack := []
  room := 0
  flags := Flags.Any

example : ∃ Γ', Straight 10 Γ₂ (.mov .w64 (.rm_r (.mem (.sib (some .rdx) none 8)) .rdi)) Γ' :=
  ⟨_, by ty_straight⟩

/-- One integer on the stack; `rdi` a writable record of two integers. -/
def Γ₃ : Ctx where
  regs := fun r => if r = .rdi then .ptr [.int, .int] true 0 else .int
  stack := [.int]
  room := 0
  flags := Flags.Any

/-! Comparing memory with a register, a one-operand signed multiply, a
sign-extending byte load from the stack, and a 32-bit store to the stack. -/

example : ∃ Γ', Straight 10 Γ₃ (.alu .cmp .w32 (.rm_r (.mem (.sib (some .rdi) none 12)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight 10 Γ₃ (.mulDiv .imul .w64 (.mem (.sib (some .rsp) none 0))) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight 10 Γ₃ (.movsx .w64 .rax .w8 (.mem (.sib (some .rsp) none 7))) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight 10 Γ₃ (.mov .w32 (.rm_r (.mem (.sib (some .rsp) none 4)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

end Rejected
