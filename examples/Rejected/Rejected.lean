import TypedAsm
import TypedAsm.Tactic

/-!
# Instructions the type system rejects

Each instruction below is unsafe in the given context, or uses an operand
form that has no typing rule.
The messages are the ones the typing tactic reports; `#guard_msgs` fails the
build if any of them changes.
-/

open TypedAsm

namespace Rejected

/-- One label per instruction, so each can be the start of its own block. -/
inductive Label
  | i0 | i1 | i2 | i3 | i4 | i5 | i6 | i7 | i8 | i9 | i10
  | i11 | i12 | i13 | i14 | i15 | i16 | i17 | i18 | i19
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
  .label .i18, .ins (.jmp (.ind (.reg .rax))),
  .label .i19, .ins (.alu .add .w32 (.rm_i (.mem (.rip 100)) 1))]

def fetch : Fetch := Asm.fetch 0 code

/-- No address may be jumped to, and there are no memory blocks. -/
def Φ : CodeTy := fun _ _ => False
def Ψ : MemTy := .ofList []

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
• storeInt: `rax` must hold a writable pointer, but its type is `int` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i0) Γ := by ty_step

/-- error: at address 3: cannot type `mov rax, qword ptr [rdi+16]` in the current context
• loadField: there is no field or stack slot at that offset -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i1) Γ := by ty_step

/-- error: at address 7: cannot type `mov qword ptr [rsi], rcx` in the current context
• storeField: `rsi` must hold a writable pointer, but its type is `read-only pointer to [int, int]`
• storeInt: `rsi` must hold a writable pointer, but its type is `read-only pointer to [int, int]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i2) Γ := by ty_step

/-- error: at address 10: cannot type `push rax` in the current context
• push: there is not enough free stack: the context has room for 0 -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i3) Γ := by ty_step

/-- error: at address 11: cannot type `mov dword ptr [rdx+8], ecx` in the current context
• storeInt: the field must have type `int`, but has type `read-only pointer to [int]` -/
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
• storeInt: the field must have type `int`, but has type `read-only pointer to [int]` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i9) Γ := by ty_step

/-- error: `ret` can transfer control, so it ends the block and is not typed by `ty_step` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i10) Γ := by ty_step

/-- error: at address 32: cannot type `mov rax, qword ptr [rdi+rcx*8]` in the current context
• loadIndexed: the index register `rcx` must hold an exactly known value, but its type is `int`; `ty_name` gives an integer a name
• loadInt: the index register `rcx` must hold an exactly known value, but its type is `int`; `ty_name` gives an integer a name -/
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
• shiftImm: `rsi` must hold a writable pointer, but its type is `read-only pointer to [int, int]` -/
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
• negRM: the index register `rcx` must hold an exactly known value, but its type is `int`; `ty_name` gives an integer a name -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i17) Γ := by ty_step

/-- error: `jmp rax`: the operand does not hold a code pointer here. A register holding the exact address of a label becomes one with `ty_code_ptr` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i18) Γ := by ty_block

/-- error: at address 59: cannot type `add dword ptr [rip+100], 1` in the current context
• aluStoreI: the address is not inside any memory block -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i19) Γ := by ty_step

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

/-! ## Calls -/

inductive Callee
  | direct | indirect | f
  deriving DecidableEq

def calls : List (Asm Callee) := [
  .label .direct, .call .f,
  .label .indirect, .ins (.call (.ind (.reg .rax))),
  .label .f, .ins .ret]

def callFetch : Fetch := Asm.fetch 0 calls

/-- A function that takes and returns integers and uses no stack. -/
def plain : FnSig where
  args := fun _ => .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- Nothing is known, and there is room for one more slot. -/
def roomy : Ctx := ⟨fun _ => .int, [], 1, Flags.Any⟩

inductive AtCallee : Callee → Ctx → Prop
  | direct : AtCallee .direct bare
  | indirect : AtCallee .indirect roomy
  | f (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    plain.CallerOk saved ret rest room → AtCallee .f (plain.entry saved ret rest room)

def Φc : CodeTy := .ofLabels calls 0 AtCallee

/-- error: `call 2`: there is no room on the stack for the return address: the context has room for 0 -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .direct) bare := by ty_call plain

/-- error: `call rax`: the operand does not hold a pointer to a function with this signature that can be called with the room available here. A register holding the exact address of a label becomes a code pointer with `ty_code_ptr` -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .indirect) roomy := by ty_call plain

/-- error: ty_call: the instruction here is `ret`, not a call -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) bare := by ty_call plain

/-! ## Branching on flags that an instruction leaves

A shift by a constant defines the carry, zero and sign flags, and the
overflow flag only when the count is one. A multiply defines carry and
overflow. -/

inductive Flagged
  | zero | overflow | carry | out
  deriving DecidableEq

def flagged : List (Asm Flagged) := [
  .label .zero, .ins (.shift .shr .w32 (.reg .rcx) (.imm 3)), .jcc .e .out,
  .label .overflow, .ins (.shift .shl .w32 (.reg .rcx) (.imm 3)), .jcc .o .out,
  .label .carry, .ins (.mulDiv .mul .w32 (.reg .rcx)), .jcc .b .out,
  .label .out, .jmp .out]

def flaggedFetch : Fetch := Asm.fetch 0 flagged

def Φf : CodeTy := .ofLabels flagged 0 (fun _ Δ => Δ = bare)

example : BlockOk Φf flaggedFetch linux Ψ (Asm.addr flagged 0 .zero) bare := by ty_block

/-- error: `jo 8`: the flags known here do not decide the condition -/
#guard_msgs in
example : BlockOk Φf flaggedFetch linux Ψ (Asm.addr flagged 0 .overflow) bare := by ty_block

example : BlockOk Φf flaggedFetch linux Ψ (Asm.addr flagged 0 .carry) bare := by ty_block

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

example : ∃ Γ', Straight Ψ 10 Γ₂ (.mov .w64 (.rm_r (.mem (.sib (some .rdx) none 8)) .rdi)) Γ' :=
  ⟨_, by ty_straight⟩

/-- One integer on the stack; `rdi` a writable record of two integers. -/
def Γ₃ : Ctx where
  regs := fun r => if r = .rdi then .ptr [.int, .int] true 0 else .int
  stack := [.int]
  room := 0
  flags := Flags.Any

/-! Comparing memory with a register, a one-operand signed multiply, a
sign-extending byte load from the stack, and a 32-bit store to the stack. -/

example : ∃ Γ', Straight Ψ 10 Γ₃ (.alu .cmp .w32 (.rm_r (.mem (.sib (some .rdi) none 12)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight Ψ 10 Γ₃ (.mulDiv .imul .w64 (.mem (.sib (some .rsp) none 0))) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight Ψ 10 Γ₃ (.movsx .w64 .rax .w8 (.mem (.sib (some .rsp) none 7))) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight Ψ 10 Γ₃ (.mov .w32 (.rm_r (.mem (.sib (some .rsp) none 4)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

/-! ## Exactly known values

When the registers an instruction reads hold exactly known values, so does
the one it writes. The block below computes `(6 << 2) / 3 = 8` and from it
an address-style sum `8 + 3 * 8 + 1`. Every value along the way is known, so
the divide is shown not to raise a divide error, and the context at `out`,
which demands that `rsi` be exactly 33, is met with nothing left to prove. -/

inductive Exact
  | start | out
  deriving DecidableEq

def exact : List (Asm Exact) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rax) 6)),
  .ins (.shift .shl .w32 (.reg .rax) (.imm 2)),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 3)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.mulDiv .div .w32 (.reg .rcx)),
  .ins (.lea .w64 .rsi (.sib (some .rax) (some (.rcx, .s8)) 1)),
  .ins (.test .w64 (.reg .rsi) (.reg .rsi)),
  .jcc .e .out,
  .label .out, .jmp .out]

def exactFetch : Fetch := Asm.fetch 0 exact

/-- At `out`, `rsi` is exactly `8 + 3 * 8 + 1`. -/
def Φe : CodeTy := .ofLabels exact 0
  (fun _ Δ => Δ = ⟨fun r => if r = .rsi then .eq 33 else .int, [], 0, Flags.Any⟩)

example : BlockOk Φe exactFetch linux Ψ (Asm.addr exact 0 .start) bare := by
  ty_block

/-! A divisor loaded from memory, checked, and then used. The loaded value
is only an integer until it is given a name; the test then says something
about that name, and the label `start` is entered only with the divisor
known not to be zero, so the divide there cannot raise a divide error. -/

inductive Divide
  | check | start | out
  deriving DecidableEq

def divide : List (Asm Divide) := [
  .label .check,
  .ins (.mov .w64 (.r_m .rcx (.sib (some .rdi) none 0))),
  .ins (.test .w64 (.reg .rcx) (.reg .rcx)),
  .jcc .ne .start,
  .jmp .out,
  .label .start,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.mulDiv .div .w64 (.reg .rcx)),
  .label .out, .jmp .out]

def divideFetch : Fetch := Asm.fetch 0 divide

inductive AtDivide : Divide → Ctx → Prop
  | check : AtDivide .check
      ⟨fun r => if r = .rdi then .ptr [.int] false 0 else .int, [], 0, Flags.Any⟩
  | start (a v : BitVec 64) : v ≠ 0 →
    AtDivide .start ⟨fun r => if r = .rax then .eq a else if r = .rcx then .eq v else .int,
      [], 0, Flags.Any⟩
  | out : AtDivide .out bare

def Φd : CodeTy := .ofLabels divide 0 AtDivide

theorem divide_ok : BlocksOk Φd divideFetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | check =>
    -- mov rcx, [rdi]
    ty_step
    ty_name .rcx as v
    ty_name .rax as a
    ty_block
    -- entering `start`: the test found `v` not to be zero
    simpa [Cond.eval, Flags.ofResult] using hcond
  | start a v hv =>
    ty_step
    ty_step_with Straight.divSafe
    -- the divisor is not zero: the tactic finds `hv` among the hypotheses
    ty_block
  | out => ty_block

/-! A signed divide. `cqo` sign-extends `rax` into `rdx`; with the divisor
known to be neither zero nor minus one, the divide cannot raise a divide error. -/

inductive Signed
  | start | out
  deriving DecidableEq

def signed : List (Asm Signed) := [
  .label .start,
  .ins .cqo,
  .ins (.mulDiv .idiv .w64 (.reg .rcx)),
  .label .out, .jmp .out]

def signedFetch : Fetch := Asm.fetch 0 signed

inductive AtSigned : Signed → Ctx → Prop
  | start (a v : BitVec 64) : v ≠ 0 → v ≠ -1 →
    AtSigned .start ⟨fun r => if r = .rax then .eq a else if r = .rcx then .eq v else .int,
      [], 0, Flags.Any⟩
  | out : AtSigned .out bare

def Φs : CodeTy := .ofLabels signed 0 AtSigned

theorem signed_ok : BlocksOk Φs signedFetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start a v hv hv1 =>
    ty_step
    ty_step_with Straight.idivSafe
    ty_block
    -- the quotient fits: the divisor is not minus one
    exact .inr hv1
  | out => ty_block

end Rejected
