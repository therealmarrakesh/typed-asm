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
  .label .i7, .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 12))),
  .label .i8, .ins (.mov .w64 (.rm_r (.reg .rsp) .rax)),
  .label .i9, .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdx) none 8)) .rdi)),
  .label .i10, .ins .ret,
  .label .i11, .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) (some (.rcx, .s8)) 0))),
  .label .i12, .ins (.cmov .g .w32 .rax (.reg .rcx)),
  .label .i13, .ins (.alu .add .w32 (.rm_r (.mem (.sib (some .rsp) none 8)) .rax)),
  .label .i14, .ins (.shift .shl .w32 (.mem (.sib (some .rsi) none 0)) (.imm 1)),
  .label .i15, .ins (.imul2 .w32 .rax (.mem (.sib (some .rdi) none 14))),
  .label .i16, .ins (.unary .not .w64 (.mem (.sib (some .rdx) none 8))),
  .label .i17, .ins (.unary .neg .w64 (.mem (.sib (some .rdi) (some (.rcx, .s8)) 0))),
  .label .i18, .ins (.jmp (.ind (.reg .rax))),
  .label .i19, .ins (.alu .add .w32 (.rm_i (.mem (.rip 100)) 1))]

def fetch : Fetch := Asm.fetch 0 code

/-- No address may be jumped to, and there are no memory blocks. -/
def Φ : CodeTy := fun _ _ => False
def Ψ : MemTy := .ofList [] []

/-- `rdi`: a writable record of two integers. `rsi`: the same, read-only.
`rdx`: a writable record whose second field is a pointer. Everything else
is an integer. The stack is full. -/
def Γ : Ctx where
  regs := fun r =>
    if r = .rdi then .ptr (.raw 16) true 0
    else if r = .rsi then .ptr (.raw 16) false 0
    else if r = .rdx then .ptr ⟨16, [(8, .ptr (.raw 8) false 0)]⟩ true 0
    else .int
  stack := []
  room := 0
  flags := Flags.Any

/-- error: at address 0: cannot type `mov qword ptr [rax], rcx` in the current context
• storeField: `rax` must hold a writable pointer, but its type is `int`. Used as an address, an arbitrary number is a general-protection fault where the processor has no such address, and a page fault where there is no memory for it -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i0) Γ := by ty_step

/-- error: at address 3: cannot type `mov rax, qword ptr [rdi+16]` in the current context
• loadField: no typed value of the block starts at that offset
• loadInt: the access would reach past the end of the block. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i1) Γ := by ty_step

/-- error: at address 7: cannot type `mov qword ptr [rsi], rcx` in the current context
• storeField: `rsi` must hold a writable pointer, but its type is `read-only pointer to 16 bytes`. A store to memory that is read-only is a page fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i2) Γ := by ty_step

/-- error: at address 10: cannot type `push rax` in the current context
• push: there is not enough free stack: the context has room for 0. Below the stack the program was given there may be no memory, which is a page fault, or other data, which would be overwritten -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i3) Γ := by ty_step

/-- error: at address 11: cannot type `mov dword ptr [rdx+8], ecx` in the current context
• storeInt: a typed value of the block reaches into those bytes, and plain bytes may not be stored over it. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i4) Γ := by ty_step

/-- error: at address 14: cannot type `div rcx` in the current context
• divSafe: the divisor, `rcx₀`, is not known to be non-zero: a check is needed before the divide. Dividing by zero is a divide error -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i5) Γ := by ty_step

/-- error: at address 17: cannot type `adc rax, rcx` in the current context
• aluExactRR: this rule does not cover operations that read the carry flag
• aluRR: the operation reads the carry flag, which is not known to be defined here. The processor leaves it undefined after some instructions, and the result would then not be determined -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i6) Γ := by ty_step

/-- error: at address 20: cannot type `mov rax, qword ptr [rdi+12]` in the current context
• loadField: no typed value of the block starts at that offset
• loadInt: the access would reach past the end of the block. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i7) Γ := by ty_step

/-- error: at address 24: cannot type `mov rsp, rax` in the current context
• movRR64: `rsp` cannot be this operand -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i8) Γ := by ty_step

/-- error: at address 27: cannot type `mov qword ptr [rdx+8], rdi` in the current context
• storeField: a value of type `pointer to 16 bytes` cannot be stored where `read-only pointer to 8 bytes` is required. The memory would no longer hold what its type says, and a later use of the value there could fault
• storeInt: a typed value of the block reaches into those bytes, and plain bytes may not be stored over it. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i9) Γ := by ty_step

/-- error: `ret` can transfer control, so it ends the block and is not typed by `ty_step` -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i10) Γ := by ty_step

/-- error: at address 32: cannot type `mov rax, qword ptr [rdi+rcx*8]` in the current context
• loadIndexed: the index register `rcx` must hold an exactly known value, but its type is `int`; `ty_name` gives an integer a name. An unknown index could reach outside what the base points to, where there may be no memory (a page fault) or other data -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i11) Γ := by ty_step

/-- error: at address 36: cannot type `cmovg eax, ecx` in the current context
• cmovRM: the flags are not known here, so they do not decide the condition. The processor leaves them undefined after some instructions, and what this one does would then not be determined -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i12) Γ := by ty_step

/-- error: at address 39: cannot type `add dword ptr [rsp+8], eax` in the current context
• aluStoreR: those bytes are not known to be inside one piece of the stack. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i13) Γ := by ty_step

/-- error: at address 43: cannot type `shl dword ptr [rsi], 1` in the current context
• shiftImm: `rsi` must hold a writable pointer, but its type is `read-only pointer to 16 bytes`. A store to memory that is read-only is a page fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i14) Γ := by ty_step

/-- error: at address 45: cannot type `imul eax, dword ptr [rdi+14]` in the current context
• imul2RM: the access would reach past the end of the block. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i15) Γ := by ty_step

/-- error: at address 49: cannot type `not qword ptr [rdx+8]` in the current context
• notRM: a typed value of the block reaches into those bytes, and plain bytes may not be stored over it. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i16) Γ := by ty_step

/-- error: at address 53: cannot type `neg qword ptr [rdi+rcx*8]` in the current context
• negRM: the index register `rcx` must hold an exactly known value, but its type is `int`; `ty_name` gives an integer a name. An unknown index could reach outside what the base points to, where there may be no memory (a page fault) or other data -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i17) Γ := by ty_step

/-- error: `jmp rax`: the operand does not hold a pointer to code here. Control would go to whatever number it holds: a general-protection fault where the processor has no such address, a page fault where there is no code. A register holding the exact address of a label becomes a pointer to code with `ty_fn_ptr` (a function) or `ty_code_ptr` (any other label) -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i18) Γ := by ty_block

/-- error: at address 59: cannot type `add dword ptr [rip+100], 1` in the current context
• aluStoreI: the address is not inside any memory block. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i19) Γ := by ty_step

/-- `rdi` holds a pointer to three integers, or null. -/
def maybe : Ctx :=
  ⟨fun r => if r = .rdi then .nullable (.ptr (.raw 24) false 0) else .int, [], 0, Flags.Any, [], 0⟩

/-- error: at address 3: cannot type `mov rax, qword ptr [rdi+16]` in the current context
• loadField: `rdi` must hold a pointer, but its type is `read-only pointer to 24 bytes or null`: it must be tested for null first, and `ty_null` then gives the two cases. An access through null is a page fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i1) maybe := by ty_step

/-- error: cannot type `mov word ptr [rdx+7], ax` in the current context
• store16RM: a typed value of the block reaches into those bytes, and plain bytes may not be stored over it. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example : ∃ Γ', Straight Ψ 10 Γ (.store16 (.sib (some .rdx) none 7) .rax) Γ' :=
  ⟨_, by ty_straight⟩

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
def bare : Ctx := ⟨fun _ => .int, [], 0, Flags.Any, [], 0⟩

/-- Eight plain bytes on the stack. -/
def oneSlot : Ctx := ⟨fun _ => .int, [.raw 8], 0, Flags.Any, [], 0⟩

inductive AtTarget : Target → Ctx → Prop
  | start : AtTarget .start bare
  | far : AtTarget .far bare
  | needsSlot : AtTarget .needsSlot oneSlot
  | needsPtr :
    AtTarget .needsPtr ⟨fun r => if r = .rdi then .ptr (.raw 8) true 0 else .int, [], 0, Flags.Any, [], 0⟩

def Φj : CodeTy := .ofLabels jumps 0 AtTarget

/-- error: no context allowed at label `needsSlot` accepts the current one
• needsSlot: the stack, the free room or the flags do not match -/
#guard_msgs in
example : BlockOk Φj jumpFetch linux Ψ (Asm.addr jumps 0 .start) bare := by ty_block

/-- error: no context allowed at label `needsPtr` accepts the current one
• needsPtr: `rdi` has type `int`, but `pointer to 8 bytes` is required -/
#guard_msgs in
example : BlockOk Φj jumpFetch linux Ψ (Asm.addr jumps 0 .far) bare := by ty_block

/-- error: `ret` needs a return address on top of the stack, but the context does not have one there. Control would go to whatever number is there: a general-protection fault where the processor has no such address, a page fault where there is no code -/
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

/-- Nothing is known, and there is room for eight more bytes. -/
def roomy : Ctx := ⟨fun _ => .int, [], 8, Flags.Any, [], 0⟩

inductive AtCallee : Callee → Ctx → Prop
  | direct : AtCallee .direct bare
  | indirect : AtCallee .indirect roomy
  | f (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    plain.CallerOk saved ret rest room → AtCallee .f (plain.entry saved ret rest room)

def Φc : CodeTy := .ofLabels calls 0 AtCallee

/-- error: `call 2`: there is no room on the stack for the return address: the context has room for 0. Below the stack the program was given there may be no memory, which is a page fault, or other data, which would be overwritten -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .direct) bare := by ty_call plain

/-- error: `call rax`: the operand does not hold a pointer to a function with this signature, or there is no room on the stack for the return address. A register holding the exact address of a function becomes a pointer to it with `ty_fn_ptr` -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .indirect) roomy := by ty_call plain

/-- error: ty_call: the instruction here is `ret`, not a call -/
#guard_msgs in
example : BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) bare := by ty_call plain

/-! ### Handing over a piece of the stack -/

/-- error: ty_stack_detach: the stack pointer's value must be known here (name it with `ty_name .rsp as sp`), and a piece of the stack must begin at that byte -/
#guard_msgs in
example (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : plain.CallerOk saved ret rest room) :
    BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) (plain.entry saved ret rest room) := by
  ty_stack_detach at 8

/-- error: ty_stack_attach: the first block the context owns is not one detached from the stack that lies where the stack now ends; the stack pointer's value must be known too -/
#guard_msgs in
example (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : plain.CallerOk saved ret rest room) :
    BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) (plain.entry saved ret rest room) := by
  ty_stack_attach

/-- error: `ret`: pieces of the stack are still detached; a function must attach them again (`ty_stack_attach`) and leave the stack as it found it -/
#guard_msgs in
example (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : plain.CallerOk saved ret rest room) :
    BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) (plain.entry saved ret rest room) := by
  ty_name .rsp as sp
  ty_stack_detach at 8
  ty_block

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

/-- error: `jo 8`: the flags known here do not decide the condition. The processor leaves some flags undefined after some instructions, and which way this goes would then not be determined -/
#guard_msgs in
example : BlockOk Φf flaggedFetch linux Ψ (Asm.addr flagged 0 .overflow) bare := by ty_block

example : BlockOk Φf flaggedFetch linux Ψ (Asm.addr flagged 0 .carry) bare := by ty_block

/-! ## System calls

A `syscall` is typed only for a call the model covers, with the number in
`rax` exactly known. A `read` also needs its buffer to lie in plain bytes of
a writable block, for as many bytes as it asks for. -/

inductive Sys
  | unknown | unmodelled | noBuffer | tooLong | overPointer
  deriving DecidableEq

def sys : List (Asm Sys) := [
  .label .unknown, .ins .syscall,
  .label .unmodelled, .ins (.mov .w32 (.rm_i (.reg .rax) 11)), .ins .syscall,
  .label .noBuffer, .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
    .ins (.mov .w32 (.rm_i (.reg .rdx) 16)), .ins .syscall,
  .label .tooLong, .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
    .ins (.mov .w32 (.rm_i (.reg .rdx) 17)), .ins .syscall,
  .label .overPointer, .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
    .ins (.mov .w32 (.rm_i (.reg .rdx) 16)), .ins .syscall]

def sysFetch : Fetch := Asm.fetch 0 sys

def Φy : CodeTy := fun _ _ => False

/-- `rsi` points to a writable block of the given shape. -/
def buffer (S : Shape) : Ctx :=
  ⟨fun r => if r = .rsi then .ptr S true 0 else .int, [], 0, Flags.Any, [], 0⟩

/-- error: `syscall`: the call number in `rax` must be exactly known, but its type is `int` -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .unknown) bare := by ty_block

/-- error: `syscall`: call number 11 has no rule. The calls that can be typed are `read` (0), `write` (1), `close` (3), `fstat` (5), `lseek` (8), `mmap` (9), `exit` (60), `clock_gettime` (228), `exit_group` (231), `openat` (257) and `getrandom` (318) -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .unmodelled) bare := by ty_block

/-- error: `read` needs `rsi` to hold a writable pointer to the buffer, the address of stack slots taken with `lea` once `rsp` has a name, or the address of a byte of a block the context owns, but its type is `int` -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .noBuffer) bare := by ty_block

/-- error: `read` could overwrite something that is not plain bytes: the buffer in `rsi` does not have room for the count in `rdx` in plain bytes of its block -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .tooLong) (buffer (.raw 16)) := by
  ty_block

/-- error: `read` could overwrite something that is not plain bytes: the buffer in `rsi` does not have room for the count in `rdx` in plain bytes of its block -/
#guard_msgs in
example : BlockOk Φy sysFetch linux Ψ (Asm.addr sys 0 .overPointer)
    (buffer ⟨16, [(8, .ptr (.raw 8) false 0)]⟩) := by
  ty_block

/-! ## Arguments

An argument's slot is loaded by its number only when the number is exactly
known and is one of the slots the context has. -/

inductive Arg
  | unknown | beyond
  deriving DecidableEq

def argLoads : List (Asm Arg) := [
  .label .unknown, .ins (.mov .w64 (.r_m .rsi (.sib (some .rsp) (some (.rax, .s8)) 8))), .ins .ud2,
  .label .beyond, .ins (.mov .w32 (.rm_i (.reg .rax) 7)),
    .ins (.mov .w64 (.r_m .rsi (.sib (some .rsp) (some (.rax, .s8)) 8))), .ins .ud2]

def argFetch : Fetch := Asm.fetch 0 argLoads

/-- error: at address 0: cannot type `mov rsi, qword ptr [rsp+rax*8+8]` in the current context
• loadStackIndexed: the index register `rax` must hold an exactly known value, but its type is `int`; `ty_name` gives an integer a name. An unknown index could reach outside what the base points to, where there may be no memory (a page fault) or other data -/
#guard_msgs in
example : BlockOk Φy argFetch linux Ψ (Asm.addr argLoads 0 .unknown) (argsCtx 0 2) := by ty_block

/-- error: at address 12: cannot type `mov rsi, qword ptr [rsp+rax*8+8]` in the current context
• loadStackIndexed: those bytes are not known to be inside one piece of the stack. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example : BlockOk Φy argFetch linux Ψ (Asm.addr argLoads 0 .beyond) (argsCtx 0 2) := by ty_block

/-! ## Text

A pointer into text may be read through, one byte at a time. Stepped
forward where the byte it points at is not known to be other than zero, it
is a number and no longer a pointer; and nothing may be stored through it. -/

inductive Txt
  | onward | store
  deriving DecidableEq

def texts : List (Asm Txt) := [
  .label .onward, .ins (.alu .add .w64 (.rm_i (.reg .rdi) 1)),
    .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 0))), .ins .ud2,
  .label .store, .ins (.store8 (.sib (some .rdi) none 0) .rax), .ins .ud2]

def textFetch : Fetch := Asm.fetch 0 texts

/-- `rdi` points into text. -/
def atText : Ctx := ⟨fun r => if r = .rdi then .str false else .int, [], 0, Flags.Any, [], 0⟩

/-- error: at address 4: cannot type `movzx eax, byte ptr [rdi]` in the current context
• movzxRM: `rdi` must hold a pointer, but its type is `int`. Used as an address, an arbitrary number is a general-protection fault where the processor has no such address, and a page fault where there is no memory for it -/
#guard_msgs in
example : BlockOk Φy textFetch linux Ψ (Asm.addr texts 0 .onward) atText := by ty_block

/-- error: at address 9: cannot type `mov byte ptr [rdi], al` in the current context
• store8RM: `rdi` must hold a writable pointer, but its type is `pointer into text`. Used as an address, an arbitrary number is a general-protection fault where the processor has no such address, and a page fault where there is no memory for it -/
#guard_msgs in
example : BlockOk Φy textFetch linux Ψ (Asm.addr texts 0 .store) atText := by ty_block

/-! ## Other calls that store into a buffer

`fstat`, `clock_gettime` and `getrandom` are typed by the condition of a
`read`: the bytes the kernel stores must all land in plain bytes of a block.
How many that is depends on the call. -/

inductive Fill
  | statSmall | clockInt | randomUnknown | randomLong
  deriving DecidableEq

def fills : List (Asm Fill) := [
  .label .statSmall, .ins (.mov .w32 (.rm_i (.reg .rax) 5)), .ins .syscall,
  .label .clockInt, .ins (.mov .w32 (.rm_i (.reg .rax) 228)), .ins .syscall,
  .label .randomUnknown, .ins (.mov .w32 (.rm_i (.reg .rax) 318)), .ins .syscall,
  .label .randomLong, .ins (.mov .w32 (.rm_i (.reg .rax) 318)),
    .ins (.mov .w32 (.rm_i (.reg .rsi) 24)), .ins .syscall]

def fillFetch : Fetch := Asm.fetch 0 fills

/-- Register `r` points to a writable block of two integers. -/
def twoAt (r : Reg) : Ctx :=
  ⟨fun r' => if r' = r then .ptr (.raw 16) true 0 else .int, [], 0, Flags.Any, [], 0⟩

/-- error: `fstat` could overwrite something that is not plain bytes: the buffer in `rsi` does not have room in plain bytes of its block for the 144 bytes the kernel stores -/
#guard_msgs in
example : BlockOk Φy fillFetch linux Ψ (Asm.addr fills 0 .statSmall) (twoAt .rsi) := by ty_block

/-- error: `clock_gettime` needs `rsi` to hold a writable pointer to the buffer, the address of stack slots taken with `lea` once `rsp` has a name, or the address of a byte of a block the context owns, but its type is `int` -/
#guard_msgs in
example : BlockOk Φy fillFetch linux Ψ (Asm.addr fills 0 .clockInt) bare := by ty_block

/-- error: `getrandom` needs the count in `rsi` to be exactly known, but its type is `int` -/
#guard_msgs in
example : BlockOk Φy fillFetch linux Ψ (Asm.addr fills 0 .randomUnknown) (twoAt .rdi) := by
  ty_block

/-- error: `getrandom` could overwrite something that is not plain bytes: the buffer in `rdi` does not have room for the count in `rsi` in plain bytes of its block -/
#guard_msgs in
example : BlockOk Φy fillFetch linux Ψ (Asm.addr fills 0 .randomLong) (twoAt .rdi) := by
  ty_block

/-! ## Asking for memory

An `mmap` is typed only in the form that gives fresh private memory, for a
block that fits in the length asked for and whose typed values all admit
zero. What it
hands back may be an error number, so it cannot be used as a pointer before
it has been tested. -/

inductive Map
  | unchecked | notZero | tooShort | shared | noKind | noHint | highHint
  deriving DecidableEq

/-- The arguments of an `mmap` of `len` bytes with the given flags, and the call. -/
def mmapCall (len flags : BitVec 32) : List (Asm Map) := [
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)), .ins (.mov .w32 (.rm_i (.reg .rsi) len)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)), .ins (.mov .w32 (.rm_i (.reg .r10) flags)),
  .ins .syscall]

def maps : List (Asm Map) :=
  [.label .unchecked] ++ mmapCall 16 0x22 ++
    [.ins (.mov .w64 (.r_m .rdx (.sib (some .rax) none 0))), .ins .ud2] ++
  [.label .notZero] ++ mmapCall 16 0x22 ++ [.ins .ud2] ++
  [.label .tooShort] ++ mmapCall 8 0x22 ++ [.ins .ud2] ++
  [.label .shared] ++ mmapCall 16 0x21 ++ [.ins .ud2] ++
  [.label .noKind] ++ mmapCall 16 0x22 ++ [.ins .ud2] ++
  -- the address asked for left as whatever `rdi` held
  [.label .noHint] ++ (mmapCall 16 0x22).drop 1 ++ [.ins .ud2] ++
  -- an address asked for that no program can have memory at
  [.label .highHint, .ins (.movAbs .rdi 0x800000000000)] ++ (mmapCall 16 0x22).drop 1 ++
    [.ins .ud2]

def mapFetch : Fetch := Asm.fetch 0 maps

/-- error: at address 25: cannot type `mov rdx, qword ptr [rax]` in the current context
• loadField: `rax` must hold a pointer, but its type is `pointer to 16 bytes or an error number`: it must be tested for an error first, and `ty_err` then gives the two cases. An error number used as an address is in the kernel's half: a page fault -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .unchecked) bare := by
  ty_steps
  ty_mmap (.raw 16)
  ty_block

/-- error: `mmap`: every typed value of the new block must admit zero, since that is what fresh memory holds: a value that may be null -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .notZero) bare := by
  ty_steps
  ty_mmap ⟨16, [(8, .ptr (.raw 8) true 0)]⟩

/-- error: `mmap`: the block does not fit in the length in `rsi` -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .tooShort) bare := by
  ty_steps
  ty_mmap (.raw 16)

/-- error: `mmap` is typed only for private memory that is not a file: `r10` must hold exactly 0x22, but its type is `exactly 0x21` -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .shared) bare := by
  ty_steps
  ty_mmap (.raw 16)

/-- error: `mmap`: the memory typing declares no kind 7 -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .noKind) bare := by
  ty_steps
  ty_mmap_kind 7

/-- error: `mmap` needs the address asked for in `rdi` to be exactly known (zero leaves the choice to the kernel), but its type is `int` -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .noHint) bare := by
  ty_steps
  ty_mmap (.raw 16)

/-- error: `mmap`: the address asked for in `rdi` is above every address a program can have memory at, and the model does not say what the kernel does then -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .highHint) bare := by
  ty_steps
  ty_mmap (.raw 16)

/-! ## Memory the program owns

A page the context owns can be used only while it is listed there. Giving it
back takes it off the list, and a jump may not go where the list is expected
to be something else: a page cannot be dropped by forgetting it. -/

inductive Mem
  | afterFree | leak | notOwned | done
  deriving DecidableEq

/-- The arguments of an `mmap` of one page, the call, and the test that
sends an error number to `done`. -/
def ownCall : List (Asm Mem) := [
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)), .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)), .ins (.mov .w32 (.rm_i (.reg .r10) 0x22)),
  .ins .syscall, .ins (.test .w64 (.reg .rax) (.reg .rax)), .jcc .s .done]

def owning : List (Asm Mem) :=
  [.label .afterFree] ++ ownCall ++ [
    .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)), .ins (.mov .w32 (.rm_i (.reg .rax) 11)),
    .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)), .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
    .ins .syscall, .ins (.mov .w64 (.r_m .rcx (.sib (some .rbx) none 0))), .ins .ud2] ++
  [.label .leak] ++ ownCall ++ [.jmp .done] ++
  [.label .notOwned, .ins (.mov .w32 (.rm_i (.reg .rax) 11)),
    .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)), .ins .syscall, .ins .ud2] ++
  [.label .done, .ins .ud2]

def ownFetch : Fetch := Asm.fetch 0 owning

/-- At `done` nothing is owned. -/
inductive AtMem : Mem → Ctx → Prop
  | done : AtMem .done bare

def Φm : CodeTy := .ofLabels owning 0 AtMem

/-- error: at address 52: cannot type `mov rcx, qword ptr [rbx]` in the current context
• loadField: `rbx` must hold a pointer, but its type is `exactly p`
• loadInt: the address is not known to be inside a block the context owns. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
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

/-- error: `munmap` is typed for a block the context owns: `rax` must hold exactly 11, `rdi` exactly the address of an owned block, and `rsi` an exactly known length -/
#guard_msgs in
example : BlockOk Φm ownFetch linux Ψ (Asm.addr owning 0 .notOwned) bare := by
  ty_steps
  ty_munmap

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

/-! A function handed a page must hand it back: it may not give it to the
kernel and return as if nothing had happened. And inside it, an index into
the page must be known to fall within it. -/

inductive Fn
  | drops | reaches
  deriving DecidableEq

def handed : List (Asm Fn) := [
  .label .drops, .ins (.mov .w32 (.rm_i (.reg .rax) 11)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)), .ins .syscall, .ins .ret,
  .label .reaches, .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) (some (.rcx, .s8)) 0))),
  .ins .ret]

def handedFetch : Fetch := Asm.fetch 0 handed

/-- Takes the page at the address in `rdi` and gives it back. -/
def pageSig (p : BitVec 64) : FnSig where
  args := fun r => if r = .rdi then .eq p else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0
  takes := [(p, .raw 4096)]
  gives := [(p, .raw 4096)]

inductive AtFn : Fn → Ctx → Prop
  | drops (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (pageSig p).CallerOk saved ret rest room → AtFn .drops ((pageSig p).entry saved ret rest room)
  | reaches (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (pageSig p).CallerOk saved ret rest room →
    AtFn .reaches ((pageSig p).entry saved ret rest room)

def Φh : CodeTy := .ofLabels handed 0 AtFn

/-- error: `ret`: the blocks owned here are not the ones the function gives back, followed by the caller's own; a function must hand back what its signature says and dispose of anything else it took -/
#guard_msgs in
example (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : (pageSig p).CallerOk saved ret rest room) :
    BlockOk Φh handedFetch linux Ψ (Asm.addr handed 0 .drops)
      ((pageSig p).entry saved ret rest room) := by
  ty_steps
  ty_munmap
  ty_block

/-- error: at address 13: cannot type `mov rax, qword ptr [rdi+rcx*8]` in the current context
• loadIndexed: `rdi` must hold a pointer, but its type is `exactly p`
• loadOwned: the address is not known to be inside a block the context owns. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed
• loadInt: the bytes are not known to be inside the block: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : (pageSig p).CallerOk saved ret rest room) :
    BlockOk Φh handedFetch linux Ψ (Asm.addr handed 0 .reaches)
      ((pageSig p).entry saved ret rest room) := by
  ty_name .rcx as i
  ty_block

/-! A function that hands back a block it made must say which block before
it returns, and may not name one it does not own. -/

inductive Mk
  | make
  deriving DecidableEq

def making : List (Asm Mk) := [.label .make, .ins .ret]

def makingFetch : Fetch := Asm.fetch 0 making

/-- Whatever address `x` is in `rax` at the return, the caller owns a page there. -/
def makeSig : FnSigEx (BitVec 64) where
  args := fun _ => .int
  preserved := calleeSaved
  need := 0
  results := fun x r => if r = .rax then .eq x else .int
  gives := fun x => [(x, .raw 4096)]

inductive AtMk : Mk → Ctx → Prop
  | make (saved : Reg → Ty) (ret : BitVec 64 → Ctx) (rest : List Shape) (room : Nat)
      (frame : List (BitVec 64 × Shape)) (above : Nat) :
    makeSig.CallerOk saved ret rest room frame above → AtMk .make (makeSig.entry saved ret rest room frame above)

def Φk : CodeTy := .ofLabels making 0 AtMk

/-- error: `ret`: the return address here is ready for a family of contexts, one for each value the function may hand back; say which the function returns into with `ty_return_as` -/
#guard_msgs in
example (saved : Reg → Ty) (ret : BitVec 64 → Ctx) (rest : List Shape) (room : Nat)
    (frame : List (BitVec 64 × Shape)) (above : Nat) (hK : makeSig.CallerOk saved ret rest room frame above) :
    BlockOk Φk makingFetch linux Ψ (Asm.addr making 0 .make)
      (makeSig.entry saved ret rest room frame above) := by
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

/-! A call through a register needs the register to be a pointer to the
function: holding some number is not enough. -/

def calling : List (Asm Mk) := [.label .make, .ins (.call (.ind (.reg .r12)))]

def callingFetch : Fetch := Asm.fetch 0 calling

/-- error: ty_call: the operand does not hold a pointer to a function with this signature. A register holding the exact address of a function becomes a pointer to it with `ty_fn_ptr` -/
#guard_msgs in
example : BlockOk Φk callingFetch linux Ψ (Asm.addr calling 0 .make) roomy := by
  ty_call makeSig returning fun x => ⟨fun _ => .int, [], 1, Flags.Any, [(x, .raw 4096)], 0⟩

/-! ## Accepted, for contrast

Storing a writable pointer into a field typed as a read-only pointer is
allowed: a writable pointer may be used as a read-only one. -/

def Γ₂ : Ctx where
  regs := fun r =>
    if r = .rdx then .ptr ⟨16, [(8, .ptr (.raw 8) false 0)]⟩ true 0
    else if r = .rdi then .ptr (.raw 8) true 0
    else .int
  stack := []
  room := 0
  flags := Flags.Any

example : ∃ Γ', Straight Ψ 10 Γ₂ (.mov .w64 (.rm_r (.mem (.sib (some .rdx) none 8)) .rdi)) Γ' :=
  ⟨_, by ty_straight⟩

/-- One integer on the stack; `rdi` a writable record of two integers. -/
def Γ₃ : Ctx where
  regs := fun r => if r = .rdi then .ptr (.raw 16) true 0 else .int
  stack := [.raw 8]
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

/-! A 16-bit store, into a field and into a stack slot. -/

example : ∃ Γ', Straight Ψ 10 Γ₃ (.store16 (.sib (some .rdi) none 6) .rax) Γ' :=
  ⟨_, by ty_straight⟩

example : ∃ Γ', Straight Ψ 10 Γ₃ (.store16 (.sib (some .rsp) none 2) .rax) Γ' :=
  ⟨_, by ty_straight⟩

/-! Through an index: a store into an array of integers, and a load from
an array of pointers, which keeps the pointer's type. -/

/-- `rdi`: 32 plain bytes, writable. `rsi`: four pointers to sixteen bytes
each. The index in `rcx` is exactly 2. -/
def Γ₄ : Ctx where
  regs := fun r =>
    if r = .rdi then .ptr (.raw 32) true 0
    else if r = .rsi then .ptr ((ShapeOf.mk 8 [(0, .ptr (.raw 16) true 0)]).rep 4) false 0
    else if r = .rcx then .eq 2
    else .int
  stack := [.raw 8]
  room := 0
  flags := Flags.Any

example : ∃ Γ', Straight Ψ 10 Γ₄
    (.mov .w64 (.rm_r (.mem (.sib (some .rdi) (some (.rcx, .s8)) 0)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

example : Straight Ψ 10 Γ₄ (.mov .w64 (.r_m .rax (.sib (some .rsi) (some (.rcx, .s8)) 8)))
    (Γ₄.setReg .rax (.ptr (.raw 16) true 0)) := by
  ty_straight

/-! A stack slot holding an integer can be given a name, like a register. -/

example (h : ∀ v : BitVec 64, BlockOk Φ fetch linux Ψ 0
    { Γ₄ with stack := [.slot (.eq v)] }) : BlockOk Φ fetch linux Ψ 0 Γ₄ := by
  ty_name_slot 0 as v
  exact (h v).asTable

/-! The order in which owned blocks are listed can be changed: here the
block whose address is in `rbx` is brought to the front, where a call would
take it from. -/

/-- Two owned blocks; `rbx` holds the address of the second. -/
def Γo (p q : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .eq q else .int, [], 0, Flags.Any,
    [(p, .raw 8), (q, .raw 16)], 0⟩

example (p q : BitVec 64)
    (h : BlockOk Φ fetch linux Ψ 0 { Γo p q with owned := [(q, .raw 16), (p, .raw 8)] }) :
    BlockOk Φ fetch linux Ψ 0 (Γo p q) := by
  ty_own_first .rbx
  exact h.asTable

/-! However many blocks a context owns, an address is found in the one it
falls in: here the sixth. -/

/-- Six owned blocks of eight bytes each, the last holding a known value; `rbx` holds the address of the last. -/
def Γ₆ (a b c d e f : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .eq f else .int, [], 0, Flags.Any,
    [(a, .raw 8), (b, .raw 8), (c, .raw 8), (d, .raw 8), (e, .raw 8), (f, ⟨8, [(0, .eq 7)]⟩)], 0⟩

example (a b c d e f : BitVec 64) :
    Straight Ψ 10 (Γ₆ a b c d e f) (.mov .w64 (.r_m .rax (.sib (some .rbx) none 0)))
      ((Γ₆ a b c d e f).setReg .rax (.eq 7)) := by
  ty_straight

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

example : ∃ Γ', Straight Ψ 10 Γ (.store16 (.sib (some .rdx) none 6) .rax) Γ' :=
  ⟨_, by ty_straight⟩

/-! A record with a link and room for 64 bytes after it, filled a byte at a
time through an index known only by a bound. The bound is what shows each
byte to be inside the record and clear of the link; with a looser bound, or
from a displacement that reaches the link, the store is refused. -/

/-- Eighty bytes: a link at byte 0, a count, then 64 plain bytes from byte 16. -/
def node : Shape := ⟨80, [(0, .nullable (.ref 1 true 0))]⟩

/-- `rbx` points to a node; `rcx` holds exactly `i`. -/
def filling (i : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .ptr node true 0 else if r = .rcx then .eq i else .int, [], 0,
    Flags.Any, [], 0⟩

example (i : BitVec 64) (hlt : i.toNat < 64) :
    Straight Ψ 10 (filling i) (.store8 (.sib (some .rbx) (some (.rcx, .s1)) 16) .rax)
      (filling i) := by
  ty_straight

/-- error: cannot type `mov byte ptr [rbx+rcx*1+16], al` in the current context
• store8RM: the bytes are not known to be inside the block: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (i : BitVec 64) (hlt : i.toNat < 65) :
    Straight Ψ 10 (filling i) (.store8 (.sib (some .rbx) (some (.rcx, .s1)) 16) .rax)
      (filling i) := by
  ty_straight

/-- error: cannot type `mov byte ptr [rbx+rcx*1+7], al` in the current context
• store8RM: the bytes are not known to be clear of the typed values the block holds. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example (i : BitVec 64) (hlt : i.toNat < 64) :
    Straight Ψ 10 (filling i) (.store8 (.sib (some .rbx) (some (.rcx, .s1)) 7) .rax)
      (filling i) := by
  ty_straight

/-! An array of records. Each is 24 bytes: a number, a pointer to sixteen
bytes at byte 8, and eight plain bytes. `rbx` points at record `k` of `n`,
as a pointer does that is stepped along the array, and `k < n` is what puts
each access inside the array. The pointer is loaded with its type and stored
back; a plain byte goes into the last eight bytes, not over the pointer; and
stepping on by one record's length gives a pointer at record `k + 1`. -/

/-- One record of the array. -/
def entryShape : Shape := ⟨24, [(8, .ptr (.raw 16) true 0)]⟩

/-- `rbx` points at record `k` of an array of `n`. -/
def walking (n k : Nat) : Ctx :=
  ⟨fun r => if r = .rbx then .ptr (entryShape.rep n) true (24 * k) else .int, [], 0,
    Flags.Any, [], 0⟩

example (n k : Nat) (hk : k < n) :
    Straight Ψ 10 (walking n k) (.mov .w64 (.r_m .rax (.sib (some .rbx) none 8)))
      ((walking n k).setReg .rax (.ptr (.raw 16) true 0)) := by
  ty_straight

example (n k : Nat) (hk : k < n) :
    Straight Ψ 10 ((walking n k).setReg .rax (.ptr (.raw 16) true 0))
      (.mov .w64 (.rm_r (.mem (.sib (some .rbx) none 8)) .rax))
      ((walking n k).setReg .rax (.ptr (.raw 16) true 0)) := by
  ty_straight

example (n k : Nat) (hk : k < n) :
    Straight Ψ 10 (walking n k) (.store8 (.sib (some .rbx) none 16) .rax) (walking n k) := by
  ty_straight

example (n k : Nat) :
    ∃ Γ', Straight Ψ 10 (walking n k) (.alu .add .w64 (.rm_i (.reg .rbx) 24)) Γ' ∧
      Γ'.regs .rbx = .ptr (entryShape.rep n) true (24 * (k + 1)) :=
  ⟨_, by ty_straight, rfl⟩

/-- error: cannot type `mov byte ptr [rbx+8], al` in the current context
• store8RM: the bytes are not known to be clear of the typed values the block holds. The memory would no longer hold what its type says, and a later use of the value there could fault -/
#guard_msgs in
example (n k : Nat) (hk : k < n) :
    Straight Ψ 10 (walking n k) (.store8 (.sib (some .rbx) none 8) .rax) (walking n k) := by
  ty_straight

/-- error: cannot type `mov rax, qword ptr [rbx+8]` in the current context
• loadField: the block is not known to hold a typed value there: a bound on the index is needed among the hypotheses
• loadInt: the bytes are not known to be inside the block: a bound on the index is needed among the hypotheses. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (n k : Nat) :
    ∃ Γ', Straight Ψ 10 (walking n k) (.mov .w64 (.r_m .rax (.sib (some .rbx) none 8))) Γ' :=
  ⟨_, by ty_straight⟩

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

/-! The stack is exact to the byte too. A frame of 104 bytes holds a buffer
of 100: once the frame is regarded as those hundred bytes and four more, a
store through an index below 100 is inside the buffer, and one that might
reach byte 100 is refused, though the frame goes on. Inside a piece any
bytes may be read at any offset; across two pieces none may. -/

/-- `rcx` holds exactly `i`, and the stack is the given pieces. -/
def frame (i : BitVec 64) (σ : List Shape) : Ctx :=
  ⟨fun r => if r = .rcx then .eq i else .int, σ, 0, Flags.Any, [], 0⟩

example (i : BitVec 64) (h : BlockOk Φ fetch linux Ψ 0 (frame i [.raw 100, .raw 4])) :
    BlockOk Φ fetch linux Ψ 0 (frame i [.raw 104]) := by
  ty_stack_split at 100
  exact h.asTable

example (i : BitVec 64) (h : BlockOk Φ fetch linux Ψ 0 (frame i [.raw 104])) :
    BlockOk Φ fetch linux Ψ 0 (frame i [.raw 100, .raw 4]) := by
  ty_stack_join at 100
  exact h.asTable

example (i : BitVec 64) (hlt : i.toNat < 100) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.store8 (.sib (some .rsp) (some (.rcx, .s1)) 0) .rax) Γ' :=
  ⟨_, by ty_straight⟩

example (i : BitVec 64) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.mov .w64 (.r_m .rax (.sib (some .rsp) none 3))) Γ' :=
  ⟨_, by ty_straight⟩

example (i : BitVec 64) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.mov .w32 (.rm_r (.mem (.sib (some .rsp) none 100)) .rax)) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: cannot type `mov byte ptr [rsp+rcx*1], al` in the current context
• store8RM: those bytes are not known to be inside one piece of the stack. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (i : BitVec 64) (hlt : i.toNat < 101) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.store8 (.sib (some .rsp) (some (.rcx, .s1)) 0) .rax) Γ' :=
  ⟨_, by ty_straight⟩

/-- error: cannot type `mov rax, qword ptr [rsp+96]` in the current context
• loadStack: no typed value of that piece of the stack starts at that offset
• loadInt: the access would reach past the end of the piece of the stack it starts in. Where nothing is known to be, there may be no memory, which is a page fault, or other data, which would be read or overwritten unnoticed -/
#guard_msgs in
example (i : BitVec 64) :
    ∃ Γ', Straight Ψ 10 (frame i [.raw 100, .raw 4])
      (.mov .w64 (.r_m .rax (.sib (some .rsp) none 96))) Γ' :=
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
  (fun _ Δ => Δ = ⟨fun r => if r = .rsi then .eq 33 else .int, [], 0, Flags.Any, [], 0⟩)

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
      ⟨fun r => if r = .rdi then .ptr (.raw 8) false 0 else .int, [], 0, Flags.Any, [], 0⟩
  | start (a v : BitVec 64) : v ≠ 0 →
    AtDivide .start ⟨fun r => if r = .rax then .eq a else if r = .rcx then .eq v else .int,
      [], 0, Flags.Any, [], 0⟩
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
  -- the divisor is not zero: the tactic finds `hv` among the hypotheses
  | start a v hv => ty_block
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
      [], 0, Flags.Any, [], 0⟩
  | out : AtSigned .out bare

def Φs : CodeTy := .ofLabels signed 0 AtSigned

theorem signed_ok : BlocksOk Φs signedFetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  -- the tactic finds both facts about the divisor among the hypotheses
  | start a v hv hv1 => ty_block
  | out => ty_block

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

/-- Nor an executable one in the kernel's half. -/
example (s : State) : s.canExec 0xffffffffff600000 1 = false := by
  cases h : s.canExec 0xffffffffff600000 1 with
  | false => rfl
  | true => exact absurd (State.canExec_top h (by decide)) (by decide)

/-- No entry contract is met by a state whose stack pointer is at such an
address, whatever the program and however the state was made. -/
example (entry : BitVec 64) (parts : List (Nat × Perm × List Byte))
    (blocks : List (BitVec 64 × Layout)) (s : State)
    (hsp : s.getReg .rsp = 0x0200000000000000) : ¬ Entry entry parts blocks 11 0 s := by
  intro h
  have := h.stack_top (by decide)
  rw [hsp] at this
  exact absurd this (by decide)

/-- A state made by marking eight bytes below such an address writable, with
the stack pointer there. -/
def nowhere : State :=
  (State.init.setPerm (0x0200000000000000 - 8) 8 .rw).setReg .rsp 0x0200000000000000

/-- Marking the memory writable changed nothing. -/
example : nowhere.canWrite (0x0200000000000000 - 8) 8 = false := by decide

-- A `push` there is a stack fault: the processor has no such address, and
-- the access is through the stack.
#guard match exec linux (.push .rax) nowhere with
  | .fault .stackFault => true
  | _ => false

-- A load from there through another register is a general-protection fault.
#guard match exec linux (.mov .w64 (.r_m .rax (.sib (some .rcx) none 0)))
    (nowhere.setReg .rcx 0x0200000000000000) with
  | .fault .generalProtection => true
  | _ => false

-- A load from the kernel's half, or from an address with nothing there, is a
-- page fault: the address exists, the memory is not the program's.
#guard match exec linux (.mov .w64 (.r_m .rax (.sib (some .rcx) none 0)))
    (nowhere.setReg .rcx 0xffff800000000000) with
  | .fault .pageFault => true
  | _ => false

-- Which addresses the processor has depends on its width. `2 ^ 47` is not
-- one with 48-bit addresses, and is one with 57-bit addresses; no program
-- has memory there either way, so only the fault differs.
#guard match exec linux (.mov .w64 (.r_m .rax (.sib (some .rcx) none 0)))
    (nowhere.setReg .rcx 0x800000000000) with
  | .fault .generalProtection => true
  | _ => false

#guard match exec linux (.mov .w64 (.r_m .rax (.sib (some .rcx) none 0)))
    { nowhere.setReg .rcx 0x800000000000 with wide := true } with
  | .fault .pageFault => true
  | _ => false

/-! ## One permission to a page

A processor protects memory a page at a time. No state of the model has two
permissions inside one page, so asking for a few bytes gives their whole
page, as it does from the kernel. -/

/-- The bytes of a page have one permission, in every state. -/
example (s : State) : s.perm 0x10000 = s.perm 0x10fff := s.perm_page (by decide)

/-- Sixteen writable bytes, as a program's data might be. -/
def sixteen : State := State.init.setPerm 0x10000 16 .rw

/-- The page is writable to its last byte, and the next one is not. -/
example : sixteen.canWrite 0x10ff8 8 = true ∧ sixteen.canWrite 0x11000 1 = false := by
  decide

end Rejected
