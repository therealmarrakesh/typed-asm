import TypedAsm
import TypedAsm.Tactic

/-!
# What the rejection tests share

The programs, contexts and typings the tests in this directory are about.
The tests themselves are in the numbered parts, which are checked side by
side.
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

/-- `rdi` holds a pointer to three integers, or null. -/
def maybe : Ctx :=
  ⟨fun r => if r = .rdi then .nullable (.ptr (.raw 24) false 0) else .int, [], 0, Flags.Any, [], 0⟩

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
  -- an address asked for, where only the kernel's choice is modelled
  [.label .highHint, .ins (.movAbs .rdi 0x800000000000)] ++ (mmapCall 16 0x22).drop 1 ++
    [.ins .ud2]

def mapFetch : Fetch := Asm.fetch 0 maps

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

/-! A call through a register needs the register to be a pointer to the
function: holding some number is not enough. -/

def calling : List (Asm Mk) := [.label .make, .ins (.call (.ind (.reg .r12)))]

def callingFetch : Fetch := Asm.fetch 0 calling

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

/-- One integer on the stack; `rdi` a writable record of two integers. -/
def Γ₃ : Ctx where
  regs := fun r => if r = .rdi then .ptr (.raw 16) true 0 else .int
  stack := [.raw 8]
  room := 0
  flags := Flags.Any

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

/-! The order in which owned blocks are listed can be changed: here the
block whose address is in `rbx` is brought to the front, where a call would
take it from. -/

/-- Two owned blocks; `rbx` holds the address of the second. -/
def Γo (p q : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .eq q else .int, [], 0, Flags.Any,
    [(p, .raw 8), (q, .raw 16)], 0⟩

/-! However many blocks a context owns, an address is found in the one it
falls in: here the sixth. -/

/-- Six owned blocks of eight bytes each, the last holding a known value; `rbx` holds the address of the last. -/
def Γ₆ (a b c d e f : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .eq f else .int, [], 0, Flags.Any,
    [(a, .raw 8), (b, .raw 8), (c, .raw 8), (d, .raw 8), (e, .raw 8), (f, ⟨8, [(0, .eq 7)]⟩)], 0⟩

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

/-! The stack is exact to the byte too. A frame of 104 bytes holds a buffer
of 100: once the frame is regarded as those hundred bytes and four more, a
store through an index below 100 is inside the buffer, and one that might
reach byte 100 is refused, though the frame goes on. Inside a piece any
bytes may be read at any offset; across two pieces none may. -/

/-- `rcx` holds exactly `i`, and the stack is the given pieces. -/
def frame (i : BitVec 64) (σ : List Shape) : Ctx :=
  ⟨fun r => if r = .rcx then .eq i else .int, σ, 0, Flags.Any, [], 0⟩

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

/-! ## A loop with nothing said at its head

A label reached only by jumping forward needs no context: what is there is
typed where the jump is made. A label that is jumped back to is the head of
a loop, and must say what holds each time round. -/

inductive Back
  | start | top | out
  deriving DecidableEq

def back : List (Asm Back) := [
  .label .start,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .out,
  .label .top,
  .ins .nop,
  .jmp .top,
  .label .out,
  .ins .ud2]

def backFetch : Fetch := Asm.fetch 0 back

inductive AtBack : Back → Ctx → Prop
  | start : AtBack .start bare

def Φb : CodeTy := .ofLabels back 0 AtBack

/-- A state made by marking eight bytes below such an address writable, with
the stack pointer there. -/
def nowhere : State :=
  (State.init.setPerm (0x0200000000000000 - 8) 8 .rw).setReg .rsp 0x0200000000000000

/-- Sixteen writable bytes, as a program's data might be. -/
def sixteen : State := State.init.setPerm 0x10000 16 .rw

end Rejected
