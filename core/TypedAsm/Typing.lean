import TypedAsm.Types
import TypedAsm.Safety

/-!
# Typing rules

Which instructions are allowed in which contexts, and what the context is
afterwards. An instruction form with no rule here is rejected.

The rules come in two layers. `Straight` covers instructions that always
continue to the next one, and says how they change the context. `HasType`
adds the instructions that transfer control, and checks every possible
successor address against the code typing.

A memory operand is `[register + constant]`, a field of a typed pointer or a
stack slot; `[register + index * scale + constant]`, a field chosen by an
exactly known index; or `[rip + constant]`, a field of a block at a fixed
address. A
whole 8-byte field or slot keeps its type when loaded or stored at 64 bits;
any other access, narrower or inside a field, reads and writes integers.

Every instruction of the machine has a rule. What the rules do not track:
an operation on values that are not exactly known gives a plain integer.
A divide is typed only when it is shown not to raise a divide error, which
needs its operands in registers holding exactly known values.
-/

namespace TypedAsm

/-! ## Subtyping -/

theorem Sub.rfl {τ : Ty} : Sub τ τ := .refl τ

theorem Sub.trans {τ υ φ : Ty} (h₁ : Sub τ υ) (h₂ : Sub υ φ) : Sub τ φ := by
  induction h₂ generalizing τ with
  | refl => exact h₁
  | int => exact .int _
  | readOnly fields w index =>
    cases h₁ with
    | refl => exact .readOnly fields w index
    | readOnly => exact .readOnly fields w index
  | refReadOnly tag w index =>
    cases h₁ with
    | refl => exact .refReadOnly tag w index
    | refReadOnly => exact .refReadOnly tag w index
  | nullable _ ih => exact .nullable (ih h₁)
  | null τ' =>
    cases h₁ with
    | refl => exact .null τ'
  | nullableMono h ih =>
    cases h₁ with
    | refl => exact .nullableMono h
    | nullable h' => exact .nullable (ih h')
    | null => exact .null _
    | nullableMono h' => exact .nullableMono (ih h')
  | orErr _ ih => exact .orErr (ih h₁)
  | orErrMono h ih =>
    cases h₁ with
    | refl => exact .orErrMono h
    | orErr h' => exact .orErr (ih h')
    | orErrMono h' => exact .orErrMono (ih h')

theorem SubList.refl : ∀ σ : List Ty, SubList σ σ
  | [] => .nil
  | τ :: σ => .cons (.refl τ) (SubList.refl σ)

theorem CtxSub.refl (Γ : Ctx) : CtxSub Γ Γ :=
  ⟨fun _ _ => .refl _, .refl _, rfl, fun _ h => h, .refl _⟩

/-- The code at `a` may be entered from a state matching `Γ`: one of the
contexts allowed there is `Γ` or weaker. -/
def Accepts (Φ : CodeTy) (a : BitVec 64) (Γ : Ctx) : Prop :=
  ∃ Δ, Φ a Δ ∧ CtxSub Γ Δ

/-! ## Changing a context -/

def CtxOf.setReg (Γ : Ctx) (r : Reg) (τ : Ty) : Ctx :=
  { Γ with regs := fun r' => if r' = r then τ else Γ.regs r' }

/-- The context after the stack pointer has moved by `d`: what was known of
its value is carried along. -/
def CtxOf.moveSp (Γ : Ctx) (d : BitVec 64) : Ctx :=
  { Γ with regs := fun r => if r = .rsp then (Γ.regs .rsp).shift d else Γ.regs r }

theorem CtxOf.moveSp_regs {Γ : Ctx} {d : BitVec 64} {r : Reg} (hr : r ≠ .rsp) :
    (Γ.moveSp d).regs r = Γ.regs r := by
  simp only [CtxOf.moveSp, hr, ↓reduceIte]

theorem CtxOf.moveSp_sp (Γ : Ctx) (d : BitVec 64) :
    (Γ.moveSp d).regs .rsp = (Γ.regs .rsp).shift d := by
  simp only [CtxOf.moveSp, ↓reduceIte]

/-- Moving by amounts that are equal gives the same type. -/
theorem Sub.shift_congr {τ : Ty} {a b : BitVec 64} (h : a = b) : Sub (τ.shift a) (τ.shift b) :=
  h ▸ .refl _

/-- Comparing a context whose stack pointer has just moved with another. -/
theorem CtxSub.ofMoved {Γ Δ : Ctx} {d : BitVec 64} {stack : List Ty} {room : Nat}
    (hregs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (Δ.regs r)) (hstack : SubList stack Δ.stack)
    (hroom : room = Δ.room) (hflags : ∀ f, Γ.flags f → Δ.flags f)
    (hsp : Sub ((Γ.regs .rsp).shift d) (Δ.regs .rsp)) :
    CtxSub { Γ.moveSp d with stack := stack, room := room } Δ :=
  ⟨fun r hr => by
      show Sub ((Γ.moveSp d).regs r) _
      rw [CtxOf.moveSp_regs hr]
      exact hregs r hr,
    hstack, hroom, hflags, by
      show Sub ((Γ.moveSp d).regs .rsp) _
      rw [CtxOf.moveSp_sp]
      exact hsp⟩

/-- Whether the operation reads the carry flag. -/
def AluOp.readsCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

/-- The result and flags of an operation that does not read the carry flag.
(For the two that do, this is the result with the carry clear.) -/
def AluOp.apply {n : Nat} (op : AluOp) (a b : BitVec n) : BitVec n × Flags :=
  match op with
  | .add | .adc => addCarry a b false
  | .sub | .sbb | .cmp => subBorrow a b false
  | .and => (a &&& b, .ofResult (a &&& b) false false)
  | .or => (a ||| b, .ofResult (a ||| b) false false)
  | .xor => (a ^^^ b, .ofResult (a ^^^ b) false false)

/-- The context after a two-operand operation on register `d`: the flags
become known, and `d` holds an integer if the operation writes it. -/
def CtxOf.afterAlu (Γ : Ctx) (op : AluOp) (d : Reg) : Ctx :=
  { (bif op.writesDst then Γ.setReg d .int else Γ) with flags := Flags.Known }

/-- The context after a system call: the operating system may have changed
`rax`, `rcx`, `r11` and the flags. -/
def CtxOf.afterSyscall (Γ : Ctx) : Ctx :=
  { ((Γ.setReg .rax .int).setReg .rcx .int).setReg .r11 .int with flags := Flags.Any }

/-- The displacement `disp` addresses 8-byte slot `i`. (A structure, not a
definition, so that it is never confused with `innerDisp` by unfolding.) -/
structure slotDisp (i : Nat) (disp : BitVec 32) : Prop where
  eq : disp = BitVec.ofNat 32 (8 * i)
  lt : 8 * i < 2 ^ 31

/-- The displacement `disp` addresses byte `k` of 8-byte slot `i`. -/
structure innerDisp (i k : Nat) (disp : BitVec 32) : Prop where
  eq : disp = BitVec.ofNat 32 (8 * i + k)
  lt : 8 * i + k < 2 ^ 31

/-- The number of bytes in a narrow value. -/
def NarrowW.bytes : NarrowW → Nat
  | .w8 => 1
  | .w16 => 2

/-! ## Operands

Three judgments about an operand, each covering a register, a field of a
block reached through a pointer, and a stack slot. They let one rule serve
every instruction that takes such an operand. `n` is the access size in bytes. -/

/-- `ReadOk Ψ next Γ n rm`: reading `n` bytes from `rm` is safe. For memory, the
bytes must lie inside one field or one stack slot. -/
inductive ReadOk (Ψ : MemTy) (next : BitVec 64) (Γ : Ctx) (n : Nat) : RM → Prop
  | reg (r : Reg) : ReadOk Ψ next Γ n (.reg r)
  | field {b : Reg} {fields : List Ty} {writable : Bool} {off i k : Nat} {disp : BitVec 32}
      {τ : Ty} :
    b ≠ .rsp → Γ.regs b = .ptr fields writable off → innerDisp i k disp →
    fields[off + i]? = some τ → k + n ≤ 8 → ReadOk Ψ next Γ n (.mem (.sib (some b) none disp))
  | slot {i k : Nat} {disp : BitVec 32} {τ : Ty} :
    innerDisp i k disp → Γ.stack[i]? = some τ → k + n ≤ 8 →
    ReadOk Ψ next Γ n (.mem (.sib (some .rsp) none disp))
  /-- An indexed access: the index register holds an exactly known value,
  and scaled and added to the displacement it lands inside a field. -/
  | indexed {b : Reg} {x : IndexReg} {sc : Scale} {fields : List Ty} {writable : Bool}
      {off i k : Nat} {disp : BitVec 32} {c : BitVec 64} {τ : Ty} :
    b ≠ .rsp → Γ.regs b = .ptr fields writable off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 (8 * i + k) →
    fields[off + i]? = some τ → k + n ≤ 8 →
    ReadOk Ψ next Γ n (.mem (.sib (some b) (some (x, sc)) disp))
  /-- A global: bytes inside one field of a block, at a fixed distance from
  the next instruction. -/
  | global {base : BitVec 64} {l : Layout} {i k : Nat} {disp : BitVec 32} {τ : Ty} :
    Ψ base = some l → next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i + k) →
    l.fields[i]? = some τ → k + n ≤ 8 → ReadOk Ψ next Γ n (.mem (.rip disp))

/-- `WriteIntOk Ψ next Γ n rm Γ'`: overwriting `n` bytes of `rm` with an arbitrary
value is safe and leaves a state matching `Γ'`. A register or stack slot
becomes an integer. A field must already be an integer field of a writable
block, since a field's type cannot change. -/
inductive WriteIntOk (Ψ : MemTy) (next : BitVec 64) (Γ : Ctx) (n : Nat) : RM → Ctx → Prop
  | reg {d : Reg} : d ≠ .rsp → WriteIntOk Ψ next Γ n (.reg d) (Γ.setReg d .int)
  | field {b : Reg} {fields : List Ty} {off i k : Nat} {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .ptr fields true off → innerDisp i k disp →
    fields[off + i]? = some .int → k + n ≤ 8 →
    WriteIntOk Ψ next Γ n (.mem (.sib (some b) none disp)) Γ
  | slot {i k : Nat} {disp : BitVec 32} {τ : Ty} :
    innerDisp i k disp → Γ.stack[i]? = some τ → k + n ≤ 8 →
    WriteIntOk Ψ next Γ n (.mem (.sib (some .rsp) none disp)) { Γ with stack := Γ.stack.set i .int }
  | indexed {b : Reg} {x : IndexReg} {sc : Scale} {fields : List Ty} {off i k : Nat}
      {disp : BitVec 32} {c : BitVec 64} :
    b ≠ .rsp → Γ.regs b = .ptr fields true off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 (8 * i + k) →
    fields[off + i]? = some .int → k + n ≤ 8 →
    WriteIntOk Ψ next Γ n (.mem (.sib (some b) (some (x, sc)) disp)) Γ
  | global {base : BitVec 64} {l : Layout} {i k : Nat} {disp : BitVec 32} :
    Ψ base = some l → l.writable = true →
    next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i + k) →
    l.fields[i]? = some .int → k + n ≤ 8 → WriteIntOk Ψ next Γ n (.mem (.rip disp)) Γ

/-- `Holds Ψ next Γ rm τ`: `rm` is a register, a whole field or a whole stack
slot that holds a value of type `τ`. -/
inductive Holds (Ψ : MemTy) (next : BitVec 64) (Γ : Ctx) : RM → Ty → Prop
  | indexed {b : Reg} {x : IndexReg} {sc : Scale} {fields : List Ty} {writable : Bool}
      {off i : Nat} {disp : BitVec 32} {c : BitVec 64} {τ : Ty} :
    b ≠ .rsp → Γ.regs b = .ptr fields writable off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 (8 * i) →
    fields[off + i]? = some τ →
    Holds Ψ next Γ (.mem (.sib (some b) (some (x, sc)) disp)) τ
  | global {base : BitVec 64} {l : Layout} {i : Nat} {disp : BitVec 32} {τ : Ty} :
    Ψ base = some l → next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i) →
    l.fields[i]? = some τ → Holds Ψ next Γ (.mem (.rip disp)) τ
  | reg {r : Reg} {τ : Ty} : r ≠ .rsp → Γ.regs r = τ → Holds Ψ next Γ (.reg r) τ
  | field {b : Reg} {fields : List Ty} {writable : Bool} {off i : Nat} {disp : BitVec 32}
      {τ : Ty} :
    b ≠ .rsp → Γ.regs b = .ptr fields writable off → slotDisp i disp →
    fields[off + i]? = some τ → Holds Ψ next Γ (.mem (.sib (some b) none disp)) τ
  | slot {i : Nat} {disp : BitVec 32} {τ : Ty} :
    slotDisp i disp → Γ.stack[i]? = some τ →
    Holds Ψ next Γ (.mem (.sib (some .rsp) none disp)) τ

/-- At least the named flags are defined. -/
def Flags.Defined (cf zf sf of : Bool) : Flags → Prop :=
  fun f => (cf = true → f.cf.isSome = true) ∧ (zf = true → f.zf.isSome = true) ∧
    (sf = true → f.sf.isSome = true) ∧ (of = true → f.of.isSome = true)

/-- Whether a condition reads only flags among the named ones. -/
def Cond.within (c : Cond) (cf zf sf of : Bool) : Bool :=
  match c with
  | .o | .no => of
  | .b | .ae => cf
  | .e | .ne => zf
  | .be | .a => cf && zf
  | .s | .ns => sf
  | .l | .ge => sf && of
  | .le | .g => zf && sf && of

/-- What is known about the flags after a shift or rotate by `c`, where `c`
has been reduced modulo the operand width. A count of zero leaves them as
they were. Otherwise a shift defines carry, zero and sign, a rotate only
carry, and either defines overflow only for a count of one. -/
def ShiftOp.flagsAfter (op : ShiftOp) (c : Nat) (old : Flags → Prop) : Flags → Prop :=
  if c = 0 then old else
  match op with
  | .shl | .shr | .sar => Flags.Defined true true true (c == 1)
  | .rol | .ror => Flags.Defined true false false (c == 1)

/-- The value a shift or rotate by `c` produces, where `c` has been reduced
modulo the operand width. -/
def ShiftOp.apply {n : Nat} (op : ShiftOp) (a : BitVec n) (c : Nat) : BitVec n :=
  match op with
  | .shl => a <<< c
  | .shr => a >>> c
  | .sar => a.sshiftRight c
  | .rol => a.rotateLeft c
  | .ror => a.rotateRight c

/-- After a multiply, only carry and overflow are defined. -/
abbrev Flags.AfterMul : Flags → Prop := Flags.Defined true false false true

/-- The context after a multiply or divide: `rax` and `rdx` hold the result,
and the flags satisfy `P`. -/
def CtxOf.afterMulDiv (Γ : Ctx) (P : Flags → Prop) : Ctx :=
  { (Γ.setReg .rax .int).setReg .rdx .int with flags := P }

/-! ## Instructions that continue to the next one -/

/-- `Straight Ψ next Γ i Γ'`: in a state matching `Γ`, instruction `i` executes
safely and leaves a state matching `Γ'`. `next` is the address of the
following instruction. The stack pointer is never an explicit destination,
except to allocate or release a frame. -/
inductive Straight (Ψ : MemTy) (next : BitVec 64) : Ctx → Instr → Ctx → Prop
  | nop {Γ : Ctx} : Straight Ψ next Γ .nop Γ
  /-- A 64-bit register copy carries the type along. -/
  | movRR64 {Γ : Ctx} {d s : Reg} : d ≠ .rsp → s ≠ .rsp →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.reg d) s)) (Γ.setReg d (Γ.regs s))
  /-- A 32-bit register copy keeps only the low half, so the result is an integer. -/
  | movRR32 {Γ : Ctx} {d s : Reg} : d ≠ .rsp →
    Straight Ψ next Γ (.mov .w32 (.rm_r (.reg d) s)) (Γ.setReg d .int)
  /-- Loading a constant gives exactly that value. -/
  | movRI {Γ : Ctx} {w : Width} {d : Reg} {imm : BitVec 32} : d ≠ .rsp →
    Straight Ψ next Γ (.mov w (.rm_i (.reg d) imm))
      (Γ.setReg d (.eq ((imm.signExtend w.bits).setWidth 64)))
  | movAbs {Γ : Ctx} {d : Reg} {imm : BitVec 64} : d ≠ .rsp →
    Straight Ψ next Γ (.movAbs d imm) (Γ.setReg d (.eq imm))
  /-- A `rip`-relative `lea` computes a known address: the address of the
  next instruction plus the displacement. -/
  | leaRip {Γ : Ctx} {d : Reg} {disp : BitVec 32} : d ≠ .rsp →
    Straight Ψ next Γ (.lea .w64 d (.rip disp)) (Γ.setReg d (.eq (next + disp.signExtend 64)))
  /-- The address of something on the stack, when the stack pointer's value
  is known. -/
  | leaSp {Γ : Ctx} {d : Reg} {disp : BitVec 32} {v : BitVec 64} :
    d ≠ .rsp → Γ.regs .rsp = .eq v →
    Straight Ψ next Γ (.lea .w64 d (.sib (some .rsp) none disp))
      (Γ.setReg d (.eq (v + disp.signExtend 64)))
  /-- `lea` only computes an address; the result is an integer. -/
  | lea {Γ : Ctx} {w : Width} {d : Reg} {m : Mem} : d ≠ .rsp →
    Straight Ψ next Γ (.lea w d m) (Γ.setReg d .int)
  /-- Load the field `i` slots past where a register points. -/
  | loadField {Γ : Ctx} {d b : Reg} {fields : List Ty} {writable : Bool} {off i : Nat}
      {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr fields writable off → slotDisp i disp →
    fields[off + i]? = some τ →
    Straight Ψ next Γ (.mov .w64 (.r_m d (.sib (some b) none disp))) (Γ.setReg d τ)
  /-- Store into the field `i` slots past where a writable pointer points.
  The stored value must have the field's type. -/
  | storeField {Γ : Ctx} {b s : Reg} {fields : List Ty} {off i : Nat} {disp : BitVec 32}
      {τ : Ty} :
    b ≠ .rsp → s ≠ .rsp → Γ.regs b = .ptr fields true off → slotDisp i disp →
    fields[off + i]? = some τ → Sub (Γ.regs s) τ →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.sib (some b) none disp)) s)) Γ
  /-- Load a whole field through an index, keeping its type. -/
  | loadIndexed {Γ : Ctx} {d b : Reg} {x : IndexReg} {sc : Scale} {fields : List Ty}
      {writable : Bool} {off i : Nat} {disp : BitVec 32} {c : BitVec 64} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr fields writable off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 (8 * i) →
    fields[off + i]? = some τ →
    Straight Ψ next Γ (.mov .w64 (.r_m d (.sib (some b) (some (x, sc)) disp))) (Γ.setReg d τ)
  /-- Store into a whole field through an index. The stored value must have
  the field's type. -/
  | storeIndexed {Γ : Ctx} {b s : Reg} {x : IndexReg} {sc : Scale} {fields : List Ty}
      {off i : Nat} {disp : BitVec 32} {c : BitVec 64} {τ : Ty} :
    b ≠ .rsp → s ≠ .rsp → Γ.regs b = .ptr fields true off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 (8 * i) →
    fields[off + i]? = some τ → Sub (Γ.regs s) τ →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.sib (some b) (some (x, sc)) disp)) s)) Γ
  /-- Load a whole field of a block at a fixed address, keeping its type. -/
  | loadGlobal {Γ : Ctx} {d : Reg} {base : BitVec 64} {l : Layout} {i : Nat} {disp : BitVec 32}
      {τ : Ty} :
    d ≠ .rsp → Ψ base = some l → next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i) →
    l.fields[i]? = some τ → Straight Ψ next Γ (.mov .w64 (.r_m d (.rip disp))) (Γ.setReg d τ)
  /-- Store into a whole field of a writable block at a fixed address. The
  stored value must have the field's type. -/
  | storeGlobal {Γ : Ctx} {s : Reg} {base : BitVec 64} {l : Layout} {i : Nat} {disp : BitVec 32}
      {τ : Ty} :
    s ≠ .rsp → Ψ base = some l → l.writable = true →
    next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i) → l.fields[i]? = some τ →
    Sub (Γ.regs s) τ → Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.rip disp)) s)) Γ
  /-- Load stack slot `i`. -/
  | loadStack {Γ : Ctx} {d : Reg} {i : Nat} {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → slotDisp i disp → Γ.stack[i]? = some τ →
    Straight Ψ next Γ (.mov .w64 (.r_m d (.sib (some .rsp) none disp))) (Γ.setReg d τ)
  /-- Store into stack slot `i`. The slot takes the type of the stored value. -/
  | storeStack {Γ : Ctx} {s : Reg} {i : Nat} {disp : BitVec 32} {τ : Ty} :
    s ≠ .rsp → slotDisp i disp → Γ.stack[i]? = some τ →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none disp)) s))
      { Γ with stack := Γ.stack.set i (Γ.regs s) }
  | push {Γ : Ctx} {r : Reg} {n : Nat} : r ≠ .rsp → Γ.room = n + 1 →
    Straight Ψ next Γ (.push r) { Γ.moveSp (-8) with stack := Γ.regs r :: Γ.stack, room := n }
  | pop {Γ : Ctx} {r : Reg} {τ : Ty} {σ : List Ty} : r ≠ .rsp → Γ.stack = τ :: σ →
    Straight Ψ next Γ (.pop r)
      (CtxOf.setReg { Γ.moveSp 8 with stack := σ, room := Γ.room + 1 } r τ)
  /-- Arithmetic between registers. The result is an integer whatever the operands were. -/
  | aluRR {Γ : Ctx} {op : AluOp} {w : Width} {d s : Reg} :
    d ≠ .rsp → (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.rm_r (.reg d) s)) (Γ.afterAlu op d)
  | aluRI {Γ : Ctx} {op : AluOp} {w : Width} {d : Reg} {imm : BitVec 32} :
    d ≠ .rsp → (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.rm_i (.reg d) imm)) (Γ.afterAlu op d)
  /-- Arithmetic on an exactly known value with a constant: the result and
  the flags are exactly known too. -/
  | aluExact {Γ : Ctx} {op : AluOp} {d : Reg} {imm : BitVec 32} {a : BitVec 64} :
    d ≠ .rsp → Γ.regs d = .eq a → op.readsCarry = false →
    Straight Ψ next Γ (.alu op .w64 (.rm_i (.reg d) imm))
      { (bif op.writesDst then Γ.setReg d (.eq (op.apply a (imm.signExtend 64)).1) else Γ) with
        flags := (· = (op.apply a (imm.signExtend 64)).2) }
  /-- Arithmetic between two exactly known values. -/
  | aluExactRR {Γ : Ctx} {op : AluOp} {d s : Reg} {a b : BitVec 64} :
    d ≠ .rsp → s ≠ .rsp → Γ.regs d = .eq a → Γ.regs s = .eq b → op.readsCarry = false →
    Straight Ψ next Γ (.alu op .w64 (.rm_r (.reg d) s))
      { (bif op.writesDst then Γ.setReg d (.eq (op.apply a b).1) else Γ) with
        flags := (· = (op.apply a b).2) }
  /-- Reserve `k` stack slots. Their contents are unknown, so they are integers. -/
  | allocFrame {Γ : Ctx} {k m : Nat} {imm : BitVec 32} :
    slotDisp k imm → Γ.room = m + k →
    Straight Ψ next Γ (.alu .sub .w64 (.rm_i (.reg .rsp) imm))
      { Γ.moveSp (-BitVec.ofNat 64 (8 * k)) with
        stack := List.replicate k .int ++ Γ.stack, room := m, flags := Flags.Known }
  /-- Release the top `k` stack slots. -/
  | freeFrame {Γ : Ctx} {k : Nat} {imm : BitVec 32} {top rest : List Ty} :
    slotDisp k imm → Γ.stack = top ++ rest → top.length = k →
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm))
      { Γ.moveSp (BitVec.ofNat 64 (8 * k)) with
        stack := rest, room := Γ.room + k, flags := Flags.Known }
  /-- Advancing a pointer by whole slots keeps it a pointer into the same block. -/
  | addPtr {Γ : Ctx} {d : Reg} {fields : List Ty} {writable : Bool} {off k : Nat}
      {imm : BitVec 32} :
    d ≠ .rsp → Γ.regs d = .ptr fields writable off → slotDisp k imm →
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg d) imm))
      { Γ.setReg d (.ptr fields writable (off + k)) with flags := Flags.Known }
  -- The rules below are stated over operands, so each covers registers,
  -- fields and stack slots at once. Where an operand is written, its new
  -- contents are an integer.
  /-- Arithmetic that writes its destination, with a register source. -/
  | aluStoreR {Γ Γ' : Ctx} {op : AluOp} {w : Width} {dst : RM} {s : Reg} :
    op.writesDst = true → ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.rm_r dst s)) { Γ' with flags := Flags.Known }
  /-- Arithmetic that writes its destination, with a constant source. -/
  | aluStoreI {Γ Γ' : Ctx} {op : AluOp} {w : Width} {dst : RM} {imm : BitVec 32} :
    op.writesDst = true → ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.rm_i dst imm)) { Γ' with flags := Flags.Known }
  /-- A comparison with a register. -/
  | cmpR {Γ : Ctx} {op : AluOp} {w : Width} {dst : RM} {s : Reg} :
    op.writesDst = false → ReadOk Ψ next Γ w.bytes.toNat dst →
    Straight Ψ next Γ (.alu op w (.rm_r dst s)) { Γ with flags := Flags.Known }
  /-- A comparison with a constant. -/
  | cmpI {Γ : Ctx} {op : AluOp} {w : Width} {dst : RM} {imm : BitVec 32} :
    op.writesDst = false → ReadOk Ψ next Γ w.bytes.toNat dst →
    Straight Ψ next Γ (.alu op w (.rm_i dst imm)) { Γ with flags := Flags.Known }
  /-- Arithmetic into a register from memory. -/
  | aluLoad {Γ : Ctx} {op : AluOp} {w : Width} {d : Reg} {m : Mem} :
    d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat (.mem m) →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.r_m d m)) (Γ.afterAlu op d)
  | testRM {Γ : Ctx} {w : Width} {dst : RM} {src : RI} : ReadOk Ψ next Γ w.bytes.toNat dst →
    Straight Ψ next Γ (.test w dst src) { Γ with flags := Flags.Known }
  | negRM {Γ Γ' : Ctx} {w : Width} {dst : RM} :
    ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    Straight Ψ next Γ (.unary .neg w dst) { Γ' with flags := Flags.Known }
  /-- `not` leaves the flags alone. -/
  | notRM {Γ Γ' : Ctx} {w : Width} {dst : RM} :
    ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    Straight Ψ next Γ (.unary .not w dst) Γ'
  /-- A shift or rotate by a constant. The count decides which flags are
  defined afterwards. -/
  | shiftImm {Γ Γ' : Ctx} {op : ShiftOp} {w : Width} {dst : RM} {n : BitVec 8} :
    ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    Straight Ψ next Γ (.shift op w dst (.imm n))
      { Γ' with flags := op.flagsAfter (n.toNat % w.bits) Γ.flags }
  /-- A shift or rotate by `cl`. The count may be zero, which leaves the
  flags as they were, so nothing is known about them afterwards. -/
  | shiftCl {Γ Γ' : Ctx} {op : ShiftOp} {w : Width} {dst : RM} :
    ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    Straight Ψ next Γ (.shift op w dst .cl) { Γ' with flags := Flags.Any }
  | mulRM {Γ : Ctx} {w : Width} {src : RM} : ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.mulDiv .mul w src) (Γ.afterMulDiv Flags.AfterMul)
  | imulRM {Γ : Ctx} {w : Width} {src : RM} : ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.mulDiv .imul w src) (Γ.afterMulDiv Flags.AfterMul)
  | imul2RM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.imul2 w d src) { Γ.setReg d .int with flags := Flags.AfterMul }
  | imul3RM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} {imm : BitVec 32} :
    d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.imul3 w d src imm) { Γ.setReg d .int with flags := Flags.AfterMul }
  | popcntRM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.popcnt w d src) { Γ.setReg d .int with flags := Flags.Known }
  | bswap {Γ : Ctx} {w : Width} {r : Reg} : r ≠ .rsp →
    Straight Ψ next Γ (.bswap w r) (Γ.setReg r .int)
  | cdq {Γ : Ctx} : Straight Ψ next Γ .cdq (Γ.setReg .rdx .int)
  | cqo {Γ : Ctx} : Straight Ψ next Γ .cqo (Γ.setReg .rdx .int)
  | movsxdRM {Γ : Ctx} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Ψ next Γ 4 src →
    Straight Ψ next Γ (.movsxd d src) (Γ.setReg d .int)
  /-- A conditional move needs flags that decide the condition. The
  destination is an integer afterwards whichever way it went. -/
  | cmovRM {Γ : Ctx} {c : Cond} {w : Width} {d : Reg} {src : RM} :
    d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat src → (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    Straight Ψ next Γ (.cmov c w d src) (Γ.setReg d .int)
  | setccRM {Γ Γ' : Ctx} {c : Cond} {dst : RM} :
    WriteIntOk Ψ next Γ 1 dst Γ' → (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    Straight Ψ next Γ (.setcc c dst) Γ'
  | movzxRM {Γ : Ctx} {w : Width} {d : Reg} {sw : NarrowW} {src : RM} :
    d ≠ .rsp → ReadOk Ψ next Γ sw.bytes src → Straight Ψ next Γ (.movzx w d sw src) (Γ.setReg d .int)
  | movsxRM {Γ : Ctx} {w : Width} {d : Reg} {sw : NarrowW} {src : RM} :
    d ≠ .rsp → ReadOk Ψ next Γ sw.bytes src → Straight Ψ next Γ (.movsx w d sw src) (Γ.setReg d .int)
  /-- A load of any width, as an integer. The 64-bit loads of a whole field
  or slot above keep its type instead. -/
  | loadInt {Γ : Ctx} {w : Width} {d : Reg} {m : Mem} :
    d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat (.mem m) →
    Straight Ψ next Γ (.mov w (.r_m d m)) (Γ.setReg d .int)
  /-- A store of any width, of a register, treated as an integer. -/
  | storeInt {Γ Γ' : Ctx} {w : Width} {dst : RM} {s : Reg} :
    WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' → Straight Ψ next Γ (.mov w (.rm_r dst s)) Γ'
  /-- A store of a constant. -/
  | storeImm {Γ Γ' : Ctx} {w : Width} {dst : RM} {imm : BitVec 32} :
    WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' → Straight Ψ next Γ (.mov w (.rm_i dst imm)) Γ'
  /-- A byte store. -/
  | store8RM {Γ Γ' : Ctx} {m : Mem} {s : Reg} :
    WriteIntOk Ψ next Γ 1 (.mem m) Γ' → Straight Ψ next Γ (.store8 m s) Γ'
  /-- A 16-bit store. -/
  | store16RM {Γ Γ' : Ctx} {m : Mem} {s : Reg} :
    WriteIntOk Ψ next Γ 2 (.mem m) Γ' → Straight Ψ next Γ (.store16 m s) Γ'
  -- The rules below compute with exactly known values: when every register
  -- an instruction reads holds a known value, so does the one it writes.
  -- At 32 bits a value is cut to its low half first, and the result is
  -- extended with zeros, as the machine does.
  /-- Clearing a register by `xor` with itself. -/
  | xorSelf {Γ : Ctx} {w : Width} {d : Reg} : d ≠ .rsp →
    Straight Ψ next Γ (.alu .xor w (.rm_r (.reg d) d))
      { Γ.setReg d (.eq 0) with flags := (· = Flags.ofResult (0 : BitVec w.bits) false false) }
  | mov32Exact {Γ : Ctx} {d s : Reg} {a : BitVec 64} : d ≠ .rsp → s ≠ .rsp → Γ.regs s = .eq a →
    Straight Ψ next Γ (.mov .w32 (.rm_r (.reg d) s)) (Γ.setReg d (.eq ((a.setWidth 32).setWidth 64)))
  | aluExact32 {Γ : Ctx} {op : AluOp} {d : Reg} {imm : BitVec 32} {a : BitVec 64} :
    d ≠ .rsp → Γ.regs d = .eq a → op.readsCarry = false →
    Straight Ψ next Γ (.alu op .w32 (.rm_i (.reg d) imm))
      { (bif op.writesDst then
          Γ.setReg d (.eq ((op.apply (a.setWidth 32) (imm.signExtend 32)).1.setWidth 64))
        else Γ) with
        flags := (· = (op.apply (a.setWidth 32) (imm.signExtend 32)).2) }
  | aluExactRR32 {Γ : Ctx} {op : AluOp} {d s : Reg} {a b : BitVec 64} :
    d ≠ .rsp → s ≠ .rsp → Γ.regs d = .eq a → Γ.regs s = .eq b → op.readsCarry = false →
    Straight Ψ next Γ (.alu op .w32 (.rm_r (.reg d) s))
      { (bif op.writesDst then
          Γ.setReg d (.eq ((op.apply (a.setWidth 32) (b.setWidth 32)).1.setWidth 64))
        else Γ) with
        flags := (· = (op.apply (a.setWidth 32) (b.setWidth 32)).2) }
  | shiftExact {Γ : Ctx} {op : ShiftOp} {w : Width} {d : Reg} {n : BitVec 8} {a : BitVec 64} :
    d ≠ .rsp → Γ.regs d = .eq a →
    Straight Ψ next Γ (.shift op w (.reg d) (.imm n))
      { Γ.setReg d (.eq ((op.apply (a.setWidth w.bits) (n.toNat % w.bits)).setWidth 64)) with
        flags := op.flagsAfter (n.toNat % w.bits) Γ.flags }
  /-- An address computed from an exactly known base. -/
  | leaExactB {Γ : Ctx} {d b : Reg} {disp : BitVec 32} {a : BitVec 64} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .eq a →
    Straight Ψ next Γ (.lea .w64 d (.sib (some b) none disp))
      (Γ.setReg d (.eq (a + disp.signExtend 64)))
  /-- An address computed from an exactly known base and index. -/
  | leaExactBI {Γ : Ctx} {d b : Reg} {x : IndexReg} {sc : Scale} {disp : BitVec 32}
      {a c : BitVec 64} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .eq a → Γ.regs x.toReg = .eq c →
    Straight Ψ next Γ (.lea .w64 d (.sib (some b) (some (x, sc)) disp))
      (Γ.setReg d (.eq (a + (c <<< sc.shift) + disp.signExtend 64)))
  | negExact {Γ : Ctx} {w : Width} {d : Reg} {a : BitVec 64} : d ≠ .rsp → Γ.regs d = .eq a →
    Straight Ψ next Γ (.unary .neg w (.reg d))
      { Γ.setReg d (.eq ((subBorrow 0 (a.setWidth w.bits) false).1.setWidth 64)) with
        flags := (· = (subBorrow 0 (a.setWidth w.bits) false).2) }
  | notExact {Γ : Ctx} {w : Width} {d : Reg} {a : BitVec 64} : d ≠ .rsp → Γ.regs d = .eq a →
    Straight Ψ next Γ (.unary .not w (.reg d))
      (Γ.setReg d (.eq ((~~~(a.setWidth w.bits)).setWidth 64)))
  | imul2Exact {Γ : Ctx} {w : Width} {d r : Reg} {a b : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs d = .eq a → Γ.regs r = .eq b →
    Straight Ψ next Γ (.imul2 w d (.reg r))
      { Γ.setReg d (.eq ((imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).1.setWidth 64)) with
        flags := (· = (imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).2) }
  | imul3Exact {Γ : Ctx} {w : Width} {d r : Reg} {imm : BitVec 32} {b : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq b →
    Straight Ψ next Γ (.imul3 w d (.reg r) imm)
      { Γ.setReg d (.eq ((imulTrunc (b.setWidth w.bits) (imm.signExtend w.bits)).1.setWidth 64)) with
        flags := (· = (imulTrunc (b.setWidth w.bits) (imm.signExtend w.bits)).2) }
  /-- A multiply or divide of exactly known values that is known to produce
  a result. This is the only rule for a divide: a divide is typed only when
  it is shown not to raise a divide error. -/
  | mulDivExact {Γ : Ctx} {op : MulDivOp} {w : Width} {r : Reg} {a d b : BitVec 64}
      {lo hi : BitVec w.bits} {fl : Flags} :
    r ≠ .rsp → Γ.regs .rax = .eq a → Γ.regs .rdx = .eq d → Γ.regs r = .eq b →
    op.eval (d.setWidth w.bits) (a.setWidth w.bits) (b.setWidth w.bits) = .next (lo, hi, fl) →
    Straight Ψ next Γ (.mulDiv op w (.reg r))
      { (Γ.setReg .rax (.eq (lo.setWidth 64))).setReg .rdx (.eq (hi.setWidth 64)) with
        flags := (· = fl) }
  | cdqExact {Γ : Ctx} {a : BitVec 64} : Γ.regs .rax = .eq a →
    Straight Ψ next Γ .cdq (Γ.setReg .rdx (.eq ((signFill (a.setWidth 32)).setWidth 64)))
  | cqoExact {Γ : Ctx} {a : BitVec 64} : Γ.regs .rax = .eq a →
    Straight Ψ next Γ .cqo (Γ.setReg .rdx (.eq (signFill a)))
  | movsxdExact {Γ : Ctx} {d r : Reg} {a : BitVec 64} : d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.movsxd d (.reg r)) (Γ.setReg d (.eq ((a.setWidth 32).signExtend 64)))
  | movzxExact {Γ : Ctx} {w : Width} {sw : NarrowW} {d r : Reg} {a : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.movzx w d sw (.reg r))
      (Γ.setReg d (.eq (((a.setWidth sw.bits).setWidth w.bits).setWidth 64)))
  | movsxExact {Γ : Ctx} {w : Width} {sw : NarrowW} {d r : Reg} {a : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.movsx w d sw (.reg r))
      (Γ.setReg d (.eq (((a.setWidth sw.bits).signExtend w.bits).setWidth 64)))
  | popcntExact {Γ : Ctx} {w : Width} {d r : Reg} {a : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.popcnt w d (.reg r))
      { Γ.setReg d (.eq ((popcount (a.setWidth w.bits)).setWidth 64)) with
        flags := (· = ⟨some false, some (a.setWidth w.bits == 0), some false, some false⟩) }
  | bswapExact {Γ : Ctx} {w : Width} {r : Reg} {a : BitVec 64} : r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.bswap w r) (Γ.setReg r (.eq ((TypedAsm.bswap w (a.setWidth w.bits)).setWidth 64)))
  /-- A conditional move between exactly known values, when the flags say
  which way it goes. -/
  | cmovExact {Γ : Ctx} {c : Cond} {w : Width} {d r : Reg} {x a : BitVec 64} {b : Bool} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs d = .eq x → Γ.regs r = .eq a →
    (∀ f, Γ.flags f → c.eval f = some b) →
    Straight Ψ next Γ (.cmov c w d (.reg r))
      (Γ.setReg d (.eq ((if b then a.setWidth w.bits else x.setWidth w.bits).setWidth 64)))
  | setccExact {Γ : Ctx} {c : Cond} {d : Reg} {x : BitVec 64} {b : Bool} :
    d ≠ .rsp → Γ.regs d = .eq x → (∀ f, Γ.flags f → c.eval f = some b) →
    Straight Ψ next Γ (.setcc c (.reg d))
      (Γ.setReg d (.eq ((x &&& ~~~0xff) ||| (if b then (1 : BitVec 8) else 0).setWidth 64)))
  /-- Testing two exactly known values gives exactly known flags. -/
  | testExact {Γ : Ctx} {r r' : Reg} {a b : BitVec 64} :
    r ≠ .rsp → r' ≠ .rsp → Γ.regs r = .eq a → Γ.regs r' = .eq b →
    Straight Ψ next Γ (.test .w64 (.reg r) (.reg r'))
      { Γ with flags := (· = Flags.ofResult (a &&& b) false false) }

/-! ## Rules keep holding when the memory typing grows

A rule looks at the memory typing only to find a block at a known address,
and a block that was there still is. -/

theorem ReadOk.ext {Ψ Ψ' : MemTy} {next : BitVec 64} {Γ : Ctx} {n : Nat} {rm : RM}
    (h : ReadOk Ψ next Γ n rm) (he : Ψ.Ext Ψ') : ReadOk Ψ' next Γ n rm := by
  cases h with
  | global hl => apply ReadOk.global (he.blocks _ _ hl) <;> assumption
  | _ =>
    first
    | exact .reg _
    | (apply ReadOk.field <;> assumption)
    | (apply ReadOk.slot <;> assumption)
    | (apply ReadOk.indexed <;> assumption)

theorem WriteIntOk.ext {Ψ Ψ' : MemTy} {next : BitVec 64} {Γ Γ' : Ctx} {n : Nat} {rm : RM}
    (h : WriteIntOk Ψ next Γ n rm Γ') (he : Ψ.Ext Ψ') : WriteIntOk Ψ' next Γ n rm Γ' := by
  cases h with
  | global hl => apply WriteIntOk.global (he.blocks _ _ hl) <;> assumption
  | _ =>
    first
    | (apply WriteIntOk.reg <;> assumption)
    | (apply WriteIntOk.field <;> assumption)
    | (apply WriteIntOk.slot <;> assumption)
    | (apply WriteIntOk.indexed <;> assumption)

theorem Holds.ext {Ψ Ψ' : MemTy} {next : BitVec 64} {Γ : Ctx} {rm : RM} {τ : Ty}
    (h : Holds Ψ next Γ rm τ) (he : Ψ.Ext Ψ') : Holds Ψ' next Γ rm τ := by
  cases h with
  | global hl => apply Holds.global (he.blocks _ _ hl) <;> assumption
  | _ =>
    first
    | (apply Holds.reg <;> assumption)
    | (apply Holds.field <;> assumption)
    | (apply Holds.slot <;> assumption)
    | (apply Holds.indexed <;> assumption)

/-- Closes a premise of a rule being carried to a larger memory typing. -/
local macro "ext_premise" : tactic =>
  `(tactic| first
    | assumption
    | exact ReadOk.ext (by assumption) (by assumption)
    | exact WriteIntOk.ext (by assumption) (by assumption))

/-- Carries a rule, whichever it is, to a larger memory typing. -/
local macro "ext_rule" : tactic =>
  `(tactic| first
    | (apply Straight.nop <;> ext_premise)
    | (apply Straight.movRR64 <;> ext_premise)
    | (apply Straight.movRR32 <;> ext_premise)
    | (apply Straight.movRI <;> ext_premise)
    | (apply Straight.movAbs <;> ext_premise)
    | (apply Straight.leaRip <;> ext_premise)
    | (apply Straight.leaSp <;> ext_premise)
    | (apply Straight.lea <;> ext_premise)
    | (apply Straight.loadField <;> ext_premise)
    | (apply Straight.storeField <;> ext_premise)
    | (apply Straight.loadIndexed <;> ext_premise)
    | (apply Straight.storeIndexed <;> ext_premise)
    | (apply Straight.loadStack <;> ext_premise)
    | (apply Straight.storeStack <;> ext_premise)
    | (apply Straight.push <;> ext_premise)
    | (apply Straight.pop <;> ext_premise)
    | (apply Straight.aluRR <;> ext_premise)
    | (apply Straight.aluRI <;> ext_premise)
    | (apply Straight.aluExact <;> ext_premise)
    | (apply Straight.aluExactRR <;> ext_premise)
    | (apply Straight.allocFrame <;> ext_premise)
    | (apply Straight.freeFrame <;> ext_premise)
    | (apply Straight.addPtr <;> ext_premise)
    | (apply Straight.aluStoreR <;> ext_premise)
    | (apply Straight.aluStoreI <;> ext_premise)
    | (apply Straight.cmpR <;> ext_premise)
    | (apply Straight.cmpI <;> ext_premise)
    | (apply Straight.aluLoad <;> ext_premise)
    | (apply Straight.testRM <;> ext_premise)
    | (apply Straight.negRM <;> ext_premise)
    | (apply Straight.notRM <;> ext_premise)
    | (apply Straight.shiftImm <;> ext_premise)
    | (apply Straight.shiftCl <;> ext_premise)
    | (apply Straight.mulRM <;> ext_premise)
    | (apply Straight.imulRM <;> ext_premise)
    | (apply Straight.imul2RM <;> ext_premise)
    | (apply Straight.imul3RM <;> ext_premise)
    | (apply Straight.popcntRM <;> ext_premise)
    | (apply Straight.bswap <;> ext_premise)
    | (apply Straight.cdq <;> ext_premise)
    | (apply Straight.cqo <;> ext_premise)
    | (apply Straight.movsxdRM <;> ext_premise)
    | (apply Straight.cmovRM <;> ext_premise)
    | (apply Straight.setccRM <;> ext_premise)
    | (apply Straight.movzxRM <;> ext_premise)
    | (apply Straight.movsxRM <;> ext_premise)
    | (apply Straight.loadInt <;> ext_premise)
    | (apply Straight.storeInt <;> ext_premise)
    | (apply Straight.storeImm <;> ext_premise)
    | (apply Straight.store8RM <;> ext_premise)
    | (apply Straight.store16RM <;> ext_premise)
    | (apply Straight.xorSelf <;> ext_premise)
    | (apply Straight.mov32Exact <;> ext_premise)
    | (apply Straight.aluExact32 <;> ext_premise)
    | (apply Straight.aluExactRR32 <;> ext_premise)
    | (apply Straight.shiftExact <;> ext_premise)
    | (apply Straight.leaExactB <;> ext_premise)
    | (apply Straight.leaExactBI <;> ext_premise)
    | (apply Straight.negExact <;> ext_premise)
    | (apply Straight.notExact <;> ext_premise)
    | (apply Straight.imul2Exact <;> ext_premise)
    | (apply Straight.imul3Exact <;> ext_premise)
    | (apply Straight.mulDivExact <;> ext_premise)
    | (apply Straight.cdqExact <;> ext_premise)
    | (apply Straight.cqoExact <;> ext_premise)
    | (apply Straight.movsxdExact <;> ext_premise)
    | (apply Straight.movzxExact <;> ext_premise)
    | (apply Straight.movsxExact <;> ext_premise)
    | (apply Straight.popcntExact <;> ext_premise)
    | (apply Straight.bswapExact <;> ext_premise)
    | (apply Straight.cmovExact <;> ext_premise)
    | (apply Straight.setccExact <;> ext_premise)
    | (apply Straight.testExact <;> ext_premise))

theorem Straight.ext {Ψ Ψ' : MemTy} {next : BitVec 64} {Γ Γ' : Ctx} {i : Instr}
    (h : Straight Ψ next Γ i Γ') (he : Ψ.Ext Ψ') : Straight Ψ' next Γ i Γ' := by
  cases h with
  | loadGlobal hd hl haddr hi => exact .loadGlobal hd (he.blocks _ _ hl) haddr hi
  | storeGlobal hs hl hwr haddr hi hsub => exact .storeGlobal hs (he.blocks _ _ hl) hwr haddr hi hsub
  | _ => ext_rule

/-! ## System calls

What a system call does is up to the operating system, so a `syscall` is
typed by a fact about the operating system at that point in the program. -/

/-- From any state matching `Γ`, the system call returns to where it was made
with a state matching `Γ'`. The memory typing may have grown by then, both
before the call (`Ψ₁`) and because of it (`Ψ₂`): this is how a call that
allocates memory is typed. -/
def SysReturns (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ Γ' : Ctx) : Prop :=
  ∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, WellTyped fetch sys Ψ₁ n Γ s →
    ∃ s', sys s = .next s' ∧ s'.rip = s.rip ∧
      ∃ Ψ₂ : MemTy, Ψ₁.Ext Ψ₂ ∧ Ψ₂.WF ∧ WellTyped fetch sys Ψ₂ n Γ' s'

/-- From any state matching `Γ`, the system call ends the program. -/
def SysExits (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ : Ctx) : Prop :=
  ∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → ∃ c, sys s = .exit c

/-! ## All typed instructions -/

/-- `HasType Φ fetch sys Ψ next Γ i`: in a state matching `Γ`, instruction `i`
executes safely, and wherever control goes next, the code there accepts the
resulting state. `next` is the address of the following instruction. -/
inductive HasType (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (next : BitVec 64) :
    Ctx → Instr → Prop
  | straight {Γ Γ' : Ctx} {i : Instr} : Straight Ψ next Γ i Γ' → Accepts Φ next Γ' → HasType Φ fetch sys Ψ next Γ i
  | jmp {Γ : Ctx} {d : BitVec 32} : Accepts Φ (next + d.signExtend 64) Γ →
    HasType Φ fetch sys Ψ next Γ (.jmp (.rel d))
  /-- A conditional jump needs flags that decide the condition. Each
  successor must accept, and may assume which way the condition went. -/
  | jcc {Γ : Ctx} {c : Cond} {d : BitVec 32} :
    (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    (∀ f, Γ.flags f → c.eval f = some true → Accepts Φ (next + d.signExtend 64) Γ) →
    (∀ f, Γ.flags f → c.eval f = some false → Accepts Φ next Γ) →
    HasType Φ fetch sys Ψ next Γ (.jcc c d)
  /-- A call pushes the return address, typed as a pointer to code expecting
  the context required at the instruction after the call. The callee sees it
  on top of the stack. -/
  | call {Γ ret : Ctx} {d : BitVec 32} {n : Nat} : Γ.room = n + 1 → Φ next ret →
    Accepts Φ (next + d.signExtend 64)
      { Γ.moveSp (-8) with stack := .code ret :: Γ.stack, room := n } →
    HasType Φ fetch sys Ψ next Γ (.call (.rel d))
  /-- A return needs a code pointer on top of the stack, and the state with it
  popped must match what that code requires. -/
  | ret {Γ Δ : Ctx} {σ : List Ty} : Γ.stack = .code Δ :: σ →
    CtxSub { Γ.moveSp 8 with stack := σ, room := Γ.room + 1 } Δ →
    HasType Φ fetch sys Ψ next Γ .ret
  /-- A system call that returns. It is typed only where the operating
  system is shown to return to the next instruction with a state matching
  `Γ'`; there is no rule for a call about which nothing is known. -/
  | syscall {Γ Γ' : Ctx} : SysReturns fetch sys Ψ Γ Γ' → Accepts Φ next Γ' →
    HasType Φ fetch sys Ψ next Γ .syscall
  /-- A system call that ends the program. Nothing after it needs a type. -/
  | syscallExit {Γ : Ctx} : SysExits fetch sys Ψ Γ → HasType Φ fetch sys Ψ next Γ .syscall
  /-- Jump through a register, field or stack slot holding a code pointer. -/
  | jmpInd {Γ Δ : Ctx} {rm : RM} : Holds Ψ next Γ rm (.code Δ) → CtxSub Γ Δ →
    HasType Φ fetch sys Ψ next Γ (.jmp (.ind rm))
  /-- Call through a register, field or stack slot holding a code pointer.
  The callee sees the return address on top of the stack. -/
  | callInd {Γ Δ ret : Ctx} {rm : RM} {n : Nat} : Holds Ψ next Γ rm (.code Δ) → Γ.room = n + 1 → Φ next ret →
    CtxSub { Γ.moveSp (-8) with stack := .code ret :: Γ.stack, room := n } Δ →
    HasType Φ fetch sys Ψ next Γ (.call (.ind rm))
  /-- A register holding exactly the address of a function may be treated as
  a pointer to that function, to be called by any caller. -/
  | fnPtr {Γ : Ctx} {i : Instr} {r : Reg} {a : BitVec 64} {sig : FnSig} :
    r ≠ .rsp → Γ.regs r = .eq a → sig.At Φ a →
    HasType Φ fetch sys Ψ next (Γ.setReg r sig.ty) i → HasType Φ fetch sys Ψ next Γ i
  /-- Call through a register, field or stack slot holding a function
  pointer. The conditions are those of a direct call to that function. -/
  | callFn {Γ ret : Ctx} {rm : RM} {sig : FnSig} {m : Nat} :
    Holds Ψ next Γ rm sig.ty → Γ.room = m + 1 → Φ next ret →
    (∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsIn (Γ.moveSp (-8)).regs r)) →
    Sub ((Γ.regs .rsp).shift (-8)) (sig.regsIn (Γ.moveSp (-8)).regs .rsp) →
    CtxSub (sig.returned (Γ.moveSp (-8)).regs Γ.stack m) ret → sig.need ≤ m →
    HasType Φ fetch sys Ψ next Γ (.call (.ind rm))
  /-- Jump to a function through a pointer to it: a tail call, made on
  behalf of the caller the current function would have returned to. -/
  | jmpFn {Γ ret : Ctx} {rm : RM} {sig : FnSig} {saved : Reg → Ty} {rest : List Ty}
      {room : Nat} :
    Holds Ψ next Γ rm sig.ty → sig.CallerOk saved ret rest room →
    CtxSub Γ (sig.entry saved ret rest room) → HasType Φ fetch sys Ψ next Γ (.jmp (.ind rm))
  /-- Any instruction is well typed in a context no state can match. This is
  how code that is never reached, such as a `ud2` after an impossible branch,
  is typed. -/
  | unreachable {Γ : Ctx} {i : Instr} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, ¬WellTyped fetch sys Ψ₁ n Γ s) →
    HasType Φ fetch sys Ψ next Γ i
  /-- A register holding exactly the address of typed code may be treated as
  a pointer to that code. This is how a code pointer that is not a return
  address comes into being. -/
  | codePtr {Γ Δ : Ctx} {i : Instr} {r : Reg} {a : BitVec 64} :
    r ≠ .rsp → Γ.regs r = .eq a → Φ a Δ →
    HasType Φ fetch sys Ψ next (Γ.setReg r (.code Δ)) i → HasType Φ fetch sys Ψ next Γ i
  /-- Case analysis on the state: if every state matching `Γ` matches one of
  a family of contexts, and the instruction is typed in each of them, it is
  typed in `Γ`. This is how a value that is only known to be an integer gets
  a name: the family has one context for each value it could be. -/
  | cover {ι : Type} {Γ : Ctx} {Γ' : ι → Ctx} {i : Instr} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF →
      ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → ∃ x, WellTyped fetch sys Ψ₁ n (Γ' x) s) →
    (∀ x, HasType Φ fetch sys Ψ next (Γ' x) i) → HasType Φ fetch sys Ψ next Γ i
  /-- The rule of consequence: an instruction typed in `Γ'` is typed in any
  context whose matching states all match `Γ'`. This is the escape from the
  syntactic rules to an arbitrary argument about states. -/
  | weaken {Γ Γ' : Ctx} {i : Instr} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF →
      ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → WellTyped fetch sys Ψ₁ n Γ' s) →
    HasType Φ fetch sys Ψ next Γ' i → HasType Φ fetch sys Ψ next Γ i

/-! ## Programs and states -/

/-- A program is well typed if, for every address and every context the code
typing allows there, the address holds an instruction that is well typed in
that context. -/
def ProgramOk (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) : Prop :=
  ∀ a Γ, Φ a Γ → ∃ i len, fetch a = some (i, len) ∧ HasType Φ fetch sys Ψ (a + len) Γ i

/-- A state is well typed if it matches a context the code typing allows at
its `rip`, at every step count. -/
def StateOk (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (s : State) : Prop :=
  ∃ Γ, Φ s.rip Γ ∧ ∀ n, WellTyped fetch sys Ψ n Γ s

end TypedAsm
