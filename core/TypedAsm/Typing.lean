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

A memory operand is `[register + constant]`: a field of a typed pointer or a
stack slot. A whole 8-byte field or slot keeps its type when loaded or
stored at 64 bits; any other access, narrower or inside a field, reads and
writes integers. Indexed and `rip`-relative data operands have no rule.

Every instruction of the machine has a rule. What the rules do not track:
the results of multiplies, divides, shifts and the like are plain integers,
the flags after a shift are unknown, and a divide is not shown free of a
divide error, which safety permits.
-/

namespace TypedAsm

/-! ## Subtyping -/

/-- `Sub τ υ`: every value of type `τ` also has type `υ`. -/
inductive Sub : Ty → Ty → Prop
  | refl (τ : Ty) : Sub τ τ
  /-- Any value may be treated as an integer. -/
  | int (τ : Ty) : Sub τ .int
  /-- A writable pointer may be used as a read-only one. -/
  | readOnly (fields : List Ty) (writable : Bool) (index : Nat) :
    Sub (.ptr fields true index) (.ptr fields writable index)

/-- Subtyping slot by slot, for two stacks of the same length. -/
inductive SubList : List Ty → List Ty → Prop
  | nil : SubList [] []
  | cons {τ υ : Ty} {σ ρ : List Ty} : Sub τ υ → SubList σ ρ → SubList (τ :: σ) (υ :: ρ)

/-- `CtxSub Γ Δ`: every state matching `Γ` also matches `Δ`. The stack shape
and room must agree exactly; only the types of registers and slots may be weakened. -/
structure CtxSub (Γ Δ : Ctx) : Prop where
  regs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (Δ.regs r)
  stack : SubList Γ.stack Δ.stack
  room : Γ.room = Δ.room
  flags : ∀ f, Γ.flags f → Δ.flags f

theorem Sub.rfl {τ : Ty} : Sub τ τ := .refl τ

theorem Sub.trans {τ υ φ : Ty} (h₁ : Sub τ υ) (h₂ : Sub υ φ) : Sub τ φ := by
  cases h₁ with
  | refl => exact h₂
  | int => cases h₂ <;> exact .int _
  | readOnly fields w index =>
    cases h₂ with
    | refl => exact .readOnly fields w index
    | int => exact .int _
    | readOnly => exact .readOnly fields _ index

theorem SubList.refl : ∀ σ : List Ty, SubList σ σ
  | [] => .nil
  | τ :: σ => .cons (.refl τ) (SubList.refl σ)

theorem CtxSub.refl (Γ : Ctx) : CtxSub Γ Γ :=
  ⟨fun _ _ => .refl _, .refl _, rfl, fun _ h => h⟩

/-- The code at `a` may be entered from a state matching `Γ`: one of the
contexts allowed there is `Γ` or weaker. -/
def Accepts (Φ : CodeTy) (a : BitVec 64) (Γ : Ctx) : Prop :=
  ∃ Δ, Φ a Δ ∧ CtxSub Γ Δ

/-! ## Changing a context -/

def CtxOf.setReg (Γ : Ctx) (r : Reg) (τ : Ty) : Ctx :=
  { Γ with regs := fun r' => if r' = r then τ else Γ.regs r' }

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

/-- `ReadOk Γ n rm`: reading `n` bytes from `rm` is safe. For memory, the
bytes must lie inside one field or one stack slot. -/
inductive ReadOk (Γ : Ctx) (n : Nat) : RM → Prop
  | reg (r : Reg) : ReadOk Γ n (.reg r)
  | field {b : Reg} {fields : List Ty} {writable : Bool} {off i k : Nat} {disp : BitVec 32}
      {τ : Ty} :
    b ≠ .rsp → Γ.regs b = .ptr fields writable off → innerDisp i k disp →
    fields[off + i]? = some τ → k + n ≤ 8 → ReadOk Γ n (.mem (.sib (some b) none disp))
  | slot {i k : Nat} {disp : BitVec 32} {τ : Ty} :
    innerDisp i k disp → Γ.stack[i]? = some τ → k + n ≤ 8 →
    ReadOk Γ n (.mem (.sib (some .rsp) none disp))

/-- `WriteIntOk Γ n rm Γ'`: overwriting `n` bytes of `rm` with an arbitrary
value is safe and leaves a state matching `Γ'`. A register or stack slot
becomes an integer. A field must already be an integer field of a writable
block, since a field's type cannot change. -/
inductive WriteIntOk (Γ : Ctx) (n : Nat) : RM → Ctx → Prop
  | reg {d : Reg} : d ≠ .rsp → WriteIntOk Γ n (.reg d) (Γ.setReg d .int)
  | field {b : Reg} {fields : List Ty} {off i k : Nat} {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .ptr fields true off → innerDisp i k disp →
    fields[off + i]? = some .int → k + n ≤ 8 →
    WriteIntOk Γ n (.mem (.sib (some b) none disp)) Γ
  | slot {i k : Nat} {disp : BitVec 32} {τ : Ty} :
    innerDisp i k disp → Γ.stack[i]? = some τ → k + n ≤ 8 →
    WriteIntOk Γ n (.mem (.sib (some .rsp) none disp)) { Γ with stack := Γ.stack.set i .int }

/-- `CodeAt Γ rm Δ`: `rm` holds a pointer to code that expects `Δ`. -/
inductive CodeAt (Γ : Ctx) : RM → Ctx → Prop
  | reg {r : Reg} {Δ : Ctx} : r ≠ .rsp → Γ.regs r = .code Δ → CodeAt Γ (.reg r) Δ
  | field {b : Reg} {fields : List Ty} {writable : Bool} {off i : Nat} {disp : BitVec 32}
      {Δ : Ctx} :
    b ≠ .rsp → Γ.regs b = .ptr fields writable off → slotDisp i disp →
    fields[off + i]? = some (.code Δ) → CodeAt Γ (.mem (.sib (some b) none disp)) Δ
  | slot {i : Nat} {disp : BitVec 32} {Δ : Ctx} :
    slotDisp i disp → Γ.stack[i]? = some (.code Δ) →
    CodeAt Γ (.mem (.sib (some .rsp) none disp)) Δ

/-- The two instructions that can raise a divide error. -/
def Instr.isDivide : Instr → Bool
  | .mulDiv .div _ _ => true
  | .mulDiv .idiv _ _ => true
  | _ => false

/-- The context after a multiply or divide: `rax` and `rdx` hold the result,
and the flags are not all defined. -/
def CtxOf.afterMulDiv (Γ : Ctx) : Ctx :=
  { (Γ.setReg .rax .int).setReg .rdx .int with flags := Flags.Any }

/-! ## Instructions that continue to the next one -/

/-- `Straight next Γ i Γ'`: in a state matching `Γ`, instruction `i` executes
safely and leaves a state matching `Γ'`. `next` is the address of the
following instruction. The stack pointer is never an explicit destination,
except to allocate or release a frame. -/
inductive Straight (next : BitVec 64) : Ctx → Instr → Ctx → Prop
  | nop {Γ : Ctx} : Straight next Γ .nop Γ
  /-- A 64-bit register copy carries the type along. -/
  | movRR64 {Γ : Ctx} {d s : Reg} : d ≠ .rsp → s ≠ .rsp →
    Straight next Γ (.mov .w64 (.rm_r (.reg d) s)) (Γ.setReg d (Γ.regs s))
  /-- A 32-bit register copy keeps only the low half, so the result is an integer. -/
  | movRR32 {Γ : Ctx} {d s : Reg} : d ≠ .rsp →
    Straight next Γ (.mov .w32 (.rm_r (.reg d) s)) (Γ.setReg d .int)
  /-- Loading a constant gives exactly that value. -/
  | movRI {Γ : Ctx} {w : Width} {d : Reg} {imm : BitVec 32} : d ≠ .rsp →
    Straight next Γ (.mov w (.rm_i (.reg d) imm))
      (Γ.setReg d (.eq ((imm.signExtend w.bits).setWidth 64)))
  | movAbs {Γ : Ctx} {d : Reg} {imm : BitVec 64} : d ≠ .rsp →
    Straight next Γ (.movAbs d imm) (Γ.setReg d (.eq imm))
  /-- A `rip`-relative `lea` computes a known address: the address of the
  next instruction plus the displacement. -/
  | leaRip {Γ : Ctx} {d : Reg} {disp : BitVec 32} : d ≠ .rsp →
    Straight next Γ (.lea .w64 d (.rip disp)) (Γ.setReg d (.eq (next + disp.signExtend 64)))
  /-- `lea` only computes an address; the result is an integer. -/
  | lea {Γ : Ctx} {w : Width} {d : Reg} {m : Mem} : d ≠ .rsp →
    Straight next Γ (.lea w d m) (Γ.setReg d .int)
  /-- Load the field `i` slots past where a register points. -/
  | loadField {Γ : Ctx} {d b : Reg} {fields : List Ty} {writable : Bool} {off i : Nat}
      {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr fields writable off → slotDisp i disp →
    fields[off + i]? = some τ →
    Straight next Γ (.mov .w64 (.r_m d (.sib (some b) none disp))) (Γ.setReg d τ)
  /-- Store into the field `i` slots past where a writable pointer points.
  The stored value must have the field's type. -/
  | storeField {Γ : Ctx} {b s : Reg} {fields : List Ty} {off i : Nat} {disp : BitVec 32}
      {τ : Ty} :
    b ≠ .rsp → s ≠ .rsp → Γ.regs b = .ptr fields true off → slotDisp i disp →
    fields[off + i]? = some τ → Sub (Γ.regs s) τ →
    Straight next Γ (.mov .w64 (.rm_r (.mem (.sib (some b) none disp)) s)) Γ
  /-- A 32- or 64-bit store of a register into an integer field. Any value
  may be written, because any value is an integer. -/
  | storeIntR {Γ : Ctx} {w : Width} {b s : Reg} {fields : List Ty} {off i k : Nat}
      {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .ptr fields true off → innerDisp i k disp →
    fields[off + i]? = some .int → k + w.bytes.toNat ≤ 8 →
    Straight next Γ (.mov w (.rm_r (.mem (.sib (some b) none disp)) s)) Γ
  /-- A 32- or 64-bit store of a constant into an integer field. -/
  | storeIntI {Γ : Ctx} {w : Width} {b : Reg} {fields : List Ty} {off i k : Nat}
      {disp imm : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .ptr fields true off → innerDisp i k disp →
    fields[off + i]? = some .int → k + w.bytes.toNat ≤ 8 →
    Straight next Γ (.mov w (.rm_i (.mem (.sib (some b) none disp)) imm)) Γ
  /-- A byte store into an integer field. -/
  | store8Field {Γ : Ctx} {b s : Reg} {fields : List Ty} {off i k : Nat} {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .ptr fields true off → innerDisp i k disp →
    fields[off + i]? = some .int → k + 1 ≤ 8 →
    Straight next Γ (.store8 (.sib (some b) none disp) s) Γ
  /-- Load stack slot `i`. -/
  | loadStack {Γ : Ctx} {d : Reg} {i : Nat} {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → slotDisp i disp → Γ.stack[i]? = some τ →
    Straight next Γ (.mov .w64 (.r_m d (.sib (some .rsp) none disp))) (Γ.setReg d τ)
  /-- Store into stack slot `i`. The slot takes the type of the stored value. -/
  | storeStack {Γ : Ctx} {s : Reg} {i : Nat} {disp : BitVec 32} {τ : Ty} :
    s ≠ .rsp → slotDisp i disp → Γ.stack[i]? = some τ →
    Straight next Γ (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none disp)) s))
      { Γ with stack := Γ.stack.set i (Γ.regs s) }
  | push {Γ : Ctx} {r : Reg} {n : Nat} : r ≠ .rsp → Γ.room = n + 1 →
    Straight next Γ (.push r) { Γ with stack := Γ.regs r :: Γ.stack, room := n }
  | pop {Γ : Ctx} {r : Reg} {τ : Ty} {σ : List Ty} : r ≠ .rsp → Γ.stack = τ :: σ →
    Straight next Γ (.pop r) (CtxOf.setReg { Γ with stack := σ, room := Γ.room + 1 } r τ)
  /-- Arithmetic between registers. The result is an integer whatever the operands were. -/
  | aluRR {Γ : Ctx} {op : AluOp} {w : Width} {d s : Reg} :
    d ≠ .rsp → (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight next Γ (.alu op w (.rm_r (.reg d) s)) (Γ.afterAlu op d)
  | aluRI {Γ : Ctx} {op : AluOp} {w : Width} {d : Reg} {imm : BitVec 32} :
    d ≠ .rsp → (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight next Γ (.alu op w (.rm_i (.reg d) imm)) (Γ.afterAlu op d)
  /-- Arithmetic with a field of a block as the source. -/
  | aluMem {Γ : Ctx} {op : AluOp} {d b : Reg} {fields : List Ty} {writable : Bool}
      {off i : Nat} {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr fields writable off → slotDisp i disp →
    fields[off + i]? = some τ → (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight next Γ (.alu op .w64 (.r_m d (.sib (some b) none disp))) (Γ.afterAlu op d)
  /-- Arithmetic on an exactly known value with a constant: the result and
  the flags are exactly known too. -/
  | aluExact {Γ : Ctx} {op : AluOp} {d : Reg} {imm : BitVec 32} {a : BitVec 64} :
    d ≠ .rsp → Γ.regs d = .eq a → op.readsCarry = false →
    Straight next Γ (.alu op .w64 (.rm_i (.reg d) imm))
      { (bif op.writesDst then Γ.setReg d (.eq (op.apply a (imm.signExtend 64)).1) else Γ) with
        flags := (· = (op.apply a (imm.signExtend 64)).2) }
  /-- Arithmetic between two exactly known values. -/
  | aluExactRR {Γ : Ctx} {op : AluOp} {d s : Reg} {a b : BitVec 64} :
    d ≠ .rsp → s ≠ .rsp → Γ.regs d = .eq a → Γ.regs s = .eq b → op.readsCarry = false →
    Straight next Γ (.alu op .w64 (.rm_r (.reg d) s))
      { (bif op.writesDst then Γ.setReg d (.eq (op.apply a b).1) else Γ) with
        flags := (· = (op.apply a b).2) }
  /-- Reserve `k` stack slots. Their contents are unknown, so they are integers. -/
  | allocFrame {Γ : Ctx} {k m : Nat} {imm : BitVec 32} :
    slotDisp k imm → Γ.room = m + k →
    Straight next Γ (.alu .sub .w64 (.rm_i (.reg .rsp) imm))
      { Γ with stack := List.replicate k .int ++ Γ.stack, room := m, flags := Flags.Known }
  /-- Release the top `k` stack slots. -/
  | freeFrame {Γ : Ctx} {k : Nat} {imm : BitVec 32} {top rest : List Ty} :
    slotDisp k imm → Γ.stack = top ++ rest → top.length = k →
    Straight next Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm))
      { Γ with stack := rest, room := Γ.room + k, flags := Flags.Known }
  /-- A 32-bit load from inside a field. The result is an integer whatever the field holds. -/
  | loadField32 {Γ : Ctx} {d b : Reg} {fields : List Ty} {writable : Bool} {off i k : Nat}
      {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr fields writable off → innerDisp i k disp →
    fields[off + i]? = some τ → k + 4 ≤ 8 →
    Straight next Γ (.mov .w32 (.r_m d (.sib (some b) none disp))) (Γ.setReg d .int)
  /-- A zero-extending 8- or 16-bit load from inside a field. -/
  | movzxField {Γ : Ctx} {w : Width} {sw : NarrowW} {d b : Reg} {fields : List Ty}
      {writable : Bool} {off i k : Nat} {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr fields writable off → innerDisp i k disp →
    fields[off + i]? = some τ → k + sw.bytes ≤ 8 →
    Straight next Γ (.movzx w d sw (.mem (.sib (some b) none disp))) (Γ.setReg d .int)
  /-- A sign-extending 8- or 16-bit load from inside a field. -/
  | movsxField {Γ : Ctx} {w : Width} {sw : NarrowW} {d b : Reg} {fields : List Ty}
      {writable : Bool} {off i k : Nat} {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr fields writable off → innerDisp i k disp →
    fields[off + i]? = some τ → k + sw.bytes ≤ 8 →
    Straight next Γ (.movsx w d sw (.mem (.sib (some b) none disp))) (Γ.setReg d .int)
  /-- Advancing a pointer by whole slots keeps it a pointer into the same block. -/
  | addPtr {Γ : Ctx} {d : Reg} {fields : List Ty} {writable : Bool} {off k : Nat}
      {imm : BitVec 32} :
    d ≠ .rsp → Γ.regs d = .ptr fields writable off → slotDisp k imm →
    Straight next Γ (.alu .add .w64 (.rm_i (.reg d) imm))
      { Γ.setReg d (.ptr fields writable (off + k)) with flags := Flags.Known }
  -- The rules below are stated over operands, so each covers registers,
  -- fields and stack slots at once. Where an operand is written, its new
  -- contents are an integer.
  /-- Arithmetic that writes its destination, with a register source. -/
  | aluStoreR {Γ Γ' : Ctx} {op : AluOp} {w : Width} {dst : RM} {s : Reg} :
    op.writesDst = true → ReadOk Γ w.bytes.toNat dst → WriteIntOk Γ w.bytes.toNat dst Γ' →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight next Γ (.alu op w (.rm_r dst s)) { Γ' with flags := Flags.Known }
  /-- Arithmetic that writes its destination, with a constant source. -/
  | aluStoreI {Γ Γ' : Ctx} {op : AluOp} {w : Width} {dst : RM} {imm : BitVec 32} :
    op.writesDst = true → ReadOk Γ w.bytes.toNat dst → WriteIntOk Γ w.bytes.toNat dst Γ' →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight next Γ (.alu op w (.rm_i dst imm)) { Γ' with flags := Flags.Known }
  /-- A comparison with a register. -/
  | cmpR {Γ : Ctx} {op : AluOp} {w : Width} {dst : RM} {s : Reg} :
    op.writesDst = false → ReadOk Γ w.bytes.toNat dst →
    Straight next Γ (.alu op w (.rm_r dst s)) { Γ with flags := Flags.Known }
  /-- A comparison with a constant. -/
  | cmpI {Γ : Ctx} {op : AluOp} {w : Width} {dst : RM} {imm : BitVec 32} :
    op.writesDst = false → ReadOk Γ w.bytes.toNat dst →
    Straight next Γ (.alu op w (.rm_i dst imm)) { Γ with flags := Flags.Known }
  /-- Arithmetic into a register from memory. -/
  | aluLoad {Γ : Ctx} {op : AluOp} {w : Width} {d : Reg} {m : Mem} :
    d ≠ .rsp → ReadOk Γ w.bytes.toNat (.mem m) →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight next Γ (.alu op w (.r_m d m)) (Γ.afterAlu op d)
  | testRM {Γ : Ctx} {w : Width} {dst : RM} {src : RI} : ReadOk Γ w.bytes.toNat dst →
    Straight next Γ (.test w dst src) { Γ with flags := Flags.Known }
  | negRM {Γ Γ' : Ctx} {w : Width} {dst : RM} :
    ReadOk Γ w.bytes.toNat dst → WriteIntOk Γ w.bytes.toNat dst Γ' →
    Straight next Γ (.unary .neg w dst) { Γ' with flags := Flags.Known }
  /-- `not` leaves the flags alone. -/
  | notRM {Γ Γ' : Ctx} {w : Width} {dst : RM} :
    ReadOk Γ w.bytes.toNat dst → WriteIntOk Γ w.bytes.toNat dst Γ' →
    Straight next Γ (.unary .not w dst) Γ'
  /-- A shift or rotate. Afterwards nothing is known about the flags: some
  are undefined, and a count of zero leaves them as they were. -/
  | shiftRM {Γ Γ' : Ctx} {op : ShiftOp} {w : Width} {dst : RM} {c : Count} :
    ReadOk Γ w.bytes.toNat dst → WriteIntOk Γ w.bytes.toNat dst Γ' →
    Straight next Γ (.shift op w dst c) { Γ' with flags := Flags.Any }
  | mulRM {Γ : Ctx} {w : Width} {src : RM} : ReadOk Γ w.bytes.toNat src →
    Straight next Γ (.mulDiv .mul w src) Γ.afterMulDiv
  | imulRM {Γ : Ctx} {w : Width} {src : RM} : ReadOk Γ w.bytes.toNat src →
    Straight next Γ (.mulDiv .imul w src) Γ.afterMulDiv
  /-- A divide may raise a divide error, which is an acceptable outcome; if
  it does not, execution continues. -/
  | divRM {Γ : Ctx} {w : Width} {src : RM} : ReadOk Γ w.bytes.toNat src →
    Straight next Γ (.mulDiv .div w src) Γ.afterMulDiv
  | idivRM {Γ : Ctx} {w : Width} {src : RM} : ReadOk Γ w.bytes.toNat src →
    Straight next Γ (.mulDiv .idiv w src) Γ.afterMulDiv
  | imul2RM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Γ w.bytes.toNat src →
    Straight next Γ (.imul2 w d src) { Γ.setReg d .int with flags := Flags.Any }
  | imul3RM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} {imm : BitVec 32} :
    d ≠ .rsp → ReadOk Γ w.bytes.toNat src →
    Straight next Γ (.imul3 w d src imm) { Γ.setReg d .int with flags := Flags.Any }
  | popcntRM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Γ w.bytes.toNat src →
    Straight next Γ (.popcnt w d src) { Γ.setReg d .int with flags := Flags.Known }
  | bswap {Γ : Ctx} {w : Width} {r : Reg} : r ≠ .rsp →
    Straight next Γ (.bswap w r) (Γ.setReg r .int)
  | cdq {Γ : Ctx} : Straight next Γ .cdq (Γ.setReg .rdx .int)
  | cqo {Γ : Ctx} : Straight next Γ .cqo (Γ.setReg .rdx .int)
  | movsxdRM {Γ : Ctx} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Γ 4 src →
    Straight next Γ (.movsxd d src) (Γ.setReg d .int)
  /-- A conditional move needs flags that decide the condition. The
  destination is an integer afterwards whichever way it went. -/
  | cmovRM {Γ : Ctx} {c : Cond} {w : Width} {d : Reg} {src : RM} :
    d ≠ .rsp → ReadOk Γ w.bytes.toNat src → (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    Straight next Γ (.cmov c w d src) (Γ.setReg d .int)
  | setccRM {Γ Γ' : Ctx} {c : Cond} {dst : RM} :
    WriteIntOk Γ 1 dst Γ' → (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    Straight next Γ (.setcc c dst) Γ'
  | movzxRM {Γ : Ctx} {w : Width} {d : Reg} {sw : NarrowW} {src : RM} :
    d ≠ .rsp → ReadOk Γ sw.bytes src → Straight next Γ (.movzx w d sw src) (Γ.setReg d .int)
  | movsxRM {Γ : Ctx} {w : Width} {d : Reg} {sw : NarrowW} {src : RM} :
    d ≠ .rsp → ReadOk Γ sw.bytes src → Straight next Γ (.movsx w d sw src) (Γ.setReg d .int)
  /-- A load of any width, as an integer. The 64-bit loads of a whole field
  or slot above keep its type instead. -/
  | loadInt {Γ : Ctx} {w : Width} {d : Reg} {m : Mem} :
    d ≠ .rsp → ReadOk Γ w.bytes.toNat (.mem m) →
    Straight next Γ (.mov w (.r_m d m)) (Γ.setReg d .int)
  /-- A store of any width, of a register, treated as an integer. -/
  | storeInt {Γ Γ' : Ctx} {w : Width} {dst : RM} {s : Reg} :
    WriteIntOk Γ w.bytes.toNat dst Γ' → Straight next Γ (.mov w (.rm_r dst s)) Γ'
  /-- A store of a constant. -/
  | storeImm {Γ Γ' : Ctx} {w : Width} {dst : RM} {imm : BitVec 32} :
    WriteIntOk Γ w.bytes.toNat dst Γ' → Straight next Γ (.mov w (.rm_i dst imm)) Γ'
  /-- A byte store. -/
  | store8RM {Γ Γ' : Ctx} {m : Mem} {s : Reg} :
    WriteIntOk Γ 1 (.mem m) Γ' → Straight next Γ (.store8 m s) Γ'
  | test {Γ : Ctx} {w : Width} {r : Reg} {src : RI} :
    Straight next Γ (.test w (.reg r) src) { Γ with flags := Flags.Known }
  /-- Testing two exactly known values gives exactly known flags. -/
  | testExact {Γ : Ctx} {r r' : Reg} {a b : BitVec 64} :
    r ≠ .rsp → r' ≠ .rsp → Γ.regs r = .eq a → Γ.regs r' = .eq b →
    Straight next Γ (.test .w64 (.reg r) (.reg r'))
      { Γ with flags := (· = Flags.ofResult (a &&& b) false false) }

/-! ## All typed instructions -/

/-- `HasType Φ fetch sys Ψ next Γ i`: in a state matching `Γ`, instruction `i`
executes safely, and wherever control goes next, the code there accepts the
resulting state. `next` is the address of the following instruction. -/
inductive HasType (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (next : BitVec 64) :
    Ctx → Instr → Prop
  | straight {Γ Γ' : Ctx} {i : Instr} : Straight next Γ i Γ' → Accepts Φ next Γ' → HasType Φ fetch sys Ψ next Γ i
  | jmp {Γ : Ctx} {d : BitVec 32} : Accepts Φ (next + d.signExtend 64) Γ →
    HasType Φ fetch sys Ψ next Γ (.jmp (.rel d))
  /-- A conditional jump needs flags that decide the condition. Each
  successor must accept, and may assume which way the condition went. -/
  | jcc {Γ : Ctx} {c : Cond} {d : BitVec 32} :
    (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    (∀ f, Γ.flags f → c.eval f = some true → Accepts Φ (next + d.signExtend 64) Γ) →
    (∀ f, Γ.flags f → c.eval f = some false → Accepts Φ next Γ) →
    HasType Φ fetch sys Ψ next Γ (.jcc c d)
  /-- Jump through a register holding a code pointer. -/
  | jmpReg {Γ Δ : Ctx} {r : Reg} : r ≠ .rsp → Γ.regs r = .code Δ → CtxSub Γ Δ →
    HasType Φ fetch sys Ψ next Γ (.jmp (.ind (.reg r)))
  /-- A call pushes the return address, typed as a pointer to code expecting
  the context required at the instruction after the call. The callee sees it
  on top of the stack. -/
  | call {Γ ret : Ctx} {d : BitVec 32} {n : Nat} : Γ.room = n + 1 → Φ next ret →
    Accepts Φ (next + d.signExtend 64) { Γ with stack := .code ret :: Γ.stack, room := n } →
    HasType Φ fetch sys Ψ next Γ (.call (.rel d))
  /-- A return needs a code pointer on top of the stack, and the state with it
  popped must match what that code requires. -/
  | ret {Γ Δ : Ctx} {σ : List Ty} : Γ.stack = .code Δ :: σ →
    CtxSub { Γ with stack := σ, room := Γ.room + 1 } Δ → HasType Φ fetch sys Ψ next Γ .ret
  | syscall {Γ : Ctx} : Accepts Φ next Γ.afterSyscall → HasType Φ fetch sys Ψ next Γ .syscall
  /-- Jump through a register, field or stack slot holding a code pointer. -/
  | jmpInd {Γ Δ : Ctx} {rm : RM} : CodeAt Γ rm Δ → CtxSub Γ Δ →
    HasType Φ fetch sys Ψ next Γ (.jmp (.ind rm))
  /-- Call through a register, field or stack slot holding a code pointer.
  The callee sees the return address on top of the stack. -/
  | callInd {Γ Δ ret : Ctx} {rm : RM} {n : Nat} : CodeAt Γ rm Δ → Γ.room = n + 1 → Φ next ret →
    CtxSub { Γ with stack := .code ret :: Γ.stack, room := n } Δ →
    HasType Φ fetch sys Ψ next Γ (.call (.ind rm))
  /-- Any instruction is well typed in a context no state can match. This is
  how code that is never reached, such as a `ud2` after an impossible branch,
  is typed. -/
  | unreachable {Γ : Ctx} {i : Instr} : (∀ n s, ¬WellTyped fetch sys Ψ n Γ s) →
    HasType Φ fetch sys Ψ next Γ i
  /-- A register holding exactly the address of typed code may be treated as
  a pointer to that code. This is how a code pointer that is not a return
  address comes into being. -/
  | codePtr {Γ Δ : Ctx} {i : Instr} {r : Reg} {a : BitVec 64} :
    r ≠ .rsp → Γ.regs r = .eq a → Φ a Δ →
    HasType Φ fetch sys Ψ next (Γ.setReg r (.code Δ)) i → HasType Φ fetch sys Ψ next Γ i
  /-- The rule of consequence: an instruction typed in `Γ'` is typed in any
  context whose matching states all match `Γ'`. This is the escape from the
  syntactic rules to an arbitrary argument about states. -/
  | weaken {Γ Γ' : Ctx} {i : Instr} :
    (∀ n s, WellTyped fetch sys Ψ n Γ s → WellTyped fetch sys Ψ n Γ' s) →
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

/-- What the type system assumes about the operating system: a system call
from a well-typed state has an acceptable outcome, and if it returns, it
returns to the same place with a state that is still well typed, having
changed at most `rax`, `rcx`, `r11` and the flags as far as types can tell. -/
def SysOk (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) : Prop :=
  ∀ n Γ s, WellTyped fetch sys Ψ n Γ s →
    (sys s).isSafe = true ∧
    ∀ s', sys s = .next s' → s'.rip = s.rip ∧ WellTyped fetch sys Ψ n Γ.afterSyscall s'

end TypedAsm
