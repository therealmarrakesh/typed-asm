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

Field and stack-slot accesses are 64-bit and at fixed offsets.
-/

namespace TypedAsm

/-! ## Subtyping -/

/-- `Sub τ υ`: every value of type `τ` also has type `υ`. -/
inductive Sub : Ty → Ty → Prop
  | refl (τ : Ty) : Sub τ τ
  /-- Any value may be treated as an integer. -/
  | int (τ : Ty) : Sub τ .int
  /-- A writable pointer may be used as a read-only one. -/
  | readOnly (fields : List Ty) (writable : Bool) : Sub (.ptr fields true) (.ptr fields writable)

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
  flags : Δ.flags = true → Γ.flags = true

/-- The code at `a` may be entered from a state matching `Γ`. -/
def Accepts (Φ : CodeTy) (a : BitVec 64) (Γ : Ctx) : Prop :=
  ∃ Δ, Φ a = some Δ ∧ CtxSub Γ Δ

/-! ## Changing a context -/

def CtxOf.setReg (Γ : Ctx) (r : Reg) (τ : Ty) : Ctx :=
  { Γ with regs := fun r' => if r' = r then τ else Γ.regs r' }

/-- Whether the operation reads the carry flag. -/
def AluOp.readsCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

/-- The context after a two-operand operation on register `d`: the flags
become known, and `d` holds an integer if the operation writes it. -/
def CtxOf.afterAlu (Γ : Ctx) (op : AluOp) (d : Reg) : Ctx :=
  { (if op.writesDst then Γ.setReg d .int else Γ) with flags := true }

/-- The context after a system call: the operating system may have changed
`rax`, `rcx`, `r11` and the flags. -/
def CtxOf.afterSyscall (Γ : Ctx) : Ctx :=
  { ((Γ.setReg .rax .int).setReg .rcx .int).setReg .r11 .int with flags := false }

/-- The displacement that addresses 8-byte slot `i`. -/
def slotDisp (i : Nat) (disp : BitVec 32) : Prop :=
  disp = BitVec.ofNat 32 (8 * i) ∧ 8 * i < 2 ^ 31

/-! ## Instructions that continue to the next one -/

/-- `Straight Γ i Γ'`: in a state matching `Γ`, instruction `i` executes
safely and leaves a state matching `Γ'`. The stack pointer is never an
explicit destination. -/
inductive Straight : Ctx → Instr → Ctx → Prop
  | nop {Γ : Ctx} : Straight Γ .nop Γ
  /-- A 64-bit register copy carries the type along. -/
  | movRR64 {Γ : Ctx} {d s : Reg} : d ≠ .rsp → s ≠ .rsp →
    Straight Γ (.mov .w64 (.rm_r (.reg d) s)) (Γ.setReg d (Γ.regs s))
  /-- A 32-bit register copy keeps only the low half, so the result is an integer. -/
  | movRR32 {Γ : Ctx} {d s : Reg} : d ≠ .rsp →
    Straight Γ (.mov .w32 (.rm_r (.reg d) s)) (Γ.setReg d .int)
  | movRI {Γ : Ctx} {w : Width} {d : Reg} {imm : BitVec 32} : d ≠ .rsp →
    Straight Γ (.mov w (.rm_i (.reg d) imm)) (Γ.setReg d .int)
  | movAbs {Γ : Ctx} {d : Reg} {imm : BitVec 64} : d ≠ .rsp →
    Straight Γ (.movAbs d imm) (Γ.setReg d .int)
  /-- `lea` only computes an address; the result is an integer. -/
  | lea {Γ : Ctx} {w : Width} {d : Reg} {m : Mem} : d ≠ .rsp →
    Straight Γ (.lea w d m) (Γ.setReg d .int)
  /-- Load field `i` of the block a register points to. -/
  | loadField {Γ : Ctx} {d b : Reg} {fields : List Ty} {writable : Bool} {i : Nat}
      {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr fields writable → fields[i]? = some τ →
    slotDisp i disp →
    Straight Γ (.mov .w64 (.r_m d (.sib (some b) none disp))) (Γ.setReg d τ)
  /-- Store into field `i` of a writable block. The stored value must have the field's type. -/
  | storeField {Γ : Ctx} {b s : Reg} {fields : List Ty} {i : Nat} {disp : BitVec 32} {τ : Ty} :
    b ≠ .rsp → s ≠ .rsp → Γ.regs b = .ptr fields true → fields[i]? = some τ →
    Sub (Γ.regs s) τ → slotDisp i disp →
    Straight Γ (.mov .w64 (.rm_r (.mem (.sib (some b) none disp)) s)) Γ
  /-- Load stack slot `i`. -/
  | loadStack {Γ : Ctx} {d : Reg} {i : Nat} {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → Γ.stack[i]? = some τ → slotDisp i disp →
    Straight Γ (.mov .w64 (.r_m d (.sib (some .rsp) none disp))) (Γ.setReg d τ)
  /-- Store into stack slot `i`. The slot takes the type of the stored value. -/
  | storeStack {Γ : Ctx} {s : Reg} {i : Nat} {disp : BitVec 32} :
    s ≠ .rsp → i < Γ.stack.length → slotDisp i disp →
    Straight Γ (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none disp)) s))
      { Γ with stack := Γ.stack.set i (Γ.regs s) }
  | push {Γ : Ctx} {r : Reg} {n : Nat} : r ≠ .rsp → Γ.room = n + 1 →
    Straight Γ (.push r) { Γ with stack := Γ.regs r :: Γ.stack, room := n }
  | pop {Γ : Ctx} {r : Reg} {τ : Ty} {σ : List Ty} : r ≠ .rsp → Γ.stack = τ :: σ →
    Straight Γ (.pop r) (CtxOf.setReg { Γ with stack := σ, room := Γ.room + 1 } r τ)
  /-- Arithmetic between registers. The result is an integer whatever the operands were. -/
  | aluRR {Γ : Ctx} {op : AluOp} {w : Width} {d s : Reg} :
    d ≠ .rsp → (op.readsCarry = true → Γ.flags = true) →
    Straight Γ (.alu op w (.rm_r (.reg d) s)) (Γ.afterAlu op d)
  | aluRI {Γ : Ctx} {op : AluOp} {w : Width} {d : Reg} {imm : BitVec 32} :
    d ≠ .rsp → (op.readsCarry = true → Γ.flags = true) →
    Straight Γ (.alu op w (.rm_i (.reg d) imm)) (Γ.afterAlu op d)
  | test {Γ : Ctx} {w : Width} {r : Reg} {src : RI} :
    Straight Γ (.test w (.reg r) src) { Γ with flags := true }

/-! ## All typed instructions -/

/-- `HasType Φ next Γ i`: in a state matching `Γ`, instruction `i` executes
safely, and wherever control goes next, the code there accepts the resulting
state. `next` is the address of the following instruction. -/
inductive HasType (Φ : CodeTy) (next : BitVec 64) : Ctx → Instr → Prop
  | straight {Γ Γ' : Ctx} {i : Instr} : Straight Γ i Γ' → Accepts Φ next Γ' → HasType Φ next Γ i
  | jmp {Γ : Ctx} {d : BitVec 32} : Accepts Φ (next + d.signExtend 64) Γ →
    HasType Φ next Γ (.jmp (.rel d))
  /-- A conditional jump needs known flags, and both successors must accept. -/
  | jcc {Γ : Ctx} {c : Cond} {d : BitVec 32} : Γ.flags = true →
    Accepts Φ (next + d.signExtend 64) Γ → Accepts Φ next Γ → HasType Φ next Γ (.jcc c d)
  /-- Jump through a register holding a code pointer. -/
  | jmpReg {Γ Δ : Ctx} {r : Reg} : r ≠ .rsp → Γ.regs r = .code Δ → CtxSub Γ Δ →
    HasType Φ next Γ (.jmp (.ind (.reg r)))
  /-- A call pushes the return address, typed as a pointer to code expecting
  the context required at the instruction after the call. The callee sees it
  on top of the stack. -/
  | call {Γ ret : Ctx} {d : BitVec 32} {n : Nat} : Γ.room = n + 1 → Φ next = some ret →
    Accepts Φ (next + d.signExtend 64) { Γ with stack := .code ret :: Γ.stack, room := n } →
    HasType Φ next Γ (.call (.rel d))
  /-- A return needs a code pointer on top of the stack, and the state with it
  popped must match what that code requires. -/
  | ret {Γ Δ : Ctx} {σ : List Ty} : Γ.stack = .code Δ :: σ →
    CtxSub { Γ with stack := σ, room := Γ.room + 1 } Δ → HasType Φ next Γ .ret
  | syscall {Γ : Ctx} : Accepts Φ next Γ.afterSyscall → HasType Φ next Γ .syscall

/-! ## Programs and states -/

/-- A program is well typed if every address the code typing mentions holds
an instruction that is well typed in the context given for that address. -/
def ProgramOk (Φ : CodeTy) (fetch : Fetch) : Prop :=
  ∀ a Γ, Φ a = some Γ → ∃ i len, fetch a = some (i, len) ∧ HasType Φ (a + len) Γ i

/-- A state is well typed if it matches the context the code typing gives
for its `rip`, at every step count. -/
def StateOk (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (s : State) : Prop :=
  ∃ Γ, Φ s.rip = some Γ ∧ ∀ n, WellTyped fetch sys Ψ n Γ s

/-- What the type system assumes about the operating system: a system call
from a well-typed state has an acceptable outcome, and if it returns, it
returns to the same place with a state that is still well typed, having
changed at most `rax`, `rcx`, `r11` and the flags as far as types can tell. -/
def SysOk (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) : Prop :=
  ∀ n Γ s, WellTyped fetch sys Ψ n Γ s →
    (sys s).isSafe = true ∧
    ∀ s', sys s = .next s' → s'.rip = s.rip ∧ WellTyped fetch sys Ψ n Γ.afterSyscall s'

end TypedAsm
