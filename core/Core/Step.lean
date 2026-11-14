import Core.Memory

/-!
# Executing instructions

What each instruction does to a machine state, and how the machine moves from
one instruction to the next.

Flags the hardware leaves undefined after an instruction become `none`.
-/

namespace Core

/-- Exceptions the hardware raises. -/
inductive Fault
  /-- Division by zero, or a quotient that does not fit. -/
  | divideError
  /-- An undefined instruction, including `ud2`. -/
  | invalidOpcode
  deriving DecidableEq, Repr

/-- The result of trying to execute one instruction. -/
inductive Outcome
  /-- Execution continued normally. -/
  | next (s : State)
  /-- The hardware would raise an exception. -/
  | fault (f : Fault)
  /-- The program asked the operating system to end it, with this status. -/
  | exit (code : BitVec 32)
  /-- The model does not say what happens. -/
  | stuck

/-- Where the machine finds instructions: the instruction at an address,
together with its length in bytes. -/
abbrev Fetch := BitVec 64 → Option (Instr × BitVec 64)

/-- What the operating system does on `syscall`. It receives the state with
`rip` already past the instruction. The hardware overwrites `rcx` and `r11`
on the way in, so a faithful oracle does not preserve them. -/
abbrev Syscall := State → Outcome

/-! ## Flags -/

/-- The flags that depend only on the result. -/
def Flags.ofResult {n : Nat} (r : BitVec n) (cf of : Bool) : Flags where
  cf := some cf
  zf := some (r == 0)
  sf := some r.msb
  of := some of

/-- Whether a condition holds, or `none` if it depends on an unknown flag. -/
def Cond.eval (f : Flags) : Cond → Option Bool
  | .o => f.of
  | .no => f.of.map (!·)
  | .b => f.cf
  | .ae => f.cf.map (!·)
  | .e => f.zf
  | .ne => f.zf.map (!·)
  | .be => do return (← f.cf) || (← f.zf)
  | .a => do return !((← f.cf) || (← f.zf))
  | .s => f.sf
  | .ns => f.sf.map (!·)
  | .l => do return (← f.sf) != (← f.of)
  | .ge => do return (← f.sf) == (← f.of)
  | .le => do return (← f.zf) || ((← f.sf) != (← f.of))
  | .g => do return !(← f.zf) && ((← f.sf) == (← f.of))

/-! ## Arithmetic -/

/-- `a + b + carry`, with the resulting flags. The sum is computed one bit
wider than the operands, so the carry out is its top bit. -/
def addCarry {n : Nat} (a b : BitVec n) (carry : Bool) : BitVec n × Flags :=
  let wide := a.setWidth (n + 1) + b.setWidth (n + 1) + (BitVec.ofBool carry).setWidth (n + 1)
  let r := wide.setWidth n
  (r, .ofResult r wide.msb (a.msb == b.msb && r.msb != a.msb))

/-- `a - b - borrow`, with the resulting flags. The carry flag is the borrow out. -/
def subBorrow {n : Nat} (a b : BitVec n) (borrow : Bool) : BitVec n × Flags :=
  let wide := a.setWidth (n + 1) - b.setWidth (n + 1) - (BitVec.ofBool borrow).setWidth (n + 1)
  let r := wide.setWidth n
  (r, .ofResult r wide.msb (a.msb != b.msb && r.msb != a.msb))

/-- The result and flags of a two-operand operation. `cf` is the incoming carry
flag; the result is `none` when the operation needs it and it is unknown. -/
def AluOp.eval {n : Nat} (op : AluOp) (cf : Option Bool) (a b : BitVec n) :
    Option (BitVec n × Flags) :=
  match op with
  | .add => some (addCarry a b false)
  | .adc => cf.map (addCarry a b)
  | .sub | .cmp => some (subBorrow a b false)
  | .sbb => cf.map (subBorrow a b)
  | .and => some (a &&& b, .ofResult (a &&& b) false false)
  | .or => some (a ||| b, .ofResult (a ||| b) false false)
  | .xor => some (a ^^^ b, .ofResult (a ^^^ b) false false)

/-- Whether the operation writes its result back to the destination. -/
def AluOp.writesDst : AluOp → Bool
  | .cmp => false
  | _ => true

/-- The result and flags of a shift or rotate by `c`, where `c` has already
been reduced modulo the operand width. A count of zero changes no flags.
Rotates change only the carry and overflow flags. The overflow flag is
defined only for a count of one. -/
def ShiftOp.eval {n : Nat} (op : ShiftOp) (old : Flags) (a : BitVec n) (c : Nat) :
    BitVec n × Flags :=
  if c = 0 then (a, old) else
  let ofIfOne (b : Bool) : Option Bool := if c = 1 then some b else none
  match op with
  | .shl =>
    let r := a <<< c
    let cf := a.getLsbD (n - c)
    (r, ⟨some cf, some (r == 0), some r.msb, ofIfOne (r.msb != cf)⟩)
  | .shr =>
    let r := a >>> c
    (r, ⟨some (a.getLsbD (c - 1)), some (r == 0), some r.msb, ofIfOne a.msb⟩)
  | .sar =>
    let r := a.sshiftRight c
    (r, ⟨some (a.getLsbD (c - 1)), some (r == 0), some r.msb, ofIfOne false⟩)
  | .rol =>
    let r := a.rotateLeft c
    let cf := r.getLsbD 0
    (r, { old with cf := some cf, of := ofIfOne (r.msb != cf) })
  | .ror =>
    let r := a.rotateRight c
    (r, { old with cf := some r.msb, of := ofIfOne (r.msb != r.getLsbD (n - 2)) })

/-- Flags after a multiply: carry and overflow both report whether the
product did not fit; zero and sign are undefined. -/
def Flags.ofMul (overflow : Bool) : Flags :=
  ⟨some overflow, none, none, some overflow⟩

/-- Flags after a divide: all undefined. -/
def Flags.unknown : Flags :=
  ⟨none, none, none, none⟩

/-- Signed multiply keeping only the low half of the product. -/
def imulTrunc {n : Nat} (a b : BitVec n) : BitVec n × Flags :=
  let full := a.signExtend (n + n) * b.signExtend (n + n)
  let r := full.setWidth n
  (r, .ofMul (full != r.signExtend (n + n)))

/-- Widening multiply and divide. `hi` and `lo` are the incoming `rdx` and
`rax`; the result is the new `rax`, the new `rdx`, and the flags. A divide
faults on a zero divisor or a quotient that does not fit. -/
def MulDivOp.eval {n : Nat} (op : MulDivOp) (hi lo src : BitVec n) :
    Except Fault (BitVec n × BitVec n × Flags) :=
  match op with
  | .mul =>
    let full := lo.setWidth (n + n) * src.setWidth (n + n)
    let h := (full >>> n).setWidth n
    .ok (full.setWidth n, h, .ofMul (h != 0))
  | .imul =>
    let full := lo.signExtend (n + n) * src.signExtend (n + n)
    let l := full.setWidth n
    .ok (l, (full >>> n).setWidth n, .ofMul (full != l.signExtend (n + n)))
  | .div =>
    let dividend := hi ++ lo
    let d := src.setWidth (n + n)
    let q := dividend / d
    if src == 0 || (q.setWidth n).setWidth (n + n) != q then .error .divideError
    else .ok (q.setWidth n, (dividend % d).setWidth n, .unknown)
  | .idiv =>
    let dividend := hi ++ lo
    let d := src.signExtend (n + n)
    let q := dividend.sdiv d
    if src == 0 || (q.setWidth n).signExtend (n + n) != q then .error .divideError
    else .ok (q.setWidth n, (dividend.srem d).setWidth n, .unknown)

/-- The number of set bits. -/
def popcount {n : Nat} (a : BitVec n) : BitVec n :=
  BitVec.ofNat n ((List.range n).filter (a.getLsbD ·)).length

def bswap32 (v : BitVec 32) : BitVec 32 :=
  v.extractLsb' 0 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 24 8

def bswap64 (v : BitVec 64) : BitVec 64 :=
  bswap32 (v.extractLsb' 0 32) ++ bswap32 (v.extractLsb' 32 32)

/-- Reverse the order of the bytes. -/
def bswap (w : Width) (v : BitVec w.bits) : BitVec w.bits :=
  match w with
  | .w32 => bswap32 v
  | .w64 => bswap64 v

/-- All ones if the value is negative, otherwise zero. -/
def signFill {n : Nat} (a : BitVec n) : BitVec n :=
  if a.msb then BitVec.allOnes n else 0

def NarrowW.bits : NarrowW → Nat
  | .w8 => 8
  | .w16 => 16

/-! ## Operands -/

namespace State

def readRM (s : State) (w : Width) : RM → BitVec w.bits
  | .reg r => s.readReg w r
  | .mem m => s.load w (s.ea m)

def writeRM (s : State) (w : Width) (dst : RM) (v : BitVec w.bits) : State :=
  match dst with
  | .reg r => s.writeReg w r v
  | .mem m => s.store w (s.ea m) v

def readRI (s : State) (w : Width) : RI → BitVec w.bits
  | .reg r => s.readReg w r
  | .imm i => i.signExtend w.bits

/-- Read an 8- or 16-bit value: the low bits of a register, or from memory. -/
def readNarrow (s : State) (sw : NarrowW) (src : RM) : BitVec sw.bits :=
  match src with
  | .reg r => (s.getReg r).setWidth sw.bits
  | .mem m =>
    match sw with
    | .w8 => s.load8 (s.ea m)
    | .w16 => s.load16 (s.ea m)

/-- Write one byte: the low byte of a register, leaving its other 56 bits
unchanged, or one byte of memory. -/
def writeRM8 (s : State) (dst : RM) (v : BitVec 8) : State :=
  match dst with
  | .reg r => s.setReg r ((s.getReg r &&& ~~~0xff) ||| v.setWidth 64)
  | .mem m => s.store8 (s.ea m) v

/-- A shift count reduced modulo the operand width, as the hardware does. -/
def shiftCount (s : State) (w : Width) : Count → Nat
  | .imm n => n.toNat % w.bits
  | .cl => (s.getReg .rcx).toNat % w.bits

/-- Decrement `rsp` by 8 and store a value there. -/
def push64 (s : State) (v : BitVec 64) : State :=
  let sp := s.getReg .rsp - 8
  (s.setReg .rsp sp).store64 sp v

/-- Load the value at `rsp` and increment `rsp` by 8. -/
def pop64 (s : State) : BitVec 64 × State :=
  (s.load64 (s.getReg .rsp), s.setReg .rsp (s.getReg .rsp + 8))

end State

/-- The destination of a two-operand form. -/
def Operands.dst : Operands → RM
  | .rm_r dst _ => dst
  | .r_m dst _ => .reg dst
  | .rm_i dst _ => dst

/-- The value of the source of a two-operand form. Immediates are sign-extended. -/
def Operands.src (s : State) (w : Width) : Operands → BitVec w.bits
  | .rm_r _ src => s.readReg w src
  | .r_m _ src => s.load w (s.ea src)
  | .rm_i _ imm => imm.signExtend w.bits

/-! ## Instructions -/

/-- Execute one instruction. `s.rip` must already hold the address of the
instruction after it. -/
def exec (sys : Syscall) (i : Instr) (s : State) : Outcome :=
  match i with
  -- arithmetic and logic
  | .alu op w ops =>
    match op.eval s.flags.cf (s.readRM w ops.dst) (ops.src s w) with
    | none => .stuck
    | some (r, flags) =>
      let s := if op.writesDst then s.writeRM w ops.dst r else s
      .next { s with flags }
  | .test w dst src =>
    let r := s.readRM w dst &&& s.readRI w src
    .next { s with flags := .ofResult r false false }
  | .unary .neg w dst =>
    let (r, flags) := subBorrow 0 (s.readRM w dst) false
    .next { s.writeRM w dst r with flags }
  | .unary .not w dst => .next (s.writeRM w dst (~~~(s.readRM w dst)))
  | .shift op w dst c =>
    let (r, flags) := op.eval s.flags (s.readRM w dst) (s.shiftCount w c)
    .next { s.writeRM w dst r with flags }
  | .mulDiv op w src =>
    match op.eval (s.readReg w .rdx) (s.readReg w .rax) (s.readRM w src) with
    | .error f => .fault f
    | .ok (lo, hi, flags) => .next { (s.writeReg w .rax lo).writeReg w .rdx hi with flags }
  | .imul2 w dst src =>
    let (r, flags) := imulTrunc (s.readReg w dst) (s.readRM w src)
    .next { s.writeReg w dst r with flags }
  | .imul3 w dst src imm =>
    let (r, flags) := imulTrunc (s.readRM w src) (imm.signExtend w.bits)
    .next { s.writeReg w dst r with flags }
  | .popcnt w dst src =>
    let a := s.readRM w src
    .next { s.writeReg w dst (popcount a) with flags := ⟨some false, some (a == 0), some false, some false⟩ }
  | .bswap w r => .next (s.writeReg w r (bswap w (s.readReg w r)))
  | .cdq => .next (s.writeReg .w32 .rdx (signFill (s.readReg .w32 .rax)))
  | .cqo => .next (s.writeReg .w64 .rdx (signFill (s.readReg .w64 .rax)))
  -- data movement
  | .mov w ops => .next (s.writeRM w ops.dst (ops.src s w))
  | .movAbs dst imm => .next (s.setReg dst imm)
  | .store8 dst src => .next (s.store8 (s.ea dst) ((s.getReg src).setWidth 8))
  | .movzx w dst sw src => .next (s.writeReg w dst ((s.readNarrow sw src).setWidth w.bits))
  | .movsx w dst sw src => .next (s.writeReg w dst ((s.readNarrow sw src).signExtend w.bits))
  | .movsxd dst src => .next (s.setReg dst ((s.readRM .w32 src).signExtend 64))
  | .lea w dst addr => .next (s.writeReg w dst ((s.ea addr).setWidth w.bits))
  | .cmov c w dst src =>
    match c.eval s.flags with
    | none => .stuck
    | some b => .next (s.writeReg w dst (if b then s.readRM w src else s.readReg w dst))
  | .setcc c dst =>
    match c.eval s.flags with
    | none => .stuck
    | some b => .next (s.writeRM8 dst (if b then 1 else 0))
  | .push r => .next (s.push64 (s.getReg r))
  | .pop r =>
    let (v, s) := s.pop64
    .next (s.setReg r v)
  -- control flow
  | .jmp (.rel d) => .next { s with rip := s.rip + d.signExtend 64 }
  | .jmp (.ind rm) => .next { s with rip := s.readRM .w64 rm }
  | .jcc c d =>
    match c.eval s.flags with
    | none => .stuck
    | some true => .next { s with rip := s.rip + d.signExtend 64 }
    | some false => .next s
  | .call t =>
    let target := match t with
      | .rel d => s.rip + d.signExtend 64
      | .ind rm => s.readRM .w64 rm
    .next { s.push64 s.rip with rip := target }
  | .ret =>
    let (v, s) := s.pop64
    .next { s with rip := v }
  -- miscellaneous
  | .nop => .next s
  | .ud2 => .fault .invalidOpcode
  | .syscall => sys s

/-- Fetch the instruction at `rip`, advance `rip` past it, and execute it. -/
def step (fetch : Fetch) (sys : Syscall) (s : State) : Outcome :=
  match fetch s.rip with
  | none => .stuck
  | some (i, len) => exec sys i { s with rip := s.rip + len }

/-- Take up to `n` steps, stopping early at a fault, at exit, or when stuck. -/
def run (fetch : Fetch) (sys : Syscall) : Nat → State → Outcome
  | 0, s => .next s
  | n + 1, s =>
    match step fetch sys s with
    | .next s => run fetch sys n s
    | o => o

/-- Popping straight after a push returns the pushed value. -/
theorem State.pop64_push64 (s : State) (v : BitVec 64) : (s.push64 v).pop64.1 = v :=
  State.load_store_same _ .w64 _ v

/-! ## Agreement with the standard library

The carry and overflow flags above are defined from first principles. These
check them against Lean's own overflow predicates. -/

theorem addCarry_cf (w : Width) (a b : BitVec w.bits) :
    (addCarry a b false).2.cf = some (BitVec.uaddOverflow a b) := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    simp only [addCarry, Flags.ofResult, Option.some.injEq] <;> bv_decide

theorem addCarry_of (w : Width) (a b : BitVec w.bits) :
    (addCarry a b false).2.of = some (BitVec.saddOverflow a b) := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    simp only [addCarry, Flags.ofResult, Option.some.injEq] <;> bv_decide

theorem subBorrow_cf (w : Width) (a b : BitVec w.bits) :
    (subBorrow a b false).2.cf = some (BitVec.usubOverflow a b) := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    simp only [subBorrow, Flags.ofResult, Option.some.injEq] <;> bv_decide

theorem subBorrow_of (w : Width) (a b : BitVec w.bits) :
    (subBorrow a b false).2.of = some (BitVec.ssubOverflow a b) := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    simp only [subBorrow, Flags.ofResult, Option.some.injEq] <;> bv_decide

end Core
