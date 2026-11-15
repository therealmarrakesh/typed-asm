import TypedAsm.Memory

/-!
# Executing instructions

What each instruction does to a machine state, and how the machine moves from
one instruction to the next.

Flags the hardware leaves undefined after an instruction become `none`.
-/

namespace TypedAsm

/-- The result of trying to execute one instruction. -/
abbrev Outcome := Result State

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
    Result (BitVec n × BitVec n × Flags) :=
  match op with
  | .mul =>
    let full := lo.setWidth (n + n) * src.setWidth (n + n)
    let h := (full >>> n).setWidth n
    .next (full.setWidth n, h, .ofMul (h != 0))
  | .imul =>
    let full := lo.signExtend (n + n) * src.signExtend (n + n)
    let l := full.setWidth n
    .next (l, (full >>> n).setWidth n, .ofMul (full != l.signExtend (n + n)))
  | .div =>
    let dividend := hi ++ lo
    let d := src.setWidth (n + n)
    let q := dividend / d
    if src == 0 || (q.setWidth n).setWidth (n + n) != q then .fault .divideError
    else .next (q.setWidth n, (dividend % d).setWidth n, .unknown)
  | .idiv =>
    let dividend := hi ++ lo
    let d := src.signExtend (n + n)
    let q := dividend.sdiv d
    if src == 0 || (q.setWidth n).signExtend (n + n) != q then .fault .divideError
    else .next (q.setWidth n, (dividend.srem d).setWidth n, .unknown)

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

@[reducible] def NarrowW.bits : NarrowW → Nat
  | .w8 => 8
  | .w16 => 16

/-! ## Operands

Reading or writing a memory operand faults if the access is not permitted. -/

namespace State

def readRM (s : State) (w : Width) : RM → Result (BitVec w.bits)
  | .reg r => .next (s.readReg w r)
  | .mem m => s.read w (s.ea m)

def writeRM (s : State) (w : Width) (dst : RM) (v : BitVec w.bits) : Result State :=
  match dst with
  | .reg r => .next (s.writeReg w r v)
  | .mem m => s.write w (s.ea m) v

def readRI (s : State) (w : Width) : RI → BitVec w.bits
  | .reg r => s.readReg w r
  | .imm i => i.signExtend w.bits

/-- Read an 8- or 16-bit value: the low bits of a register, or from memory. -/
def readNarrow (s : State) (sw : NarrowW) (src : RM) : Result (BitVec sw.bits) :=
  match src with
  | .reg r => .next ((s.getReg r).setWidth sw.bits)
  | .mem m =>
    match sw with
    | .w8 => s.read8 (s.ea m)
    | .w16 => s.read16 (s.ea m)

/-- Write one byte: the low byte of a register, leaving its other 56 bits
unchanged, or one byte of memory. -/
def writeRM8 (s : State) (dst : RM) (v : BitVec 8) : Result State :=
  match dst with
  | .reg r => .next (s.setReg r ((s.getReg r &&& ~~~0xff) ||| v.setWidth 64))
  | .mem m => s.write8 (s.ea m) v

/-- A shift count reduced modulo the operand width, as the hardware does. -/
def shiftCount (s : State) (w : Width) : Count → Nat
  | .imm n => n.toNat % w.bits
  | .cl => (s.getReg .rcx).toNat % w.bits

/-- Decrement `rsp` by 8 and store a value there. -/
def push64 (s : State) (v : BitVec 64) : Result State :=
  let sp := s.getReg .rsp - 8
  (s.setReg .rsp sp).write64 sp v

/-- Load the value at `rsp` and increment `rsp` by 8. -/
def pop64 (s : State) : Result (BitVec 64 × State) := do
  let v ← s.read64 (s.getReg .rsp)
  return (v, s.setReg .rsp (s.getReg .rsp + 8))

end State

/-- The destination of a two-operand form. -/
def Operands.dst : Operands → RM
  | .rm_r dst _ => dst
  | .r_m dst _ => .reg dst
  | .rm_i dst _ => dst

/-- The value of the source of a two-operand form. Immediates are sign-extended. -/
def Operands.src (s : State) (w : Width) : Operands → Result (BitVec w.bits)
  | .rm_r _ src => .next (s.readReg w src)
  | .r_m _ src => s.read w (s.ea src)
  | .rm_i _ imm => .next (imm.signExtend w.bits)

/-! ## Instructions -/

/-- Execute one instruction. `s.rip` must already hold the address of the
instruction after it.

An instruction that faults changes nothing: a fault carries no state, and
every memory access is checked before any part of it is performed. -/
def exec (sys : Syscall) (i : Instr) (s : State) : Outcome :=
  match i with
  -- arithmetic and logic
  | .alu op w ops => do
    let a ← s.readRM w ops.dst
    let b ← ops.src s w
    let (r, flags) ← Result.ofOption (op.eval s.flags.cf a b)
    let s ← if op.writesDst then s.writeRM w ops.dst r else pure s
    return { s with flags }
  | .test w dst src => do
    let r := (← s.readRM w dst) &&& s.readRI w src
    return { s with flags := .ofResult r false false }
  | .unary .neg w dst => do
    let (r, flags) := subBorrow 0 (← s.readRM w dst) false
    let s ← s.writeRM w dst r
    return { s with flags }
  | .unary .not w dst => do
    s.writeRM w dst (~~~(← s.readRM w dst))
  | .shift op w dst c => do
    let (r, flags) := op.eval s.flags (← s.readRM w dst) (s.shiftCount w c)
    let s ← s.writeRM w dst r
    return { s with flags }
  | .mulDiv op w src => do
    let (lo, hi, flags) ← op.eval (s.readReg w .rdx) (s.readReg w .rax) (← s.readRM w src)
    return { (s.writeReg w .rax lo).writeReg w .rdx hi with flags }
  | .imul2 w dst src => do
    let (r, flags) := imulTrunc (s.readReg w dst) (← s.readRM w src)
    return { s.writeReg w dst r with flags }
  | .imul3 w dst src imm => do
    let (r, flags) := imulTrunc (← s.readRM w src) (imm.signExtend w.bits)
    return { s.writeReg w dst r with flags }
  | .popcnt w dst src => do
    let a ← s.readRM w src
    return { s.writeReg w dst (popcount a) with
      flags := ⟨some false, some (a == 0), some false, some false⟩ }
  | .bswap w r => .next (s.writeReg w r (bswap w (s.readReg w r)))
  | .cdq => .next (s.writeReg .w32 .rdx (signFill (s.readReg .w32 .rax)))
  | .cqo => .next (s.writeReg .w64 .rdx (signFill (s.readReg .w64 .rax)))
  -- data movement
  | .mov w ops => do
    s.writeRM w ops.dst (← ops.src s w)
  | .movAbs dst imm => .next (s.setReg dst imm)
  | .store8 dst src => s.write8 (s.ea dst) ((s.getReg src).setWidth 8)
  | .store16 dst src => s.write16 (s.ea dst) ((s.getReg src).setWidth 16)
  | .movzx w dst sw src => do
    return s.writeReg w dst ((← s.readNarrow sw src).setWidth w.bits)
  | .movsx w dst sw src => do
    return s.writeReg w dst ((← s.readNarrow sw src).signExtend w.bits)
  | .movsxd dst src => do
    return s.setReg dst ((← s.readRM .w32 src).signExtend 64)
  | .lea w dst addr => .next (s.writeReg w dst ((s.ea addr).setWidth w.bits))
  | .cmov c w dst src => do
    -- The source is read, and can fault, even when the condition is false.
    let v ← s.readRM w src
    let b ← Result.ofOption (c.eval s.flags)
    return s.writeReg w dst (if b then v else s.readReg w dst)
  | .setcc c dst => do
    let b ← Result.ofOption (c.eval s.flags)
    s.writeRM8 dst (if b then 1 else 0)
  | .push r => s.push64 (s.getReg r)
  | .pop r => do
    let (v, s) ← s.pop64
    return s.setReg r v
  -- control flow
  | .jmp (.rel d) => .next { s with rip := s.rip + d.signExtend 64 }
  | .jmp (.ind rm) => do
    return { s with rip := ← s.readRM .w64 rm }
  | .jcc c d => do
    let b ← Result.ofOption (c.eval s.flags)
    return if b then { s with rip := s.rip + d.signExtend 64 } else s
  | .call t => do
    let target ← match t with
      | .rel d => pure (s.rip + d.signExtend 64)
      | .ind rm => s.readRM .w64 rm
    let s' ← s.push64 s.rip
    return { s' with rip := target }
  | .ret => do
    let (v, s) ← s.pop64
    return { s with rip := v }
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

/-- Popping straight after a successful push returns the pushed value. -/
theorem State.pop64_push64 {s s' : State} {v : BitVec 64} (h : s.push64 v = .next s') :
    s'.pop64 = .next (v, s'.setReg .rsp (s'.getReg .rsp + 8)) := by
  simp only [State.push64, State.write64] at h
  split at h
  next hw =>
    cases h
    have hsp : ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v).getReg .rsp
        = s.getReg .rsp - 8 :=
      (State.getReg_store _ .w64 _ v _).trans (State.getReg_setReg_same _ _ _)
    have hr : ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v).canRead
        (s.getReg .rsp - 8) 8 = true :=
      State.canRead_of_canWrite hw
    have hv : ((s.setReg .rsp (s.getReg .rsp - 8)).store64 (s.getReg .rsp - 8) v).load64
        (s.getReg .rsp - 8) = v :=
      State.load_store_same _ .w64 _ v
    simp only [State.pop64, State.read64, hsp, hr, hv, ite_true]
    rfl
  next => cases h

/-! ## Agreement with the standard library

The carry and overflow flags above are defined from first principles. These
check them against Lean's own overflow predicates. -/

theorem addCarry_cf (w : Width) (a b : BitVec w.bits) :
    (addCarry a b false).2.cf = some (BitVec.uaddOverflow a b) := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    (have := a.isLt; have := b.isLt
     simp [addCarry, Flags.ofResult, BitVec.uaddOverflow, BitVec.msb_eq_decide, BitVec.toNat_add,
       BitVec.toNat_setWidth]
     omega)

theorem addCarry_of (w : Width) (a b : BitVec w.bits) :
    (addCarry a b false).2.of = some (BitVec.saddOverflow a b) := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    (have := a.isLt; have := b.isLt
     simp only [addCarry, Flags.ofResult, Option.some.injEq, BitVec.saddOverflow]
     rw [Bool.eq_iff_iff]
     simp [BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.toNat_setWidth,
       BitVec.toInt_eq_toNat_cond]
     omega)

theorem subBorrow_cf (w : Width) (a b : BitVec w.bits) :
    (subBorrow a b false).2.cf = some (BitVec.usubOverflow a b) := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    (have := a.isLt; have := b.isLt
     simp [subBorrow, Flags.ofResult, BitVec.usubOverflow, BitVec.msb_eq_decide, BitVec.toNat_sub,
       BitVec.toNat_setWidth]
     omega)

theorem subBorrow_of (w : Width) (a b : BitVec w.bits) :
    (subBorrow a b false).2.of = some (BitVec.ssubOverflow a b) := by
  revert a b
  cases w <;> simp only [Width.bits] <;> intro a b <;>
    (have := a.isLt; have := b.isLt
     simp only [subBorrow, Flags.ofResult, Option.some.injEq, BitVec.ssubOverflow]
     rw [Bool.eq_iff_iff]
     simp [BitVec.msb_eq_decide, BitVec.toNat_sub, BitVec.toNat_setWidth,
       BitVec.toInt_eq_toNat_cond]
     omega)

end TypedAsm
