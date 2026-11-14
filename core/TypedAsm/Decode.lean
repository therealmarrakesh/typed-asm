import TypedAsm.Encode

/-!
# Decoding instructions

Reading an instruction back from bytes. `decode` is the inverse of
`Instr.encode`: see `Roundtrip.lean`.

The decoder accepts some byte sequences the encoder never produces, such as
a longer displacement than necessary, and reads them as the processor does.
It rejects everything outside the instruction set, including the legacy
prefixes and the byte registers `ah`, `ch`, `dh` and `bh`.
-/

namespace TypedAsm

/-! ## Numbers back to names -/

def Reg.ofNum : Nat → Reg
  | 0 => .rax | 1 => .rcx | 2 => .rdx | 3 => .rbx | 4 => .rsp | 5 => .rbp | 6 => .rsi | 7 => .rdi
  | 8 => .r8 | 9 => .r9 | 10 => .r10 | 11 => .r11 | 12 => .r12 | 13 => .r13 | 14 => .r14
  | _ => .r15

/-- Number 4 is `rsp`, which cannot be an index. -/
def IndexReg.ofNum : Nat → Option IndexReg
  | 0 => some .rax | 1 => some .rcx | 2 => some .rdx | 3 => some .rbx | 5 => some .rbp
  | 6 => some .rsi | 7 => some .rdi | 8 => some .r8 | 9 => some .r9 | 10 => some .r10
  | 11 => some .r11 | 12 => some .r12 | 13 => some .r13 | 14 => some .r14 | 15 => some .r15
  | _ => none

def Scale.ofCode : Nat → Scale
  | 0 => .s1 | 1 => .s2 | 2 => .s4 | _ => .s8

/-- Codes 10 and 11 are the parity conditions, which are not in the instruction set. -/
def Cond.ofCode : Nat → Option Cond
  | 0 => some .o | 1 => some .no | 2 => some .b | 3 => some .ae | 4 => some .e | 5 => some .ne
  | 6 => some .be | 7 => some .a | 8 => some .s | 9 => some .ns | 12 => some .l | 13 => some .ge
  | 14 => some .le | 15 => some .g
  | _ => none

def AluOp.ofCode : Nat → AluOp
  | 0 => .add | 1 => .or | 2 => .adc | 3 => .sbb | 4 => .and | 5 => .sub | 6 => .xor | _ => .cmp

def ShiftOp.ofCode : Nat → Option ShiftOp
  | 0 => some .rol | 1 => some .ror | 4 => some .shl | 5 => some .shr | 7 => some .sar
  | _ => none

def MulDivOp.ofCode : Nat → Option MulDivOp
  | 4 => some .mul | 5 => some .imul | 6 => some .div | 7 => some .idiv
  | _ => none

/-! ## Reading pieces -/

/-- The bits of a `REX` prefix. With no prefix, all are false. -/
structure Rex where
  present : Bool
  w : Bool
  r : Bool
  x : Bool
  b : Bool

def Rex.none : Rex := ⟨false, false, false, false, false⟩

/-- Reads a `REX` prefix if there is one. -/
def takeRex : List Byte → Rex × List Byte
  | [] => (.none, [])
  | p :: rest =>
    if 0x40 ≤ p.toNat ∧ p.toNat < 0x50 then
      (⟨true, decide (p.toNat / 8 % 2 = 1), decide (p.toNat / 4 % 2 = 1),
        decide (p.toNat / 2 % 2 = 1), decide (p.toNat % 2 = 1)⟩, rest)
    else (.none, p :: rest)

/-- The value a `REX` bit adds to a 3-bit register number. -/
def extBit (b : Bool) : Nat := if b then 8 else 0

/-- Reads a 32-bit value, least significant byte first. -/
def take32 : List Byte → Option (BitVec 32 × List Byte)
  | b0 :: b1 :: b2 :: b3 :: rest => some (b3 ++ b2 ++ b1 ++ b0, rest)
  | _ => none

/-- Reads a 64-bit value, least significant byte first. -/
def take64 (bs : List Byte) : Option (BitVec 64 × List Byte) := do
  let (lo, bs) ← take32 bs
  let (hi, bs) ← take32 bs
  return (hi ++ lo, bs)

/-- Reads one byte and sign-extends it to 32 bits. -/
def take8s : List Byte → Option (BitVec 32 × List Byte)
  | b :: rest => some (b.signExtend 32, rest)
  | [] => none

/-- Reads the displacement that goes with a `ModRM` mode. -/
def takeDisp (mode : Nat) (bs : List Byte) : Option (BitVec 32 × List Byte) :=
  if mode = 0 then some (0, bs)
  else if mode = 1 then take8s bs
  else take32 bs

/-- Reads an operand: the `ModRM` byte and whatever follows it. Returns the
3-bit register field, the operand, and the remaining bytes. -/
def takeOperand (rx : Rex) : List Byte → Option (Nat × RM × List Byte)
  | [] => none
  | m :: bs =>
    let mode := m.toNat / 64
    let reg := m.toNat / 8 % 8
    let rm := m.toNat % 8
    if mode = 3 then some (reg, .reg (Reg.ofNum (rm + extBit rx.b)), bs)
    else if rm = 4 then
      match bs with
      | [] => none
      | s :: bs =>
        let scale := s.toNat / 64
        let idx := s.toNat / 8 % 8
        let base := s.toNat % 8
        -- Index number 4 without the `REX` bit means "no index".
        let index? : Option (Option (IndexReg × Scale)) :=
          if idx = 4 ∧ rx.x = false then some none
          else (IndexReg.ofNum (idx + extBit rx.x)).map fun i => some (i, Scale.ofCode scale)
        match index? with
        | none => none
        | some index =>
          -- Base number 5 in mode 0 means "no base, 32-bit displacement".
          if base = 5 ∧ mode = 0 then
            (take32 bs).map fun (d, bs) => (reg, .mem (.sib none index d), bs)
          else
            (takeDisp mode bs).map fun (d, bs) =>
              (reg, .mem (.sib (some (Reg.ofNum (base + extBit rx.b))) index d), bs)
    else if rm = 5 ∧ mode = 0 then
      (take32 bs).map fun (d, bs) => (reg, .mem (.rip d), bs)
    else
      (takeDisp mode bs).map fun (d, bs) =>
        (reg, .mem (.sib (some (Reg.ofNum (rm + extBit rx.b))) none d), bs)

/-- Reads an operand that must be in memory. -/
def takeMem (rx : Rex) (bs : List Byte) : Option (Nat × Mem × List Byte) :=
  match takeOperand rx bs with
  | some (reg, .mem m, bs) => some (reg, m, bs)
  | _ => none

/-- Whether a byte-sized register operand is one we model. Without a `REX`
prefix, register numbers 4 to 7 mean `ah`, `ch`, `dh`, `bh`. -/
def byteRegOk (rx : Rex) (r : Reg) : Bool :=
  rx.present || !r.byteNeedsRex

def byteRmOk (rx : Rex) (rm : RM) : Bool :=
  rx.present || !rm.byteNeedsRex

/-! ## Instructions -/

/-- Decodes the instructions whose first opcode byte is `0F`. -/
def decode0F (rx : Rex) (w : Width) (op : Nat) (bs : List Byte) : Option (Instr × List Byte) :=
  let regOf (n : Nat) : Reg := Reg.ofNum (n + extBit rx.r)
  if op = 0x05 then some (.syscall, bs)
  else if op = 0x0B then some (.ud2, bs)
  else if op = 0xAF then (takeOperand rx bs).map fun (reg, rm, bs) => (.imul2 w (regOf reg) rm, bs)
  else if op = 0xB6 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      if byteRmOk rx rm then some (.movzx w (regOf reg) .w8 rm, bs) else none
  else if op = 0xB7 then
    (takeOperand rx bs).map fun (reg, rm, bs) => (.movzx w (regOf reg) .w16 rm, bs)
  else if op = 0xBE then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      if byteRmOk rx rm then some (.movsx w (regOf reg) .w8 rm, bs) else none
  else if op = 0xBF then
    (takeOperand rx bs).map fun (reg, rm, bs) => (.movsx w (regOf reg) .w16 rm, bs)
  else if 0x40 ≤ op ∧ op < 0x50 then
    (Cond.ofCode (op - 0x40)).bind fun c =>
      (takeOperand rx bs).map fun (reg, rm, bs) => (.cmov c w (regOf reg) rm, bs)
  else if 0x80 ≤ op ∧ op < 0x90 then
    (Cond.ofCode (op - 0x80)).bind fun c => (take32 bs).map fun (d, bs) => (.jcc c d, bs)
  else if 0x90 ≤ op ∧ op < 0xA0 then
    (Cond.ofCode (op - 0x90)).bind fun c =>
      (takeOperand rx bs).bind fun (_, rm, bs) =>
        if byteRmOk rx rm then some (.setcc c rm, bs) else none
  else if 0xC8 ≤ op ∧ op < 0xD0 then
    some (.bswap w (Reg.ofNum (op - 0xC8 + extBit rx.b)), bs)
  else none

/-- Decodes an instruction given its prefixes and first opcode byte. -/
def decodeOp (f3 : Bool) (rx : Rex) (op : Nat) (bs : List Byte) : Option (Instr × List Byte) :=
  let w : Width := if rx.w then .w64 else .w32
  let regOf (n : Nat) : Reg := Reg.ofNum (n + extBit rx.r)
  if f3 then
    -- The only instruction with this prefix is `popcnt`.
    match bs with
    | o2 :: bs =>
      if op = 0x0F ∧ o2.toNat = 0xB8 then
        (takeOperand rx bs).map fun (reg, rm, bs) => (.popcnt w (regOf reg) rm, bs)
      else none
    | [] => none
  else if op < 0x40 ∧ op % 8 = 1 then
    (takeOperand rx bs).map fun (reg, rm, bs) =>
      (.alu (AluOp.ofCode (op / 8)) w (.rm_r rm (regOf reg)), bs)
  else if op < 0x40 ∧ op % 8 = 3 then
    (takeMem rx bs).map fun (reg, m, bs) => (.alu (AluOp.ofCode (op / 8)) w (.r_m (regOf reg) m), bs)
  else if op < 0x40 ∧ op % 8 = 5 then
    (take32 bs).map fun (imm, bs) => (.alu (AluOp.ofCode (op / 8)) w (.rm_i (.reg .rax) imm), bs)
  else if 0x50 ≤ op ∧ op < 0x58 then some (.push (Reg.ofNum (op - 0x50 + extBit rx.b)), bs)
  else if 0x58 ≤ op ∧ op < 0x60 then some (.pop (Reg.ofNum (op - 0x58 + extBit rx.b)), bs)
  else if 0xB8 ≤ op ∧ op < 0xC0 then
    let r := Reg.ofNum (op - 0xB8 + extBit rx.b)
    if rx.w then (take64 bs).map fun (imm, bs) => (.movAbs r imm, bs)
    else (take32 bs).map fun (imm, bs) => (.mov .w32 (.rm_i (.reg r) imm), bs)
  else if op = 0x0F then
    match bs with
    | o2 :: bs => decode0F rx w o2.toNat bs
    | [] => none
  else if op = 0x63 then
    if rx.w then (takeOperand rx bs).map fun (reg, rm, bs) => (.movsxd (regOf reg) rm, bs)
    else none
  else if op = 0x69 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      (take32 bs).map fun (imm, bs) => (.imul3 w (regOf reg) rm imm, bs)
  else if op = 0x6B then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      (take8s bs).map fun (imm, bs) => (.imul3 w (regOf reg) rm imm, bs)
  else if op = 0x81 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      (take32 bs).map fun (imm, bs) => (.alu (AluOp.ofCode reg) w (.rm_i rm imm), bs)
  else if op = 0x83 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      (take8s bs).map fun (imm, bs) => (.alu (AluOp.ofCode reg) w (.rm_i rm imm), bs)
  else if op = 0x85 then
    (takeOperand rx bs).map fun (reg, rm, bs) => (.test w rm (.reg (regOf reg)), bs)
  else if op = 0x88 then
    (takeMem rx bs).bind fun (reg, m, bs) =>
      if byteRegOk rx (regOf reg) then some (.store8 m (regOf reg), bs) else none
  else if op = 0x89 then
    (takeOperand rx bs).map fun (reg, rm, bs) => (.mov w (.rm_r rm (regOf reg)), bs)
  else if op = 0x8B then
    (takeMem rx bs).map fun (reg, m, bs) => (.mov w (.r_m (regOf reg) m), bs)
  else if op = 0x8D then
    (takeMem rx bs).map fun (reg, m, bs) => (.lea w (regOf reg) m, bs)
  else if op = 0x90 then
    -- With a `REX` prefix this byte is an exchange, not a no-op.
    if rx.present then none else some (.nop, bs)
  else if op = 0x99 then some (if rx.w then .cqo else .cdq, bs)
  else if op = 0xA9 then
    (take32 bs).map fun (imm, bs) => (.test w (.reg .rax) (.imm imm), bs)
  else if op = 0xC1 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      (ShiftOp.ofCode reg).bind fun sop =>
        match bs with
        | n :: bs => some (.shift sop w rm (.imm n), bs)
        | [] => none
  else if op = 0xC3 then some (.ret, bs)
  else if op = 0xC7 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      if reg = 0 then (take32 bs).map fun (imm, bs) => (.mov w (.rm_i rm imm), bs) else none
  else if op = 0xD1 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      (ShiftOp.ofCode reg).map fun sop => (.shift sop w rm (.imm 1), bs)
  else if op = 0xD3 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      (ShiftOp.ofCode reg).map fun sop => (.shift sop w rm .cl, bs)
  else if op = 0xE8 then (take32 bs).map fun (d, bs) => (.call (.rel d), bs)
  else if op = 0xE9 then (take32 bs).map fun (d, bs) => (.jmp (.rel d), bs)
  else if op = 0xF7 then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      if reg = 0 then (take32 bs).map fun (imm, bs) => (.test w rm (.imm imm), bs)
      else if reg = 2 then some (.unary .not w rm, bs)
      else if reg = 3 then some (.unary .neg w rm, bs)
      else (MulDivOp.ofCode reg).map fun mop => (.mulDiv mop w rm, bs)
  else if op = 0xFF then
    (takeOperand rx bs).bind fun (reg, rm, bs) =>
      if reg = 2 then some (.call (.ind rm), bs)
      else if reg = 4 then some (.jmp (.ind rm), bs)
      else none
  else none

/-- Decodes one instruction from the front of a byte sequence, returning it
with the bytes that follow. -/
def decodeFrom (bs : List Byte) : Option (Instr × List Byte) :=
  let (f3, bs) : Bool × List Byte :=
    match bs with
    | p :: rest => if p.toNat = 0xF3 then (true, rest) else (false, p :: rest)
    | [] => (false, [])
  let (rx, bs) := takeRex bs
  match bs with
  | op :: bs => decodeOp f3 rx op.toNat bs
  | [] => none

/-- Decodes one instruction from the front of a byte sequence, returning it
with the number of bytes it occupied. -/
def decode (bs : List Byte) : Option (Instr × Nat) :=
  (decodeFrom bs).map fun (i, rest) => (i, bs.length - rest.length)

end TypedAsm
