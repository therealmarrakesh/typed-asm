import TypedAsm.Instr

/-!
# Encoding instructions

Each instruction as the bytes an x86-64 processor reads. Every instruction
has exactly one encoding here, chosen to be the one an assembler normally
emits: the shortest displacement that fits, the short immediate forms, and a
`REX` prefix only when one is needed.

Relative jumps and calls always use a 32-bit offset.
-/

namespace TypedAsm

abbrev Byte := BitVec 8

/-- The 4-bit number the hardware uses for a register. -/
def Reg.num : Reg → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3 | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14
  | .r15 => 15

/-- The low three bits of a register's number, which go in the instruction proper. -/
def Reg.low (r : Reg) : Nat := r.num % 8

/-- The top bit of a register's number, which goes in the `REX` prefix. -/
def Reg.ext (r : Reg) : Bool := decide (8 ≤ r.num)

/-- Whether using the register's low byte needs a `REX` prefix: without one,
numbers 4 to 7 mean `ah`, `ch`, `dh`, `bh` instead of `spl`, `bpl`, `sil`, `dil`. -/
def Reg.byteNeedsRex (r : Reg) : Bool := decide (4 ≤ r.num ∧ r.num < 8)

/-- The 4-bit number the hardware uses for a condition. -/
def Cond.code : Cond → Nat
  | .o => 0 | .no => 1 | .b => 2 | .ae => 3 | .e => 4 | .ne => 5 | .be => 6 | .a => 7
  | .s => 8 | .ns => 9 | .l => 12 | .ge => 13 | .le => 14 | .g => 15

/-- The 3-bit number that selects among the two-operand arithmetic operations. -/
def AluOp.code : AluOp → Nat
  | .add => 0 | .or => 1 | .adc => 2 | .sbb => 3 | .and => 4 | .sub => 5 | .xor => 6 | .cmp => 7

def ShiftOp.code : ShiftOp → Nat
  | .rol => 0 | .ror => 1 | .shl => 4 | .shr => 5 | .sar => 7

def MulDivOp.code : MulDivOp → Nat
  | .mul => 4 | .imul => 5 | .div => 6 | .idiv => 7

def Scale.code : Scale → Nat
  | .s1 => 0 | .s2 => 1 | .s4 => 2 | .s8 => 3

def byte (n : Nat) : Byte := BitVec.ofNat 8 n

/-- A 32-bit value as four bytes, least significant first. -/
def le32 (v : BitVec 32) : List Byte :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8]

/-- A 64-bit value as eight bytes, least significant first. -/
def le64 (v : BitVec 64) : List Byte :=
  le32 (v.extractLsb' 0 32) ++ le32 (v.extractLsb' 32 32)

/-- Whether a 32-bit value is the sign extension of its low byte. -/
def fits8 (v : BitVec 32) : Bool :=
  (v.setWidth 8).signExtend 32 == v

/-- The low byte of a value that fits in one. -/
def imm8 (v : BitVec 32) : List Byte :=
  [v.setWidth 8]

/-- The `ModRM` byte: a 2-bit mode, a 3-bit register or opcode field, and a
3-bit register-or-memory field. -/
def modrmByte (mode reg rm : Nat) : Byte :=
  byte (mode * 64 + (reg % 8) * 8 + rm % 8)

/-- The `SIB` byte: scale, index and base. -/
def sibByte (scale index base : Nat) : Byte :=
  byte (scale * 64 + (index % 8) * 8 + base % 8)

/-- The encoding of an operand: the bytes after the opcode, and the two
`REX` bits that extend its index and base registers. -/
structure OperandBytes where
  x : Bool
  b : Bool
  bytes : List Byte

/-- The `ModRM` mode and the bytes for a displacement from base register `b`:
the shortest that fits. A base of `rbp` or `r13` cannot have none, because
that bit pattern means something else. -/
def dispEnc (b : Reg) (disp : BitVec 32) : Nat × List Byte :=
  if disp == 0 && b.low != 5 then (0, [])
  else if fits8 disp then (1, imm8 disp)
  else (2, le32 disp)

/-- A memory operand, with `reg` in the register field of the `ModRM` byte. -/
def Mem.encode (reg : Nat) : Mem → OperandBytes
  | .rip disp => ⟨false, false, modrmByte 0 reg 5 :: le32 disp⟩
  | .sib none none disp => ⟨false, false, [modrmByte 0 reg 4, sibByte 0 4 5] ++ le32 disp⟩
  | .sib none (some (i, s)) disp =>
    ⟨i.toReg.ext, false, [modrmByte 0 reg 4, sibByte s.code i.toReg.num 5] ++ le32 disp⟩
  | .sib (some b) index disp =>
    let mode := (dispEnc b disp).1
    let dispBytes := (dispEnc b disp).2
    match index with
    | none =>
      -- A base of `rsp` or `r12` needs a `SIB` byte.
      if b.low == 4 then ⟨false, b.ext, [modrmByte mode reg 4, sibByte 0 4 4] ++ dispBytes⟩
      else ⟨false, b.ext, modrmByte mode reg b.num :: dispBytes⟩
    | some (i, s) =>
      ⟨i.toReg.ext, b.ext, [modrmByte mode reg 4, sibByte s.code i.toReg.num b.num] ++ dispBytes⟩

/-- A register-or-memory operand, with `reg` in the register field. -/
def RM.encode (reg : Nat) : RM → OperandBytes
  | .reg r => ⟨false, r.ext, [modrmByte 3 reg r.num]⟩
  | .mem m => m.encode reg

/-- The `REX` prefix, present only if one of its bits is set or it is forced. -/
def rex (w r x b : Bool) (force : Bool := false) : List Byte :=
  if w || r || x || b || force then
    [byte (0x40 + (if w then 8 else 0) + (if r then 4 else 0) + (if x then 2 else 0)
      + (if b then 1 else 0))]
  else []

def Width.rexW : Width → Bool
  | .w32 => false
  | .w64 => true

/-- An instruction of the common shape: optional prefix, `REX`, opcode, then
an operand with a register or opcode extension in its register field. -/
def encodeOp (w : Bool) (opcode : List Byte) (reg : Nat) (regExt : Bool) (rm : RM)
    (force : Bool := false) (pre : List Byte := []) : List Byte :=
  let m := rm.encode reg
  pre ++ rex w regExt m.x m.b force ++ opcode ++ m.bytes

/-- Whether a register-or-memory operand is a register whose low byte needs `REX`. -/
def RM.byteNeedsRex : RM → Bool
  | .reg r => r.byteNeedsRex
  | .mem _ => false

/-- The bytes of an instruction. -/
def Instr.encode : Instr → List Byte
  -- arithmetic and logic
  | .alu op w (.rm_r dst src) => encodeOp w.rexW [byte (op.code * 8 + 1)] src.num src.ext dst
  | .alu op w (.r_m dst src) => encodeOp w.rexW [byte (op.code * 8 + 3)] dst.num dst.ext (.mem src)
  | .alu op w (.rm_i dst imm) =>
    if fits8 imm then encodeOp w.rexW [0x83] op.code false dst ++ imm8 imm
    else if dst = .reg .rax then rex w.rexW false false false ++ [byte (op.code * 8 + 5)] ++ le32 imm
    else encodeOp w.rexW [0x81] op.code false dst ++ le32 imm
  | .test w dst (.reg r) => encodeOp w.rexW [0x85] r.num r.ext dst
  | .test w dst (.imm i) =>
    if dst = .reg .rax then rex w.rexW false false false ++ [0xA9] ++ le32 i
    else encodeOp w.rexW [0xF7] 0 false dst ++ le32 i
  | .unary .not w dst => encodeOp w.rexW [0xF7] 2 false dst
  | .unary .neg w dst => encodeOp w.rexW [0xF7] 3 false dst
  | .shift op w dst (.imm n) =>
    if n == 1 then encodeOp w.rexW [0xD1] op.code false dst
    else encodeOp w.rexW [0xC1] op.code false dst ++ [n]
  | .shift op w dst .cl => encodeOp w.rexW [0xD3] op.code false dst
  | .mulDiv op w src => encodeOp w.rexW [0xF7] op.code false src
  | .imul2 w dst src => encodeOp w.rexW [0x0F, 0xAF] dst.num dst.ext src
  | .imul3 w dst src imm =>
    if fits8 imm then encodeOp w.rexW [0x6B] dst.num dst.ext src ++ imm8 imm
    else encodeOp w.rexW [0x69] dst.num dst.ext src ++ le32 imm
  | .popcnt w dst src => encodeOp w.rexW [0x0F, 0xB8] dst.num dst.ext src (pre := [0xF3])
  | .bswap w r => rex w.rexW false false r.ext ++ [0x0F, byte (0xC8 + r.low)]
  | .cdq => [0x99]
  | .cqo => [0x48, 0x99]
  -- data movement
  | .mov w (.rm_r dst src) => encodeOp w.rexW [0x89] src.num src.ext dst
  | .mov w (.r_m dst src) => encodeOp w.rexW [0x8B] dst.num dst.ext (.mem src)
  | .mov .w32 (.rm_i (.reg r) imm) => rex false false false r.ext ++ [byte (0xB8 + r.low)] ++ le32 imm
  | .mov w (.rm_i dst imm) => encodeOp w.rexW [0xC7] 0 false dst ++ le32 imm
  | .movAbs dst imm => rex true false false dst.ext ++ [byte (0xB8 + dst.low)] ++ le64 imm
  | .store8 dst src => encodeOp false [0x88] src.num src.ext (.mem dst) (force := src.byteNeedsRex)
  | .movzx w dst .w8 src =>
    encodeOp w.rexW [0x0F, 0xB6] dst.num dst.ext src (force := src.byteNeedsRex)
  | .movzx w dst .w16 src => encodeOp w.rexW [0x0F, 0xB7] dst.num dst.ext src
  | .movsx w dst .w8 src =>
    encodeOp w.rexW [0x0F, 0xBE] dst.num dst.ext src (force := src.byteNeedsRex)
  | .movsx w dst .w16 src => encodeOp w.rexW [0x0F, 0xBF] dst.num dst.ext src
  | .movsxd dst src => encodeOp true [0x63] dst.num dst.ext src
  | .lea w dst addr => encodeOp w.rexW [0x8D] dst.num dst.ext (.mem addr)
  | .cmov c w dst src => encodeOp w.rexW [0x0F, byte (0x40 + c.code)] dst.num dst.ext src
  | .setcc c dst => encodeOp false [0x0F, byte (0x90 + c.code)] 0 false dst (force := dst.byteNeedsRex)
  | .push r => rex false false false r.ext ++ [byte (0x50 + r.low)]
  | .pop r => rex false false false r.ext ++ [byte (0x58 + r.low)]
  -- control flow
  | .jmp (.rel d) => 0xE9 :: le32 d
  | .jmp (.ind rm) => encodeOp false [0xFF] 4 false rm
  | .jcc c d => [0x0F, byte (0x80 + c.code)] ++ le32 d
  | .call (.rel d) => 0xE8 :: le32 d
  | .call (.ind rm) => encodeOp false [0xFF] 2 false rm
  | .ret => [0xC3]
  -- miscellaneous
  | .nop => [0x90]
  | .ud2 => [0x0F, 0x0B]
  | .syscall => [0x0F, 0x05]

/-- The number of bytes an instruction occupies. -/
def Instr.length (i : Instr) : Nat :=
  i.encode.length

end TypedAsm
