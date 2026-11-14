/-!
# Instruction syntax

The restricted x86-64 instruction set as plain data. Nothing here gives the
instructions meaning; semantics, encoding and typing are defined over `Instr`
elsewhere.
-/

namespace TypedAsm

/-- The sixteen 64-bit general-purpose registers, in hardware encoding order. -/
inductive Reg
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

/-- Operand width for computation. A 32-bit write zero-extends into the full register. -/
inductive Width
  | w32 | w64
  deriving DecidableEq, Repr

/-- Narrow widths, available only as the source of an extending load. -/
inductive NarrowW
  | w8 | w16
  deriving DecidableEq, Repr

/-- Condition codes (the fourteen that do not involve the parity flag). -/
inductive Cond
  | o | no | b | ae | e | ne | be | a | s | ns | l | ge | le | g
  deriving DecidableEq, Repr

/-- Index-register scale factor. -/
inductive Scale
  | s1 | s2 | s4 | s8
  deriving DecidableEq, Repr

/-- Registers usable as an index in an address. Every register except `rsp`,
which the hardware cannot encode in that position. -/
inductive IndexReg
  | rax | rcx | rdx | rbx | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

def IndexReg.toReg : IndexReg → Reg
  | .rax => .rax | .rcx => .rcx | .rdx => .rdx | .rbx => .rbx
  | .rbp => .rbp | .rsi => .rsi | .rdi => .rdi
  | .r8 => .r8 | .r9 => .r9 | .r10 => .r10 | .r11 => .r11
  | .r12 => .r12 | .r13 => .r13 | .r14 => .r14 | .r15 => .r15

/-- An address expression. -/
inductive Mem
  /-- `[base + index*scale + disp]` -/
  | sib (base : Option Reg) (index : Option (IndexReg × Scale)) (disp : BitVec 32)
  /-- `[rip + disp]` -/
  | rip (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- A register or a memory location. -/
inductive RM
  | reg (r : Reg)
  | mem (m : Mem)
  deriving DecidableEq, Repr

/-- Two-operand shapes. There is no memory-to-memory form by construction. -/
inductive Operands
  | rm_r (dst : RM) (src : Reg)
  | r_m (dst : Reg) (src : Mem)
  | rm_i (dst : RM) (imm : BitVec 32)
  deriving DecidableEq, Repr

/-- A register or an immediate. -/
inductive RI
  | reg (r : Reg)
  | imm (i : BitVec 32)
  deriving DecidableEq, Repr

/-- Two-operand arithmetic and logic. `cmp` writes only the flags. -/
inductive AluOp
  | add | sub | adc | sbb | and | or | xor | cmp
  deriving DecidableEq, Repr

inductive UnOp
  | neg | not
  deriving DecidableEq, Repr

inductive ShiftOp
  | shl | shr | sar | rol | ror
  deriving DecidableEq, Repr

/-- Widening multiply and divide through `rdx:rax`. -/
inductive MulDivOp
  | mul | imul | div | idiv
  deriving DecidableEq, Repr

/-- A shift count: an immediate or the `cl` register. -/
inductive Count
  | imm (n : BitVec 8)
  | cl
  deriving DecidableEq, Repr

/-- A jump or call target: relative to the next instruction, or indirect. -/
inductive Target
  | rel (d : BitVec 32)
  | ind (rm : RM)
  deriving DecidableEq, Repr

inductive Instr
  -- arithmetic and logic
  | alu (op : AluOp) (w : Width) (ops : Operands)
  /-- Bitwise AND that writes only the flags. It has no register-from-memory form. -/
  | test (w : Width) (dst : RM) (src : RI)
  | unary (op : UnOp) (w : Width) (dst : RM)
  | shift (op : ShiftOp) (w : Width) (dst : RM) (c : Count)
  | mulDiv (op : MulDivOp) (w : Width) (src : RM)
  | imul2 (w : Width) (dst : Reg) (src : RM)
  | imul3 (w : Width) (dst : Reg) (src : RM) (imm : BitVec 32)
  | popcnt (w : Width) (dst : Reg) (src : RM)
  | bswap (w : Width) (r : Reg)
  | cdq
  | cqo
  -- data movement
  | mov (w : Width) (ops : Operands)
  | movAbs (dst : Reg) (imm : BitVec 64)
  | store8 (dst : Mem) (src : Reg)
  | store16 (dst : Mem) (src : Reg)
  | movzx (w : Width) (dst : Reg) (sw : NarrowW) (src : RM)
  | movsx (w : Width) (dst : Reg) (sw : NarrowW) (src : RM)
  | movsxd (dst : Reg) (src : RM)
  | lea (w : Width) (dst : Reg) (addr : Mem)
  | cmov (c : Cond) (w : Width) (dst : Reg) (src : RM)
  | setcc (c : Cond) (dst : RM)
  | push (r : Reg)
  | pop (r : Reg)
  -- control flow
  | jmp (t : Target)
  | jcc (c : Cond) (rel : BitVec 32)
  | call (t : Target)
  | ret
  -- miscellaneous
  | nop
  | ud2
  | syscall
  deriving DecidableEq, Repr

/-- `add rax, [rbx + rcx*8 + 16]` -/
example : Instr :=
  .alu .add .w64 (.r_m .rax (.sib (some .rbx) (some (.rcx, .s8)) 16))

end TypedAsm
