import TypedAsm.Instr

/-!
# Printing instructions

Instructions as assembly text, in Intel syntax. Used for error messages and
for inspecting programs; nothing depends on the exact format.
-/

namespace TypedAsm

def Reg.name64 : Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

def Reg.name32 : Reg → String
  | .rax => "eax" | .rcx => "ecx" | .rdx => "edx" | .rbx => "ebx"
  | .rsp => "esp" | .rbp => "ebp" | .rsi => "esi" | .rdi => "edi"
  | r => r.name64 ++ "d"

def Reg.name16 : Reg → String
  | .rax => "ax" | .rcx => "cx" | .rdx => "dx" | .rbx => "bx"
  | .rsp => "sp" | .rbp => "bp" | .rsi => "si" | .rdi => "di"
  | r => r.name64 ++ "w"

def Reg.name8 : Reg → String
  | .rax => "al" | .rcx => "cl" | .rdx => "dl" | .rbx => "bl"
  | .rsp => "spl" | .rbp => "bpl" | .rsi => "sil" | .rdi => "dil"
  | r => r.name64 ++ "b"

def Reg.name (w : Width) (r : Reg) : String :=
  match w with
  | .w32 => r.name32
  | .w64 => r.name64

def Scale.toNat : Scale → Nat
  | .s1 => 1 | .s2 => 2 | .s4 => 4 | .s8 => 8

/-- A displacement as a signed term: `+16`, `-8`, or nothing for zero. -/
def dispText (first : Bool) (d : BitVec 32) : String :=
  let i := d.toInt
  if i == 0 then (if first then "0" else "")
  else if i < 0 then s!"-{-i}"
  else if first then s!"{i}" else s!"+{i}"

def Mem.toAsm : Mem → String
  | .rip disp => s!"[rip{dispText false disp}]"
  | .sib base index disp =>
    let b := match base with
      | some r => r.name64
      | none => ""
    let i := match index with
      | some (r, sc) => (if b == "" then "" else "+") ++ s!"{r.toReg.name64}*{sc.toNat}"
      | none => ""
    s!"[{b}{i}{dispText (b == "" && i == "") disp}]"

def Width.ptr : Width → String
  | .w32 => "dword ptr "
  | .w64 => "qword ptr "

def NarrowW.ptr : NarrowW → String
  | .w8 => "byte ptr "
  | .w16 => "word ptr "

def RM.toAsm (w : Width) : RM → String
  | .reg r => r.name w
  | .mem m => w.ptr ++ m.toAsm

def Cond.suffix : Cond → String
  | .o => "o" | .no => "no" | .b => "b" | .ae => "ae" | .e => "e" | .ne => "ne"
  | .be => "be" | .a => "a" | .s => "s" | .ns => "ns" | .l => "l" | .ge => "ge"
  | .le => "le" | .g => "g"

def AluOp.mnemonic : AluOp → String
  | .add => "add" | .sub => "sub" | .adc => "adc" | .sbb => "sbb"
  | .and => "and" | .or => "or" | .xor => "xor" | .cmp => "cmp"

def Operands.toAsm (w : Width) : Operands → String
  | .rm_r dst src => s!"{dst.toAsm w}, {src.name w}"
  | .r_m dst src => s!"{dst.name w}, {w.ptr}{src.toAsm}"
  | .rm_i dst imm => s!"{dst.toAsm w}, {imm.toInt}"

/-- An instruction as assembly text. Jump and call targets are shown as
offsets from the next instruction. -/
def Instr.toAsm : Instr → String
  | .alu op w ops => s!"{op.mnemonic} {ops.toAsm w}"
  | .test w dst (.reg r) => s!"test {dst.toAsm w}, {r.name w}"
  | .test w dst (.imm i) => s!"test {dst.toAsm w}, {i.toInt}"
  | .unary .neg w dst => s!"neg {dst.toAsm w}"
  | .unary .not w dst => s!"not {dst.toAsm w}"
  | .shift op w dst c =>
    let m := match op with
      | .shl => "shl" | .shr => "shr" | .sar => "sar" | .rol => "rol" | .ror => "ror"
    let n := match c with
      | .imm n => toString n.toNat
      | .cl => "cl"
    s!"{m} {dst.toAsm w}, {n}"
  | .mulDiv op w src =>
    let m := match op with
      | .mul => "mul" | .imul => "imul" | .div => "div" | .idiv => "idiv"
    s!"{m} {src.toAsm w}"
  | .imul2 w dst src => s!"imul {dst.name w}, {src.toAsm w}"
  | .imul3 w dst src imm => s!"imul {dst.name w}, {src.toAsm w}, {imm.toInt}"
  | .popcnt w dst src => s!"popcnt {dst.name w}, {src.toAsm w}"
  | .bswap w r => s!"bswap {r.name w}"
  | .cdq => "cdq"
  | .cqo => "cqo"
  | .mov w ops => s!"mov {ops.toAsm w}"
  | .movAbs dst imm => s!"movabs {dst.name64}, {imm.toNat}"
  | .store8 dst src => s!"mov byte ptr {dst.toAsm}, {src.name8}"
  | .store16 dst src => s!"mov word ptr {dst.toAsm}, {src.name16}"
  | .movzx w dst sw (.reg r) =>
    s!"movzx {dst.name w}, {match sw with | .w8 => r.name8 | .w16 => r.name16}"
  | .movzx w dst sw (.mem m) => s!"movzx {dst.name w}, {sw.ptr}{m.toAsm}"
  | .movsx w dst sw (.reg r) =>
    s!"movsx {dst.name w}, {match sw with | .w8 => r.name8 | .w16 => r.name16}"
  | .movsx w dst sw (.mem m) => s!"movsx {dst.name w}, {sw.ptr}{m.toAsm}"
  | .movsxd dst src => s!"movsxd {dst.name64}, {src.toAsm .w32}"
  | .lea w dst addr => s!"lea {dst.name w}, {addr.toAsm}"
  | .cmov c w dst src => s!"cmov{c.suffix} {dst.name w}, {src.toAsm w}"
  | .setcc c (.reg r) => s!"set{c.suffix} {r.name8}"
  | .setcc c (.mem m) => s!"set{c.suffix} byte ptr {m.toAsm}"
  | .push r => s!"push {r.name64}"
  | .pop r => s!"pop {r.name64}"
  | .jmp (.rel d) => s!"jmp {dispText true d}"
  | .jmp (.ind rm) => s!"jmp {rm.toAsm .w64}"
  | .jcc c d => s!"j{c.suffix} {dispText true d}"
  | .call (.rel d) => s!"call {dispText true d}"
  | .call (.ind rm) => s!"call {rm.toAsm .w64}"
  | .ret => "ret"
  | .nop => "nop"
  | .ud2 => "ud2"
  | .syscall => "syscall"

end TypedAsm
