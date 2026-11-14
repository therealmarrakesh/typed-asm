import TypedAsm

/-!
# Instructions for the encoder tests

A broad, fixed list of instructions. `tests/data/encoding.txt` holds, line
for line, the bytes the GNU assembler produces for each. The list and the
data file must be regenerated together.
-/

open TypedAsm

namespace Tests.Encoding

def regs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def conds : List Cond := [.o, .no, .b, .ae, .e, .ne, .be, .a, .s, .ns, .l, .ge, .le, .g]

def widths : List Width := [.w32, .w64]

def aluOps : List AluOp := [.add, .sub, .adc, .sbb, .and, .or, .xor, .cmp]

def shiftOps : List ShiftOp := [.shl, .shr, .sar, .rol, .ror]

def mulOps : List MulDivOp := [.mul, .imul, .div, .idiv]

/-- Displacements on both sides of each size boundary. -/
def disps : List (BitVec 32) := [0, 1, -1, 127, -128, 128, -129, 0x12345678, -0x80000000]

/-- Bases that need special encodings (`rsp`, `rbp`, `r12`, `r13`) and ones that do not. -/
def bases : List (Option Reg) :=
  [none, some .rax, some .rsp, some .rbp, some .r12, some .r13, some .rdi, some .r9]

def indexes : List (Option (IndexReg × Scale)) :=
  [none, some (.rcx, .s1), some (.rdx, .s4), some (.r10, .s8), some (.r13, .s2), some (.rbp, .s2),
   some (.r12, .s4), some (.rax, .s2)]

def mems : List Mem :=
  (bases.flatMap fun b => indexes.flatMap fun i => disps.map fun d => Mem.sib b i d)
    ++ disps.map Mem.rip

def imms : List (BitVec 32) := [1, -1, 127, 128, -128, -129, 1000, 0x7fffffff, -0x80000000]

def instrs : List Instr :=
  -- register-register forms
  (regs.flatMap fun d => regs.flatMap fun s =>
    (widths.flatMap fun w => [
      Instr.alu .add w (.rm_r (.reg d) s), .alu .cmp w (.rm_r (.reg d) s),
      .mov w (.rm_r (.reg d) s), .test w (.reg d) (.reg s), .imul2 w d (.reg s),
      .cmov .e w d (.reg s), .popcnt w d (.reg s), .movzx w d .w8 (.reg s),
      .movzx w d .w16 (.reg s), .movsx w d .w8 (.reg s), .movsx w d .w16 (.reg s),
      .imul3 w d (.reg s) 3, .imul3 w d (.reg s) 1000]) ++ [.movsxd d (.reg s)]) ++
  -- single-register forms
  (regs.flatMap fun r =>
    [Instr.push r, .pop r, .movAbs r 0x1122334455667788, .movAbs r 5, .jmp (.ind (.reg r)),
     .call (.ind (.reg r))] ++
    conds.map (fun c => Instr.setcc c (.reg r)) ++
    (widths.flatMap fun w =>
      [Instr.bswap w r, .unary .neg w (.reg r), .unary .not w (.reg r), .test w (.reg r) (.imm 5),
       .test w (.reg r) (.imm (-1000)), .mov w (.rm_i (.reg r) 5),
       .mov w (.rm_i (.reg r) (-1000))] ++
      (shiftOps.flatMap fun op => [Instr.shift op w (.reg r) (.imm 1),
        .shift op w (.reg r) (.imm 5), .shift op w (.reg r) (.imm 0), .shift op w (.reg r) .cl]) ++
      mulOps.map (fun op => Instr.mulDiv op w (.reg r)) ++
      (aluOps.flatMap fun op => imms.map fun i => Instr.alu op w (.rm_i (.reg r) i)))) ++
  -- memory forms
  (mems.flatMap fun m => ([Reg.rax, .rsi, .r9].flatMap fun r =>
    [Instr.store8 m r] ++ (widths.flatMap fun w => [
      Instr.alu .add w (.rm_r (.mem m) r), .alu .sub w (.r_m r m), .mov w (.rm_r (.mem m) r),
      .mov w (.r_m r m), .test w (.mem m) (.reg r), .imul2 w r (.mem m),
      .imul3 w r (.mem m) (-7), .popcnt w r (.mem m), .movzx w r .w8 (.mem m),
      .movzx w r .w16 (.mem m), .movsx w r .w8 (.mem m), .movsx w r .w16 (.mem m), .lea w r m,
      .cmov .g w r (.mem m)]) ++ [.movsxd r (.mem m)]) ++
    (widths.flatMap fun w => [
      Instr.alu .and w (.rm_i (.mem m) 5), .alu .xor w (.rm_i (.mem m) 1000),
      .mov w (.rm_i (.mem m) 5), .test w (.mem m) (.imm 5), .unary .neg w (.mem m),
      .unary .not w (.mem m), .shift .shl w (.mem m) (.imm 1), .shift .sar w (.mem m) (.imm 3),
      .shift .ror w (.mem m) .cl, .mulDiv .mul w (.mem m), .mulDiv .idiv w (.mem m)]) ++
    [Instr.setcc .ne (.mem m), .jmp (.ind (.mem m)), .call (.ind (.mem m))]) ++
  -- no operands, and relative control flow
  [Instr.cdq, .cqo, .ret, .nop, .ud2, .syscall] ++
  ([(1000 : BitVec 32), -1000, 0x12345678, -0x12345678].flatMap fun d =>
    [Instr.jmp (.rel d), .call (.rel d)] ++ conds.map fun c => Instr.jcc c d)

/-- Assembly text for an instruction, in a form the assembler encodes with a
32-bit offset where there is a choice. -/
def asmText : Instr → String
  | .jmp (.rel d) => s!"jmp .+{d.toInt + 5}"
  | .call (.rel d) => s!"call .+{d.toInt + 5}"
  | .jcc c d => s!"j{c.suffix} .+{d.toInt + 6}"
  | i => i.toAsm

def hexByte (b : Byte) : String :=
  let s := Nat.toDigits 16 b.toNat
  String.ofList (if s.length == 1 then '0' :: s else s)

def hex (bytes : List Byte) : String :=
  String.join (bytes.map hexByte)

end Tests.Encoding
