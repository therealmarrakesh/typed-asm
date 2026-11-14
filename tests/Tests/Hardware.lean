import TypedAsm
import Tests.Encoding

/-!
# Snippets for the hardware tests

Short instruction sequences, each run from a set of starting values. Both
sides run the same bytes, produced by our encoder: the model decodes them
from its memory, and a real processor executes them. `tests/data/hardware.txt`
holds, line for line, what the processor did.

Every snippet runs with:

* `rax`, `rcx`, `rdx` and the four flags from the input
* `rsi`, `rdi` and `r11` zero
* `rbx` and `rsp` pointing into a writable page, `r10` holding 2
* the two 8-byte words at `[rbx]` and `[rbx+8]` from the input

and ends by falling off its last instruction.
-/

open TypedAsm

namespace Tests.Hardware

/-- The writable page. -/
def dataBase : BitVec 64 := 0x10000

/-- Where `rbx` and `rsp` point: the middle of the writable page. -/
def buffer : BitVec 64 := 0x10800

/-- Where snippets are placed. -/
def codeBase : BitVec 64 := 0x20000

/-- A page the capture tool uses to pass values in and out. -/
def ioBase : Nat := 0x30000

structure Input where
  a : BitVec 64
  b : BitVec 64
  d : BitVec 64
  /-- Carry, zero, sign and overflow as bits 0 to 3. -/
  flags : Nat
  m0 : BitVec 64
  m1 : BitVec 64

/-! ## Snippets -/

open Tests.Encoding (conds widths aluOps shiftOps mulOps)

def mems : List Mem :=
  [.sib (some .rbx) none 0, .sib (some .rbx) none 4, .sib (some .rbx) (some (.r10, .s4)) 0,
   .sib (some .rbx) (some (.r10, .s8)) (-9)]

def m0 : Mem := .sib (some .rbx) none 0

/-- The combined length of some instructions. -/
def lengthOf (is : List Instr) : Nat :=
  (is.map Instr.length).sum

/-- An offset that skips these instructions. -/
def skip (is : List Instr) : BitVec 32 :=
  BitVec.ofNat 32 (lengthOf is)

/-- Marks that control fell through to here. -/
def mark : Instr := .mov .w32 (.rm_i (.reg .rsi) 7)

/-- The address just past these instructions, when they start the snippet. -/
def addrAfter (is : List Instr) : BitVec 64 :=
  codeBase + BitVec.ofNat 64 (lengthOf is)

def single : List Instr :=
  (widths.flatMap fun w =>
    (aluOps.flatMap fun op =>
      [Instr.alu op w (.rm_r (.reg .rax) .rcx)] ++
      ([(1 : BitVec 32), -1, 0x7fffffff, -0x80000000, 1000].map fun i =>
        Instr.alu op w (.rm_i (.reg .rax) i)) ++
      (mems.flatMap fun m =>
        [Instr.alu op w (.rm_r (.mem m) .rcx), .alu op w (.r_m .rax m)]) ++
      ([(1 : BitVec 32), -1, 0x7fffffff, -0x80000000].map fun i =>
        Instr.alu op w (.rm_i (.mem m0) i))) ++
    [.test w (.reg .rax) (.reg .rcx), .test w (.reg .rax) (.imm (-256)),
     .test w (.mem m0) (.reg .rcx), .test w (.mem m0) (.imm (-256)),
     .unary .neg w (.reg .rax), .unary .neg w (.mem m0), .unary .not w (.reg .rax),
     .unary .not w (.mem m0)] ++
    (shiftOps.flatMap fun op =>
      [Instr.shift op w (.reg .rax) .cl, .shift op w (.mem m0) .cl] ++
      ([(0 : BitVec 8), 1, 2, 7, 31, 32, 33, 63, 64, 65, 255].map fun n =>
        Instr.shift op w (.reg .rax) (.imm n)) ++
      ([(0 : BitVec 8), 1, 5].map fun n => Instr.shift op w (.mem m0) (.imm n))) ++
    (mulOps.flatMap fun op =>
      [Instr.mulDiv op w (.reg .rcx), .mulDiv op w (.mem (.sib (some .rbx) none 8))]) ++
    [.imul2 w .rax (.reg .rcx), .imul2 w .rax (.mem m0), .imul3 w .rax (.reg .rcx) 3,
     .imul3 w .rax (.reg .rcx) (-7), .imul3 w .rax (.reg .rcx) 0x7fffffff,
     .imul3 w .rax (.mem m0) (-7), .popcnt w .rax (.reg .rcx), .popcnt w .rax (.mem m0),
     .bswap w .rax, .mov w (.rm_r (.reg .rax) .rcx), .mov w (.rm_i (.reg .rax) (-5))] ++
    (mems.flatMap fun m =>
      [Instr.mov w (.rm_r (.mem m) .rcx), .mov w (.r_m .rax m), .mov w (.rm_i (.mem m) (-5))]) ++
    [.movzx w .rax .w8 (.reg .rcx), .movzx w .rax .w16 (.reg .rcx),
     .movzx w .rax .w8 (.mem (.sib (some .rbx) none 3)),
     .movzx w .rax .w16 (.mem (.sib (some .rbx) none 3)),
     .movsx w .rax .w8 (.reg .rcx), .movsx w .rax .w16 (.reg .rcx),
     .movsx w .rax .w8 (.mem (.sib (some .rbx) none 3)),
     .movsx w .rax .w16 (.mem (.sib (some .rbx) none 3)),
     .lea w .rax (.sib (some .rcx) (some (.rdx, .s4)) (-100)),
     .lea w .rax (.sib none (some (.rdx, .s8)) 64), .lea w .rax (.rip 100)] ++
    (conds.flatMap fun c => [Instr.cmov c w .rax (.reg .rcx), .cmov c w .rax (.mem m0)])) ++
  [.cdq, .cqo, .movsxd .rax (.reg .rcx), .movsxd .rax (.mem (.sib (some .rbx) none 4)),
   .movAbs .rax 0x123456789abcdef0, .store8 (.sib (some .rbx) none 7) .rcx,
   .store8 (.sib (some .rbx) (some (.r10, .s4)) 0) .rax, .nop] ++
  (conds.flatMap fun c =>
    [Instr.setcc c (.reg .rax), .setcc c (.mem (.sib (some .rbx) none 5))]) ++
  ([Reg.rax, .rcx, .rdx, .rbx, .rsp].map Instr.push) ++
  ([Reg.rax, .rcx, .rdx, .rsp].map Instr.pop)

/-- Sequences that exercise control flow. `rsi` ends as 7 exactly when the
marked instruction was reached. -/
def control : List (List Instr) :=
  (conds.map fun c => [Instr.jcc c (skip [mark]), mark]) ++
  [ [.jmp (.rel (skip [mark])), mark],
    -- jump through a register
    (let pre := [Instr.movAbs .rax 0, .jmp (.ind (.reg .rax)), mark]
     [.movAbs .rax (addrAfter pre), .jmp (.ind (.reg .rax)), mark]),
    -- jump through memory
    (let pre := [Instr.movAbs .rax 0, .mov .w64 (.rm_r (.mem (.sib (some .rbx) none 16)) .rax),
       .jmp (.ind (.mem (.sib (some .rbx) none 16))), mark]
     [.movAbs .rax (addrAfter pre), .mov .w64 (.rm_r (.mem (.sib (some .rbx) none 16)) .rax),
      .jmp (.ind (.mem (.sib (some .rbx) none 16))), mark]),
    -- a call pushes the address of the next instruction
    [.call (.rel 0), .pop .rcx],
    [.call (.rel (skip [mark])), mark, .pop .rcx],
    -- call through a register
    (let pre := [Instr.movAbs .rax 0, .call (.ind (.reg .rax))]
     [.movAbs .rax (addrAfter pre), .call (.ind (.reg .rax)), .pop .rcx]),
    -- call through memory addressed by `rsp`, which is read before the push
    (let pre := [Instr.movAbs .rax 0, .mov .w64 (.rm_r (.mem (.sib (some .rsp) none 8)) .rax),
       .call (.ind (.mem (.sib (some .rsp) none 8)))]
     [.movAbs .rax (addrAfter pre), .mov .w64 (.rm_r (.mem (.sib (some .rsp) none 8)) .rax),
      .call (.ind (.mem (.sib (some .rsp) none 8))), .pop .rcx]),
    -- return to an address pushed by hand
    (let pre := [Instr.movAbs .rax 0, .push .rax, .ret, mark]
     [.movAbs .rax (addrAfter pre), .push .rax, .ret, mark]) ]

def snippets : List (List Instr) :=
  single.map (fun i => [i]) ++ control

/-! ## Inputs -/

def corners : List (BitVec 64) :=
  [0, 1, 2, 3, 5, 31, 32, 33, 63, 64, 65, 0xff, 0x7f, 0x80, 0x7fff, 0x8000, 0xffff, 0x7fffffff,
   0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
   0xffffffffffffffff, 0xfffffffffffffffe, 0xfffffffe, 7, 100, 0xffffffffffffff9d]

/-- A fixed sequence of scattered 64-bit values. -/
def scattered : List (BitVec 64) :=
  (List.range 48).map fun i =>
    BitVec.ofNat 64 ((i + 1) * 0x9E3779B97F4A7C15 + (i * i + 3) * 0xD1B54A32D192ED03)

def pool : Array (BitVec 64) := (corners ++ scattered).toArray

def pick (n : Nat) : BitVec 64 := pool[n % pool.size]!

/-- How many inputs each snippet is run on. -/
def inputsPer : Nat := 20

/-- The inputs for snippet number `i`. They differ from snippet to snippet
so that between them the snippets see many combinations. -/
def inputsFor (i : Nat) : List Input :=
  (List.range inputsPer).map fun k =>
    { a := pick (i * 3 + k), b := pick (i * 5 + 2 * k + 1), d := pick (i + 7 * k + 2),
      flags := (i + k) % 16, m0 := pick (i * 11 + 3 * k + 4), m1 := pick (i * 13 + 5 * k + 6) }

/-! ## What the model does -/

def bytesOf (snippet : List Instr) : List Byte :=
  snippet.flatMap Instr.encode

def initial (snippet : List Instr) (inp : Input) : State :=
  let s := State.init.setPerm dataBase 0x1000 .rw
  let s := (s.store64 buffer inp.m0).store64 (buffer + 8) inp.m1
  let s := s.setReg .rax inp.a |>.setReg .rcx inp.b |>.setReg .rdx inp.d |>.setReg .rbx buffer
    |>.setReg .rsp buffer |>.setReg .r10 2
  let bit (n : Nat) : Option Bool := some (inp.flags / n % 2 == 1)
  let s := { s with flags := ⟨bit 1, bit 2, bit 4, bit 8⟩ }
  { s.loadCode codeBase (bytesOf snippet) with rip := codeBase }

/-- Runs until `rip` reaches `stop`, for at most `fuel` steps. -/
def runTo (stop : BitVec 64) : Nat → State → Outcome
  | 0, _ => .stuck
  | fuel + 1, s =>
    if s.rip = stop then .next s
    else match stepMem (fun _ => .stuck) s with
      | .next s => runTo stop fuel s
      | o => o

def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def hex64 (v : BitVec 64) : String := hexNat v.toNat

def flagChar : Option Bool → Char
  | some true => '1'
  | some false => '0'
  | none => '?'

/-- One line describing what the model does with a snippet and an input. A
flag the model leaves unknown is shown as `?`. -/
def modelLine (snippet : List Instr) (inp : Input) : String :=
  match runTo (addrAfter snippet) 32 (initial snippet inp) with
  | .next s =>
    let fl := String.ofList [flagChar s.flags.cf, flagChar s.flags.zf, flagChar s.flags.sf,
      flagChar s.flags.of]
    let reg (r : Reg) := hex64 (s.getReg r)
    s!"ok {reg .rax} {reg .rcx} {reg .rdx} {reg .rsi} {reg .rdi} {reg .rsp} {fl} \
       {hex64 (s.load64 (buffer - 8))} {hex64 (s.load64 buffer)} {hex64 (s.load64 (buffer + 8))}"
  | .fault .divideError => "fault"
  | .fault f => s!"model: {repr f}"
  | .exit _ => "model: exit"
  | .stuck => "model: stuck"

/-- Whether a line from the processor agrees with a line from the model. -/
def agrees (model real : String) : Bool :=
  let m := model.splitOn " "
  let r := real.splitOn " "
  m.length == r.length &&
  (List.zip m r).all fun (x, y) =>
    x == y || (x.length == y.length && x.length == 4 &&
      (List.zip x.toList y.toList).all fun (c, e) => c == e || c == '?')

/-! ## What the capture tool needs -/

/-- An absolute address in the page used to pass values in and out. -/
def io (offset : Nat) : Mem := .sib none none (BitVec.ofNat 32 (ioBase + offset))

/-- Code placed after every snippet when it is run on a processor: store the
registers and flags where the capture tool can read them, restore its stack,
and return to it. All but two of its bytes come from our encoder. -/
def epilogue : List Byte :=
  ([Instr.mov .w64 (.rm_r (.mem (io 64)) .rax), .mov .w64 (.rm_r (.mem (io 72)) .rcx),
    .mov .w64 (.rm_r (.mem (io 80)) .rdx), .mov .w64 (.rm_r (.mem (io 88)) .rsi),
    .mov .w64 (.rm_r (.mem (io 96)) .rdi), .mov .w64 (.rm_r (.mem (io 104)) .rsp),
    .mov .w64 (.r_m .rsp (io 192))].flatMap Instr.encode)
  ++ [0x9C]  -- pushfq, which is not in our instruction set
  ++ ([Instr.pop .rax, .mov .w64 (.rm_r (.mem (io 112)) .rax),
       .jmp (.ind (.mem (io 200)))].flatMap Instr.encode)

/-- The line the capture tool reads for one case: the bytes to run, then the inputs. -/
def caseLine (snippet : List Instr) (inp : Input) : String :=
  let rflags := 0x202 + (if inp.flags % 2 == 1 then 1 else 0)
    + (if inp.flags / 2 % 2 == 1 then 0x40 else 0) + (if inp.flags / 4 % 2 == 1 then 0x80 else 0)
    + (if inp.flags / 8 % 2 == 1 then 0x800 else 0)
  s!"{Tests.Encoding.hex (bytesOf snippet ++ epilogue)} {hex64 inp.a} {hex64 inp.b} \
     {hex64 inp.d} {hexNat rflags} {hex64 inp.m0} {hex64 inp.m1}"

/-- Every case, in the order of the data file. -/
def cases : List (List Instr × Input) :=
  (List.zip snippets (List.range snippets.length)).flatMap fun (sn, i) =>
    (inputsFor i).map fun inp => (sn, inp)

end Tests.Hardware
