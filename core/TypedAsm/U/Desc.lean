import TypedAsm.Step

/-!
# Instructions, described

Every instruction that goes on to the next does the same kind of thing. It
uses the values of some registers, perhaps the address its memory operand
names and the bytes there; it computes; and it leaves new values in some
registers, new flags, and perhaps new bytes at that address. No instruction
touches memory in more than one place.

Here each such instruction is given as that: which registers it uses, which
address, how many bytes there and whether they are read or written, and its
function. One statement then says what the machine does with any of them,
and one says how any of them is typed. An instruction is not typed by a rule
of its own.
-/

namespace TypedAsm.U

/-- What an instruction leaves: registers given new values, the later
winning; the flags; and the value its bytes of memory are given, where it
writes them. -/
structure Effect where
  regs : List (Reg × BitVec 64)
  flags : Flags
  store : BitVec 64 := 0

/-- An instruction as what it uses and what it does with it. The function
is given the values of `srcs` in order, the flags, the address of `addr` and
the bytes there as a number. -/
structure Desc1 where
  /-- The registers whose values the instruction computes with. -/
  srcs : List Reg
  /-- The memory operand whose address it uses. -/
  addr : Option Mem := none
  /-- How many bytes it touches there. -/
  bytes : Nat := 0
  reads : Bool := false
  writes : Bool := false
  /-- Whether it does not fault for a reason of its own: a carry it needs
  is defined, a divisor is not zero. -/
  guard : List (BitVec 64) → Flags → BitVec 64 → BitVec 64 → Bool := fun _ _ _ _ => true
  run : List (BitVec 64) → Flags → BitVec 64 → BitVec 64 → Effect

/-- The bytes of a width. -/
def wbytes : Width → Nat
  | .w32 => 4
  | .w64 => 8

def nbytes : NarrowW → Nat
  | .w8 => 1
  | .w16 => 2

/-- The registers an operand names. -/
def rmRegs : RM → List Reg
  | .reg r => [r]
  | .mem _ => []

def rmMem : RM → Option Mem
  | .reg _ => none
  | .mem m => some m

/-- The value of an operand: the register's, which is the `k`th used, or
the bytes of memory. -/
def rmVal (x : RM) (k : Nat) (vals : List (BitVec 64)) (cell : BitVec 64) : BitVec 64 :=
  match x with
  | .reg _ => vals.getD k 0
  | .mem _ => cell

/-- An operand given a value: the register, or the bytes of memory. -/
def rmSet (x : RM) (v : BitVec 64) (flags : Flags) (more : List (Reg × BitVec 64) := []) : Effect :=
  match x with
  | .reg r => ⟨(r, v) :: more, flags, 0⟩
  | .mem _ => ⟨more, flags, v⟩

/-- The source of a two-operand form: its register, used after the
destination's; the bytes of memory; or its immediate. -/
def srcRegs : Operands → List Reg
  | .rm_r _ s => [s]
  | _ => []

def srcVal (w : Width) (ops : Operands) (vals : List (BitVec 64)) (cell : BitVec 64) :
    BitVec w.bits :=
  match ops with
  | .rm_r d _ => (vals.getD (rmRegs d).length 0).setWidth w.bits
  | .r_m _ _ => cell.setWidth w.bits
  | .rm_i _ imm => imm.signExtend w.bits

def opsMem : Operands → Option Mem
  | .rm_r d _ => rmMem d
  | .r_m _ m => some m
  | .rm_i d _ => rmMem d

/-- The address of the top of the stack once eight bytes are pushed. -/
def pushMem : Mem := .sib (some .rsp) none (-8)

def topMem : Mem := .sib (some .rsp) none 0

/-- A register written at a width: the low half with the high half cleared,
or the whole. -/
def wide {w : Width} (v : BitVec w.bits) : BitVec 64 := v.setWidth 64

/-- **Each instruction that goes on to the next, described.** Nothing for
those that pass control elsewhere, call the system, or are not to be
reached. -/
def _root_.TypedAsm.Instr.desc1 : Instr → Option Desc1
  | .alu op w ops =>
    let d := ops.dst
    some {
      srcs := rmRegs d ++ srcRegs ops
      addr := opsMem ops
      bytes := wbytes w
      reads := (opsMem ops).isSome
      writes := (rmMem d).isSome && op.writesDst
      guard := fun vals fl _ cell =>
        (op.eval fl.cf ((rmVal d 0 vals cell).setWidth w.bits) (srcVal w ops vals cell)).isSome
      run := fun vals fl _ cell =>
        let a := (rmVal d 0 vals cell).setWidth w.bits
        let (r, f) := (op.eval fl.cf a (srcVal w ops vals cell)).getD (a, fl)
        if op.writesDst then rmSet d (wide r) f else ⟨[], f, 0⟩ }
  | .test w dst src =>
    some {
      srcs := rmRegs dst ++ (match src with | .reg r => [r] | .imm _ => [])
      addr := rmMem dst
      bytes := wbytes w
      reads := (rmMem dst).isSome
      run := fun vals fl _ cell =>
        let b : BitVec w.bits := match src with
          | .reg _ => (vals.getD (rmRegs dst).length 0).setWidth w.bits
          | .imm i => i.signExtend w.bits
        ⟨[], .ofResult ((rmVal dst 0 vals cell).setWidth w.bits &&& b) false false, 0⟩ }
  | .unary .neg w dst =>
    some {
      srcs := rmRegs dst, addr := rmMem dst, bytes := wbytes w
      reads := (rmMem dst).isSome, writes := (rmMem dst).isSome
      run := fun vals _ _ cell =>
        let (r, f) := subBorrow 0 ((rmVal dst 0 vals cell).setWidth w.bits) false
        rmSet dst (wide r) f }
  | .unary .not w dst =>
    some {
      srcs := rmRegs dst, addr := rmMem dst, bytes := wbytes w
      reads := (rmMem dst).isSome, writes := (rmMem dst).isSome
      run := fun vals fl _ cell =>
        rmSet dst (wide (~~~((rmVal dst 0 vals cell).setWidth w.bits))) fl }
  | .shift op w dst c =>
    some {
      srcs := rmRegs dst ++ (match c with | .cl => [.rcx] | .imm _ => [])
      addr := rmMem dst, bytes := wbytes w
      reads := (rmMem dst).isSome, writes := (rmMem dst).isSome
      run := fun vals fl _ cell =>
        let n : Nat := match c with
          | .imm k => k.toNat % w.bits
          | .cl => (vals.getD (rmRegs dst).length 0).toNat % w.bits
        let (r, f) := op.eval fl ((rmVal dst 0 vals cell).setWidth w.bits) n
        rmSet dst (wide r) f }
  | .mulDiv op w src =>
    some {
      srcs := [.rdx, .rax] ++ rmRegs src
      addr := rmMem src, bytes := wbytes w, reads := (rmMem src).isSome
      guard := fun vals _ _ cell =>
        match op.eval ((vals.getD 0 0).setWidth w.bits) ((vals.getD 1 0).setWidth w.bits)
            ((rmVal src 2 vals cell).setWidth w.bits) with
        | .next _ => true
        | _ => false
      run := fun vals fl _ cell =>
        match op.eval ((vals.getD 0 0).setWidth w.bits) ((vals.getD 1 0).setWidth w.bits)
            ((rmVal src 2 vals cell).setWidth w.bits) with
        | .next (lo, hi, f) => ⟨[(.rax, wide lo), (.rdx, wide hi)], f, 0⟩
        | _ => ⟨[], fl, 0⟩ }
  | .imul2 w dst src =>
    some {
      srcs := dst :: rmRegs src
      addr := rmMem src, bytes := wbytes w, reads := (rmMem src).isSome
      run := fun vals _ _ cell =>
        let (r, f) := imulTrunc ((vals.getD 0 0).setWidth w.bits)
          ((rmVal src 1 vals cell).setWidth w.bits)
        ⟨[(dst, wide r)], f, 0⟩ }
  | .imul3 w dst src imm =>
    some {
      srcs := rmRegs src
      addr := rmMem src, bytes := wbytes w, reads := (rmMem src).isSome
      run := fun vals _ _ cell =>
        let (r, f) := imulTrunc ((rmVal src 0 vals cell).setWidth w.bits) (imm.signExtend w.bits)
        ⟨[(dst, wide r)], f, 0⟩ }
  | .popcnt w dst src =>
    some {
      srcs := rmRegs src
      addr := rmMem src, bytes := wbytes w, reads := (rmMem src).isSome
      run := fun vals _ _ cell =>
        let a := (rmVal src 0 vals cell).setWidth w.bits
        ⟨[(dst, wide (popcount a))], ⟨some false, some (a == 0), some false, some false⟩, 0⟩ }
  | .bswap w r =>
    some {
      srcs := [r]
      run := fun vals fl _ _ => ⟨[(r, wide (bswap w ((vals.getD 0 0).setWidth w.bits)))], fl, 0⟩ }
  | .cdq =>
    some {
      srcs := [.rax]
      run := fun vals fl _ _ =>
        ⟨[(.rdx, wide (w := .w32) (signFill ((vals.getD 0 0).setWidth 32)))], fl, 0⟩ }
  | .cqo =>
    some {
      srcs := [.rax]
      run := fun vals fl _ _ =>
        ⟨[(.rdx, wide (w := .w64) (signFill ((vals.getD 0 0).setWidth 64)))], fl, 0⟩ }
  | .mov w ops =>
    let d := ops.dst
    some {
      srcs := srcRegs ops
      addr := opsMem ops
      bytes := wbytes w
      reads := match ops with | .r_m _ _ => true | _ => false
      writes := (rmMem d).isSome
      run := fun vals fl _ cell =>
        let v : BitVec w.bits := match ops with
          | .rm_r _ _ => (vals.getD 0 0).setWidth w.bits
          | .r_m _ _ => cell.setWidth w.bits
          | .rm_i _ imm => imm.signExtend w.bits
        rmSet d (wide v) fl }
  | .movAbs dst imm => some { srcs := [], run := fun _ fl _ _ => ⟨[(dst, imm)], fl, 0⟩ }
  | .store8 dst src =>
    some {
      srcs := [src], addr := some dst, bytes := 1, writes := true
      run := fun vals fl _ _ => ⟨[], fl, ((vals.getD 0 0).setWidth 8).setWidth 64⟩ }
  | .store16 dst src =>
    some {
      srcs := [src], addr := some dst, bytes := 2, writes := true
      run := fun vals fl _ _ => ⟨[], fl, ((vals.getD 0 0).setWidth 16).setWidth 64⟩ }
  | .movzx w dst sw src =>
    some {
      srcs := rmRegs src, addr := rmMem src, bytes := nbytes sw, reads := (rmMem src).isSome
      run := fun vals fl _ cell =>
        ⟨[(dst, wide (w := w) (((rmVal src 0 vals cell).setWidth sw.bits).setWidth w.bits))], fl, 0⟩ }
  | .movsx w dst sw src =>
    some {
      srcs := rmRegs src, addr := rmMem src, bytes := nbytes sw, reads := (rmMem src).isSome
      run := fun vals fl _ cell =>
        ⟨[(dst, wide (w := w) (((rmVal src 0 vals cell).setWidth sw.bits).signExtend w.bits))],
          fl, 0⟩ }
  | .movsxd dst src =>
    some {
      srcs := rmRegs src, addr := rmMem src, bytes := 4, reads := (rmMem src).isSome
      run := fun vals fl _ cell =>
        ⟨[(dst, ((rmVal src 0 vals cell).setWidth 32).signExtend 64)], fl, 0⟩ }
  | .lea w dst addr =>
    some {
      srcs := [], addr := some addr
      run := fun _ fl a _ => ⟨[(dst, wide (w := w) (a.setWidth w.bits))], fl, 0⟩ }
  | .cmov c w dst src =>
    some {
      srcs := dst :: rmRegs src
      addr := rmMem src, bytes := wbytes w, reads := (rmMem src).isSome
      guard := fun _ fl _ _ => (c.eval fl).isSome
      run := fun vals fl _ cell =>
        let v := (rmVal src 1 vals cell).setWidth w.bits
        ⟨[(dst, wide (w := w) (if (c.eval fl).getD false then v
          else (vals.getD 0 0).setWidth w.bits))], fl, 0⟩ }
  | .setcc c dst =>
    some {
      srcs := rmRegs dst, addr := rmMem dst, bytes := 1, writes := (rmMem dst).isSome
      guard := fun _ fl _ _ => (c.eval fl).isSome
      run := fun vals fl _ _ =>
        let b : BitVec 8 := if (c.eval fl).getD false then 1 else 0
        match dst with
        | .reg r => ⟨[(r, (vals.getD 0 0 &&& ~~~0xff) ||| b.setWidth 64)], fl, 0⟩
        | .mem _ => ⟨[], fl, b.setWidth 64⟩ }
  | .push r =>
    some {
      srcs := [r, .rsp], addr := some pushMem, bytes := 8, writes := true
      run := fun vals fl _ _ => ⟨[(.rsp, vals.getD 1 0 - 8)], fl, vals.getD 0 0⟩ }
  | .pop r =>
    some {
      srcs := [.rsp], addr := some topMem, bytes := 8, reads := true
      run := fun vals fl _ cell => ⟨[(.rsp, vals.getD 0 0 + 8), (r, cell)], fl, 0⟩ }
  | .nop => some { srcs := [], run := fun _ fl _ _ => ⟨[], fl, 0⟩ }
  | _ => none

end TypedAsm.U
