import TypedAsm.U.Desc

/-!
# What instructions compute, as operators

Every instruction computes its results from a few things: the values of
the registers it uses, the bytes it reads, an address, the flags before
it. What it computes is built from a small number of operators. Here they
are, as data, each with what it comes to, said with the machine's own
functions.

Because an instruction is then data built of these, whatever is to be
known of an instruction, what its result is, whether its flags are
defined, what a condition on them says, is known of the operators: once
for each, and of no instruction in particular.
-/

namespace TypedAsm.U

open TypedAsm

/-- A thing an instruction computes with: the value of a register it uses,
by position; the bytes it reads; the address of its memory operand; the
address of the instruction after it. -/
inductive Slot
  | arg (j : Nat)
  | cell
  | ea
  | next
  deriving DecidableEq

/-- An operator on one value. -/
inductive Un
  /-- The negative, at a width. -/
  | neg (w : Width)
  /-- Every bit turned, at a width. -/
  | not (w : Width)
  /-- How many bits are set, at a width. -/
  | popcnt (w : Width)
  /-- The bytes in the other order, at a width. -/
  | bswap (w : Width)
  /-- All ones or all noughts, as the top bit at a width is. -/
  | signFill (w : Width)
  /-- The low bits of a width, the rest cleared. -/
  | trunc (w : Width)
  /-- The low bits of a narrow width, widened with noughts. -/
  | zx (w : Width) (sw : NarrowW)
  /-- The low bits of a narrow width, widened with the sign. -/
  | sx (w : Width) (sw : NarrowW)
  /-- The low thirty-two bits, widened with the sign. -/
  | sxd
  /-- The low byte. -/
  | low8
  /-- The low two bytes. -/
  | low16
  /-- Moved left so many bits. -/
  | shl (k : Nat)
  deriving DecidableEq

def Un.eval : Un → BitVec 64 → BitVec 64
  | .neg w, a => wide (subBorrow 0 (a.setWidth w.bits) false).1
  | .not w, a => wide (~~~(a.setWidth w.bits))
  | .popcnt w, a => wide (TypedAsm.popcount (a.setWidth w.bits))
  | .bswap w, a => wide (TypedAsm.bswap w (a.setWidth w.bits))
  | .signFill w, a => wide (TypedAsm.signFill (a.setWidth w.bits))
  | .trunc w, a => wide (a.setWidth w.bits)
  | .zx w sw, a => wide (w := w) ((a.setWidth sw.bits).setWidth w.bits)
  | .sx w sw, a => wide (w := w) ((a.setWidth sw.bits).signExtend w.bits)
  | .sxd, a => (a.setWidth 32).signExtend 64
  | .low8, a => (a.setWidth 8).setWidth 64
  | .low16, a => (a.setWidth 16).setWidth 64
  | .shl k, a => a <<< k

/-- An operator on two values that does not turn on the flags. -/
inductive Bin
  /-- The sum. -/
  | add
  /-- The first shifted or rotated by the second, at a width. -/
  | shift (op : ShiftOp) (w : Width)
  /-- The low half of the signed product, at a width. -/
  | imul (w : Width)
  deriving DecidableEq

def Bin.eval : Bin → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .shift op w, a, n => wide (op.eval Flags.unknown (a.setWidth w.bits) (n.toNat % w.bits)).1
  | .imul w, a, b => wide (imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).1

/-- An operator on three values: the two halves of a product or quotient,
of the high half, the low half and the other operand. Where the machine
would fault, the halves are as they were. -/
inductive Tri
  | mulLo (op : MulDivOp) (w : Width)
  | mulHi (op : MulDivOp) (w : Width)
  deriving DecidableEq

def Tri.eval : Tri → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64
  | .mulLo op w, hi, lo, src =>
    match op.eval (hi.setWidth w.bits) (lo.setWidth w.bits) (src.setWidth w.bits) with
    | .next (l, _, _) => wide l
    | _ => lo
  | .mulHi op w, hi, lo, src =>
    match op.eval (hi.setWidth w.bits) (lo.setWidth w.bits) (src.setWidth w.bits) with
    | .next (_, h, _) => wide h
    | _ => hi

/-- An operator on two values that turns on the flags before it. -/
inductive FOp
  /-- An arithmetic or logical operation, at a width: with carry or borrow,
  it takes the carry flag in. -/
  | alu (op : AluOp) (w : Width)
  /-- The second, where the condition holds; otherwise the first; at a
  width. -/
  | cmov (c : Cond) (w : Width)
  /-- The first with its low byte one or nought, as the condition is. -/
  | setcc (c : Cond)
  /-- One or nought, as the condition is. -/
  | condByte (c : Cond)
  deriving DecidableEq

/-- The byte a condition comes to. -/
def condBit (c : Cond) (fl : Flags) : BitVec 8 := if (c.eval fl).getD false then 1 else 0

def FOp.eval : FOp → Flags → BitVec 64 → BitVec 64 → BitVec 64
  | .alu op w, fl, a, b =>
    wide ((op.eval fl.cf (a.setWidth w.bits) (b.setWidth w.bits)).getD (a.setWidth w.bits, fl)).1
  | .cmov c w, fl, a, b =>
    wide (w := w) (if (c.eval fl).getD false then b.setWidth w.bits else a.setWidth w.bits)
  | .setcc c, fl, a, _ => (a &&& ~~~0xff) ||| (condBit c fl).setWidth 64
  | .condByte c, fl, _, _ => (condBit c fl).setWidth 64

/-- How flags arise: of what operation, at what width. -/
inductive FSrc
  /-- As an arithmetic or logical operation leaves them. -/
  | alu (op : AluOp) (w : Width)
  /-- As of the conjunction of two values, nothing written. -/
  | test (w : Width)
  /-- As of nought less a value. -/
  | neg (w : Width)
  /-- As a shift or rotation leaves them: as they were, if by nought. -/
  | shift (op : ShiftOp) (w : Width)
  /-- As a product or quotient through the two halves leaves them. -/
  | mul (op : MulDivOp) (w : Width)
  /-- As the signed product of two values leaves them. -/
  | imul (w : Width)
  /-- The zero flag says whether a value is nought; the rest are clear. -/
  | popcnt (w : Width)
  deriving DecidableEq

def FSrc.eval : FSrc → Flags → BitVec 64 → BitVec 64 → BitVec 64 → Flags
  | .alu op w, fl, a, b, _ =>
    ((op.eval fl.cf (a.setWidth w.bits) (b.setWidth w.bits)).getD (a.setWidth w.bits, fl)).2
  | .test w, _, a, b, _ => Flags.ofResult (a.setWidth w.bits &&& b.setWidth w.bits) false false
  | .neg w, _, a, _, _ => (subBorrow 0 (a.setWidth w.bits) false).2
  | .shift op w, fl, a, n, _ => (op.eval fl (a.setWidth w.bits) (n.toNat % w.bits)).2
  | .mul op w, fl, hi, lo, src =>
    match op.eval (hi.setWidth w.bits) (lo.setWidth w.bits) (src.setWidth w.bits) with
    | .next (_, _, f) => f
    | _ => fl
  | .imul w, _, a, b, _ => (imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).2
  | .popcnt w, _, a, _, _ =>
    ⟨some false, some (a.setWidth w.bits == 0), some false, some false⟩

/-- What must hold for an instruction not to fault of itself. -/
inductive GuardE
  /-- Nothing. -/
  | none
  /-- A condition on the flags is decided. -/
  | cond (c : Cond)
  /-- An arithmetic operation, on two values, can be done: with carry or
  borrow, the carry flag is defined. -/
  | alu (op : AluOp) (w : Width)
  /-- A product or quotient through the two halves can be done: a quotient
  fits, and is not by nought. -/
  | mul (op : MulDivOp) (w : Width)
  deriving DecidableEq

def GuardE.eval : GuardE → Flags → BitVec 64 → BitVec 64 → BitVec 64 → Bool
  | .none, _, _, _, _ => true
  | .cond c, fl, _, _, _ => (c.eval fl).isSome
  | .alu op w, fl, a, b, _ => (op.eval fl.cf (a.setWidth w.bits) (b.setWidth w.bits)).isSome
  | .mul op w, _, hi, lo, src =>
    match op.eval (hi.setWidth w.bits) (lo.setWidth w.bits) (src.setWidth w.bits) with
    | .next _ => true
    | _ => false

end TypedAsm.U
