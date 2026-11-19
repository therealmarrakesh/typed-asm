import TypedAsm.Step

/-!
# What an instruction is described by

Every instruction does the same kind of thing. It uses the values of some
registers, perhaps the address a memory operand names, and perhaps bytes it
reads; it computes; and it leaves new values in some registers, new flags,
perhaps new bytes, and control at the next instruction or elsewhere. Here is
the form of such a description, as functions of what the instruction
computes with, and the small things said of operands that every
description is built with.
-/

namespace TypedAsm.U

/-- What an instruction leaves: registers given new values, the later
winning; the flags; and the value its bytes of memory are given, where it
writes them. -/
structure Effect where
  regs : List (Reg × BitVec 64)
  flags : Flags
  store : BitVec 64 := 0

/-- An instruction as what it uses and what it does with it. The functions
are given the values of `srcs` in order, the flags, the address of the next
instruction, the address `ea` names, and the bytes read as a number. -/
structure Desc where
  /-- The registers whose values the instruction computes with. -/
  srcs : List Reg
  /-- A memory operand whose address it uses as a number. -/
  ea : Option Mem := none
  /-- The bytes it reads: where, and how many. -/
  rd : Option (Mem × Nat) := none
  /-- The bytes it writes. -/
  wr : Option (Mem × Nat) := none
  /-- Whether it does not fault for a reason of its own. -/
  guard : List (BitVec 64) → Flags → BitVec 64 → BitVec 64 → BitVec 64 → Bool :=
    fun _ _ _ _ _ => true
  run : List (BitVec 64) → Flags → BitVec 64 → BitVec 64 → BitVec 64 → Effect
  /-- Where control goes, if not to the next instruction. -/
  goes : List (BitVec 64) → Flags → BitVec 64 → BitVec 64 → BitVec 64 → Option (BitVec 64) :=
    fun _ _ _ _ _ => none

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

/-- The registers a memory operand's address is made of. -/
def memRegs : Mem → List Reg
  | .sib base index _ => base.toList ++ (index.map (·.1.toReg)).toList
  | .rip _ => []

/-- The source of a two-operand form: its register, used after the
destination's; the bytes of memory; or its immediate. -/
def srcRegs : Operands → List Reg
  | .rm_r _ s => [s]
  | _ => []

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

end TypedAsm.U
