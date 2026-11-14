import TypedAsm.Instr
import Std.Tactic.BVDecide

/-!
# Machine state

The registers, flags, instruction pointer and memory, with the basic operations
for reading and writing registers.

Memory has a byte at every address, and separately a permission for every
address that says whether programs may read or write it.
-/

namespace TypedAsm

/-- The number of bits in an operand of the given width. It is reducible so
that `BitVec Width.w64.bits` and `BitVec 64` are interchangeable in proofs. -/
@[reducible] def Width.bits : Width → Nat
  | .w32 => 32
  | .w64 => 64

/-- The four modelled status flags. `none` means the value is unknown, which is
how flags the hardware leaves undefined are represented. -/
structure Flags where
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  deriving DecidableEq, Repr

/-- What a program may do with a byte of memory. -/
inductive Perm
  /-- Not accessible. -/
  | none
  /-- Readable only. -/
  | ro
  /-- Readable and writable. -/
  | rw
  deriving DecidableEq, Repr

def Perm.readable : Perm → Bool
  | .none => false
  | _ => true

def Perm.writable : Perm → Bool
  | .rw => true
  | _ => false

theorem Perm.readable_of_writable {p : Perm} (h : p.writable = true) : p.readable = true := by
  cases p <;> simp_all [Perm.readable, Perm.writable]

structure State where
  regs : Reg → BitVec 64
  flags : Flags
  rip : BitVec 64
  mem : BitVec 64 → BitVec 8
  perm : BitVec 64 → Perm

namespace State

/-- A state with every register and memory byte zero, every flag clear, and
no accessible memory. -/
def init : State where
  regs := fun _ => 0
  flags := ⟨some false, some false, some false, some false⟩
  rip := 0
  mem := fun _ => 0
  perm := fun _ => .none

/-- Set the permission of the `len` bytes starting at `base`. -/
def setPerm (s : State) (base len : BitVec 64) (p : Perm) : State :=
  { s with perm := fun x => if x - base < len then p else s.perm x }

/-- Read a full 64-bit register. -/
def getReg (s : State) (r : Reg) : BitVec 64 :=
  s.regs r

/-- Overwrite a full 64-bit register. -/
def setReg (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

/-- Read a register at the given width. The width of the result depends on `w`. -/
def readReg (s : State) (w : Width) (r : Reg) : BitVec w.bits :=
  (s.getReg r).setWidth w.bits

/-- Write a register at the given width. A 32-bit write clears the upper half. -/
def writeReg (s : State) (w : Width) (r : Reg) (v : BitVec w.bits) : State :=
  s.setReg r (v.setWidth 64)

/-- Reading a register just written gives the written value. -/
theorem getReg_setReg_same (s : State) (r : Reg) (v : BitVec 64) :
    (s.setReg r v).getReg r = v := by
  simp [getReg, setReg]

/-- Writing one register leaves every other register unchanged. -/
theorem getReg_setReg_other (s : State) (r r' : Reg) (v : BitVec 64) (h : r' ≠ r) :
    (s.setReg r v).getReg r' = s.getReg r' := by
  simp [getReg, setReg, h]

/-- After a 32-bit write, the upper 32 bits of the register are zero,
whatever the register held before and whatever value was written. -/
theorem writeReg_w32_upper_zero (s : State) (r : Reg) (v : BitVec 32) :
    ((s.writeReg .w32 r v).getReg r).extractLsb 63 32 = 0 := by
  simp only [writeReg, getReg_setReg_same]
  show (BitVec.setWidth 64 v).extractLsb 63 32 = 0
  bv_decide

end State

end TypedAsm
