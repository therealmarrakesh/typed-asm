import Core.Instr
import Std.Tactic.BVDecide

/-!
# Machine state

The registers, flags, instruction pointer and memory, with the basic operations
for reading and writing registers.
-/

namespace Core

/-- The number of bits in an operand of the given width. -/
def Width.bits : Width → Nat
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

structure State where
  regs : Reg → BitVec 64
  flags : Flags
  rip : BitVec 64
  mem : BitVec 64 → BitVec 8

namespace State

/-- A state with every register and memory byte zero and every flag clear. -/
def init : State where
  regs := fun _ => 0
  flags := ⟨some false, some false, some false, some false⟩
  rip := 0
  mem := fun _ => 0

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

end Core
