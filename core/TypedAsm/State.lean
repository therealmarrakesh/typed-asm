import TypedAsm.Instr
import Std.Tactic.BVDecide
import Std.Data.TreeMap

/-!
# Machine state

The registers, flags, instruction pointer and memory, with the basic operations
for reading and writing registers.

Memory has a byte at every address, and separately a permission for every
address that says whether programs may read or write it.

The registers and memory are stored so that the model runs at a steady
speed however long the run: the registers as sixteen fields, memory as an
ordered table of the bytes written so far. Both keep their cost when an
older state is still in use, which a run that reports where it stopped needs. Everything else sees them only as
the functions `State.regs` and `State.mem`, and the two facts about writing
them, `State.regs_setReg` and `State.mem_store8` (in `Memory`).
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
  /-- Readable and executable: this is where code lives. There is no
  permission that is both writable and executable, so code cannot be changed. -/
  | rx
  deriving DecidableEq, Repr

def Perm.readable : Perm → Bool
  | .none => false
  | _ => true

def Perm.writable : Perm → Bool
  | .rw => true
  | _ => false

def Perm.executable : Perm → Bool
  | .rx => true
  | _ => false

theorem Perm.readable_of_writable {p : Perm} (h : p.writable = true) : p.readable = true := by
  cases p <;> simp_all [Perm.readable, Perm.writable]

/-- What one `read` from the outside world delivers: some bytes, or an error
number. -/
inductive ReadEvent
  | bytes (data : List (BitVec 8))
  | error (errno : BitVec 64)

/-- The world outside the machine, as far as a program can observe it: what
is still to be read, one event per `read`, and everything written so far.
Only system calls touch it. Nothing is assumed about the input, so a result
proved for every state holds whatever the program is given to read. -/
structure World where
  input : List ReadEvent := []
  /-- The bytes of each `write` so far, most recent first. -/
  writes : List (List (BitVec 8)) := []
  /-- How many bytes each coming `write` will accept at most, one entry per
  call. When none is left a `write` accepts everything it is given. -/
  writeCaps : List Nat := []

/-- Everything written so far, in the order it was written. -/
def World.output (w : World) : List (BitVec 8) :=
  w.writes.reverse.flatten

/-- The values of the sixteen registers. -/
structure RegFile where
  (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64)

namespace RegFile

def get (f : RegFile) : Reg → BitVec 64
  | .rax => f.rax
  | .rcx => f.rcx
  | .rdx => f.rdx
  | .rbx => f.rbx
  | .rsp => f.rsp
  | .rbp => f.rbp
  | .rsi => f.rsi
  | .rdi => f.rdi
  | .r8 => f.r8
  | .r9 => f.r9
  | .r10 => f.r10
  | .r11 => f.r11
  | .r12 => f.r12
  | .r13 => f.r13
  | .r14 => f.r14
  | .r15 => f.r15

def set (f : RegFile) (r : Reg) (v : BitVec 64) : RegFile :=
  match r with
  | .rax => { f with rax := v }
  | .rcx => { f with rcx := v }
  | .rdx => { f with rdx := v }
  | .rbx => { f with rbx := v }
  | .rsp => { f with rsp := v }
  | .rbp => { f with rbp := v }
  | .rsi => { f with rsi := v }
  | .rdi => { f with rdi := v }
  | .r8 => { f with r8 := v }
  | .r9 => { f with r9 := v }
  | .r10 => { f with r10 := v }
  | .r11 => { f with r11 := v }
  | .r12 => { f with r12 := v }
  | .r13 => { f with r13 := v }
  | .r14 => { f with r14 := v }
  | .r15 => { f with r15 := v }

theorem get_set (f : RegFile) (r r' : Reg) (v : BitVec 64) :
    (f.set r v).get r' = if r' = r then v else f.get r' := by
  cases r <;> cases r' <;> rfl

end RegFile

/-- The contents of memory: the bytes written so far, over what was there to
begin with. -/
structure Memory where
  initial : BitVec 64 → BitVec 8
  written : Std.TreeMap Nat (BitVec 8) := {}

namespace Memory

def get (m : Memory) (x : BitVec 64) : BitVec 8 :=
  m.written.getD x.toNat (m.initial x)

def set (m : Memory) (a : BitVec 64) (v : BitVec 8) : Memory :=
  { m with written := m.written.insert a.toNat v }

theorem get_set (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.set a v).get x = if x = a then v else m.get x := by
  simp only [get, set, Std.TreeMap.getD_insert]
  by_cases h : x = a
  · simp [h]
  · have h' : ¬ a.toNat = x.toNat := fun e => h (BitVec.eq_of_toNat_eq e.symm)
    simp [h, h']

/-- Write a list of bytes at consecutive addresses. -/
def setBytes (m : Memory) (a : BitVec 64) : List (BitVec 8) → Memory
  | [] => m
  | b :: bs => (m.set a b).setBytes (a + 1) bs

theorem setBytes_nil (m : Memory) (a : BitVec 64) : m.setBytes a [] = m :=
  rfl

theorem get_setBytes (m : Memory) (a x : BitVec 64) (l : List (BitVec 8)) (hlen : l.length ≤ 2 ^ 64) :
    (m.setBytes a l).get x = (l[(x - a).toNat]?).getD (m.get x) := by
  induction l generalizing m a with
  | nil => simp [setBytes]
  | cons b bs ih =>
    simp only [List.length_cons] at hlen
    simp only [setBytes]
    rw [ih _ _ (by omega), get_set]
    by_cases hxa : x = a
    · subst hxa
      have h1 : (x - (x + 1)).toNat = 2 ^ 64 - 1 := by bv_omega
      have h2 : bs[(x - (x + 1)).toNat]? = none := by
        rw [h1]; exact List.getElem?_eq_none (by omega)
      rw [h2]
      simp
    · have h1 : (x - a).toNat = (x - (a + 1)).toNat + 1 := by bv_omega
      rw [h1]
      simp [hxa]

end Memory

-- How memory is stored is nobody's business but the three facts above:
-- sealing it keeps proofs from wandering into the table.
attribute [irreducible] Memory.get Memory.set Memory.setBytes


structure State where
  regFile : RegFile
  flags : Flags
  rip : BitVec 64
  memory : Memory
  perm : BitVec 64 → Perm
  world : World := {}

/-- The value of each register. -/
def State.regs (s : State) : Reg → BitVec 64 :=
  s.regFile.get

/-- The byte at each address. -/
def State.mem (s : State) : BitVec 64 → BitVec 8 :=
  s.memory.get

namespace State

/-- A state with every register and memory byte zero, every flag clear, and
no accessible memory. -/
def init : State where
  regFile := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  flags := ⟨some false, some false, some false, some false⟩
  rip := 0
  memory := { initial := fun _ => 0 }
  perm := fun _ => .none

/-- Set the permission of the `len` bytes starting at `base`. -/
def setPerm (s : State) (base len : BitVec 64) (p : Perm) : State :=
  { s with perm := fun x => if x - base < len then p else s.perm x }

/-- Read a full 64-bit register. -/
def getReg (s : State) (r : Reg) : BitVec 64 :=
  s.regs r

/-- Overwrite a full 64-bit register. -/
def setReg (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with regFile := s.regFile.set r v }

/-- Writing a register changes that register and no other. -/
theorem regs_setReg (s : State) (r r' : Reg) (v : BitVec 64) :
    (s.setReg r v).regs r' = if r' = r then v else s.regs r' :=
  RegFile.get_set _ _ _ _

/-- Read a register at the given width. The width of the result depends on `w`. -/
def readReg (s : State) (w : Width) (r : Reg) : BitVec w.bits :=
  (s.getReg r).setWidth w.bits

/-- Write a register at the given width. A 32-bit write clears the upper half. -/
def writeReg (s : State) (w : Width) (r : Reg) (v : BitVec w.bits) : State :=
  s.setReg r (v.setWidth 64)

/-- Reading a register just written gives the written value. -/
theorem getReg_setReg_same (s : State) (r : Reg) (v : BitVec 64) :
    (s.setReg r v).getReg r = v := by
  simp [getReg, regs_setReg]

/-- Writing one register leaves every other register unchanged. -/
theorem getReg_setReg_other (s : State) (r r' : Reg) (v : BitVec 64) (h : r' ≠ r) :
    (s.setReg r v).getReg r' = s.getReg r' := by
  simp [getReg, regs_setReg, h]

/-- After a 32-bit write, the upper 32 bits of the register are zero,
whatever the register held before and whatever value was written. -/
theorem writeReg_w32_upper_zero (s : State) (r : Reg) (v : BitVec 32) :
    ((s.writeReg .w32 r v).getReg r).extractLsb 63 32 = 0 := by
  simp only [writeReg, getReg_setReg_same]
  show (BitVec.setWidth 64 v).extractLsb 63 32 = 0
  bv_decide

end State

end TypedAsm
