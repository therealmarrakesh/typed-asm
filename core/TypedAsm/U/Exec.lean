import TypedAsm.U.Desc
import TypedAsm.Memory

/-!
# What the machine does with a described instruction

One statement for all of them: where the bytes the instruction reads may be
read, those it writes may be written, and it does not fault for a reason of
its own, the machine goes on to the state the description gives.
-/

namespace TypedAsm.U

/-- So many bytes at an address, as a number. -/
def loadN (s : State) (n : Nat) (a : BitVec 64) : BitVec 64 :=
  match n with
  | 1 => (s.load8 a).setWidth 64
  | 2 => (s.load16 a).setWidth 64
  | 4 => (s.load32 a).setWidth 64
  | 8 => s.load64 a
  | _ => 0

/-- So many bytes at an address given the low bytes of a number. -/
def storeN (s : State) (n : Nat) (a v : BitVec 64) : State :=
  match n with
  | 1 => s.store8 a (v.setWidth 8)
  | 2 => s.store16 a (v.setWidth 16)
  | 4 => s.store32 a (v.setWidth 32)
  | 8 => s.store64 a v
  | _ => s

theorem wbytes_eq (w : Width) : w.bytes.toNat = wbytes w := by cases w <;> rfl

theorem read_ok {s : State} {w : Width} {a : BitVec 64} (h : s.canRead a (wbytes w) = true) :
    s.read w a = .next (s.load w a) := by
  unfold State.read
  rw [wbytes_eq, h]
  rfl

theorem write_ok {s : State} {w : Width} {a : BitVec 64} {v : BitVec w.bits}
    (h : s.canWrite a (wbytes w) = true) : s.write w a v = .next (s.store w a v) := by
  unfold State.write
  rw [wbytes_eq, h]
  rfl

theorem loadN_w (s : State) (w : Width) (a : BitVec 64) :
    (loadN s (wbytes w) a).setWidth w.bits = s.load w a := by
  cases w
  · show ((s.load32 a).setWidth 64).setWidth 32 = s.load32 a
    simp
  · show (s.load64 a).setWidth 64 = s.load64 a
    simp

theorem storeN_w (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    storeN s (wbytes w) a (wide v) = s.store w a v := by
  cases w
  · show s.store32 a ((v.setWidth 64).setWidth 32) = s.store32 a v
    simp
  · show s.store64 a (v.setWidth 64) = s.store64 a v
    simp

/-- What an operand holds, at a width. -/
def rmGet (s : State) (w : Width) : RM → BitVec w.bits
  | .reg r => s.readReg w r
  | .mem m => s.load w (s.ea m)

/-- The state with an operand given a value, at a width. -/
def rmPut (s : State) (w : Width) (x : RM) (v : BitVec w.bits) : State :=
  match x with
  | .reg r => s.writeReg w r v
  | .mem m => s.store w (s.ea m) v

theorem readRM_ok {s : State} {w : Width} {x : RM}
    (h : ∀ m, x = .mem m → s.canRead (s.ea m) (wbytes w) = true) :
    s.readRM w x = .next (rmGet s w x) := by
  cases x with
  | reg r => rfl
  | mem m =>
    show (s.read w (s.ea m)).through m = _
    rw [read_ok (h m rfl), Result.through_next]
    rfl

theorem writeRM_ok {s : State} {w : Width} {x : RM} {v : BitVec w.bits}
    (h : ∀ m, x = .mem m → s.canWrite (s.ea m) (wbytes w) = true) :
    s.writeRM w x v = .next (rmPut s w x v) := by
  cases x with
  | reg r => rfl
  | mem m =>
    show (s.write w (s.ea m) v).through m = _
    rw [write_ok (h m rfl), Result.through_next]
    rfl

namespace Desc

/-- The address a described instruction uses, in a state. -/
def addrOf (d : Desc) (s : State) : BitVec 64 :=
  match d.addr with
  | some m => s.ea m
  | none => 0

/-- The values it computes with. -/
def vals (d : Desc) (s : State) : List (BitVec 64) := d.srcs.map s.getReg

/-- The bytes at its address. -/
def cell (d : Desc) (s : State) : BitVec 64 := loadN s d.bytes (d.addrOf s)

/-- What it leaves, in a state. -/
def effect (d : Desc) (s : State) : Effect := d.run (d.vals s) s.flags (d.addrOf s) (d.cell s)

/-- Whether it does not fault for a reason of its own, in a state. -/
def guarded (d : Desc) (s : State) : Bool := d.guard (d.vals s) s.flags (d.addrOf s) (d.cell s)

/-- The state it leaves. -/
def after (d : Desc) (s : State) : State :=
  let e := d.effect s
  let s₁ := if d.writes then storeN s d.bytes (d.addrOf s) e.store else s
  { e.regs.foldl (fun t p => t.setReg p.1 p.2) s₁ with flags := e.flags }

end Desc

end TypedAsm.U
