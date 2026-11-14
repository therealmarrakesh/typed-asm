import TypedAsm.State
import TypedAsm.Result

/-!
# Memory access

Effective addresses, and little-endian loads and stores over the byte-level
memory in `State`.

There are two layers. `load` and `store` are the raw operations: they ignore
permissions and always succeed. `read` and `write` are what instructions use:
they check permissions first and fault if any byte of the access is not allowed.
-/

namespace TypedAsm

/-- The left shift that multiplies by the scale factor. -/
def Scale.shift : Scale → Nat
  | .s1 => 0
  | .s2 => 1
  | .s4 => 2
  | .s8 => 3

/-- The number of bytes an operand of the given width occupies in memory. -/
def Width.bytes : Width → BitVec 64
  | .w32 => 4
  | .w64 => 8

namespace State

/-- The address a memory operand denotes. Arithmetic wraps at 64 bits.

For the `rip`-relative form, `s.rip` must already hold the address of the *next*
instruction, as it does on hardware while an instruction executes. -/
def ea (s : State) : Mem → BitVec 64
  | .sib base index disp =>
    let b := match base with
      | some r => s.getReg r
      | none => 0
    let i := match index with
      | some (r, scale) => s.getReg r.toReg <<< scale.shift
      | none => 0
    b + i + disp.signExtend 64
  | .rip disp => s.rip + disp.signExtend 64

/-! ## Loads -/

def load8 (s : State) (a : BitVec 64) : BitVec 8 :=
  s.mem a

def load16 (s : State) (a : BitVec 64) : BitVec 16 :=
  s.load8 (a + 1) ++ s.load8 a

def load32 (s : State) (a : BitVec 64) : BitVec 32 :=
  s.load16 (a + 2) ++ s.load16 a

def load64 (s : State) (a : BitVec 64) : BitVec 64 :=
  s.load32 (a + 4) ++ s.load32 a

/-- Load a value of the given width. The lowest address holds the least significant byte. -/
def load (s : State) (w : Width) (a : BitVec 64) : BitVec w.bits :=
  match w with
  | .w32 => s.load32 a
  | .w64 => s.load64 a

/-! ## Stores -/

def store8 (s : State) (a : BitVec 64) (v : BitVec 8) : State :=
  { s with mem := fun x => if x = a then v else s.mem x }

def store16 (s : State) (a : BitVec 64) (v : BitVec 16) : State :=
  (s.store8 a (v.extractLsb' 0 8)).store8 (a + 1) (v.extractLsb' 8 8)

def store32 (s : State) (a : BitVec 64) (v : BitVec 32) : State :=
  (s.store16 a (v.extractLsb' 0 16)).store16 (a + 2) (v.extractLsb' 16 16)

def store64 (s : State) (a : BitVec 64) (v : BitVec 64) : State :=
  (s.store32 a (v.extractLsb' 0 32)).store32 (a + 4) (v.extractLsb' 32 32)

/-- Store a value of the given width. The least significant byte goes to the lowest address. -/
def store (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) : State :=
  match w with
  | .w32 => s.store32 a v
  | .w64 => s.store64 a v

/-! ## Laws -/

/-- Loading from an address just stored to returns the stored value. -/
theorem load8_store8_same (s : State) (a : BitVec 64) (v : BitVec 8) :
    (s.store8 a v).load8 a = v := by
  simp [load8, store8]

/-- Loading from an address just stored to returns the stored value. -/
theorem load_store_same (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.store w a v).load w a = v := by
  cases w <;>
    simp [load, store, load64, load32, load16, load8, store64, store32, store16, store8,
      BitVec.add_assoc] <;>
    bv_decide

/-- A store changes only the bytes in its own range. -/
theorem mem_store_of_disjoint (s : State) (w : Width) (a x : BitVec 64) (v : BitVec w.bits)
    (h : w.bytes ≤ x - a) : (s.store w a v).mem x = s.mem x := by
  cases w <;>
    simp only [store, store64, store32, store16, store8, Width.bytes] at * <;>
    bv_decide

private theorem load32_congr {s t : State} {b : BitVec 64}
    (h₀ : t.mem b = s.mem b) (h₁ : t.mem (b + 1) = s.mem (b + 1))
    (h₂ : t.mem (b + 2) = s.mem (b + 2)) (h₃ : t.mem (b + 2 + 1) = s.mem (b + 2 + 1)) :
    t.load32 b = s.load32 b := by
  simp only [load32, load16, load8, h₀, h₁, h₂, h₃]

private theorem load64_congr {s t : State} {b : BitVec 64}
    (h₀ : t.mem b = s.mem b) (h₁ : t.mem (b + 1) = s.mem (b + 1))
    (h₂ : t.mem (b + 2) = s.mem (b + 2)) (h₃ : t.mem (b + 2 + 1) = s.mem (b + 2 + 1))
    (h₄ : t.mem (b + 4) = s.mem (b + 4)) (h₅ : t.mem (b + 4 + 1) = s.mem (b + 4 + 1))
    (h₆ : t.mem (b + 4 + 2) = s.mem (b + 4 + 2))
    (h₇ : t.mem (b + 4 + 2 + 1) = s.mem (b + 4 + 2 + 1)) :
    t.load64 b = s.load64 b := by
  simp only [load64, load32, load16, load8, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-- A store leaves a load from a non-overlapping range unchanged. The two
hypotheses say that neither range starts inside the other, which also covers
ranges that wrap around the end of the address space. -/
theorem load_store_disjoint (s : State) (w w' : Width) (a b : BitVec 64) (v : BitVec w.bits)
    (h₁ : w.bytes ≤ b - a) (h₂ : w'.bytes ≤ a - b) :
    (s.store w a v).load w' b = s.load w' b := by
  cases w'
  · refine load32_congr ?_ ?_ ?_ ?_ <;> apply mem_store_of_disjoint <;>
      cases w <;> simp only [Width.bytes] at * <;> bv_decide
  · refine load64_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> apply mem_store_of_disjoint <;>
      cases w <;> simp only [Width.bytes] at * <;> bv_decide

/-- A store does not change any permission. -/
theorem perm_store (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.store w a v).perm = s.perm := by
  cases w <;> simp only [store, store64, store32, store16, store8]

/-- A store does not change any register. -/
theorem getReg_store (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) (r : Reg) :
    (s.store w a v).getReg r = s.getReg r := by
  cases w <;> simp only [store, store64, store32, store16, store8, getReg]

/-- A register write does not change memory. -/
theorem load_setReg (s : State) (r : Reg) (v : BitVec 64) (w : Width) (a : BitVec 64) :
    (s.setReg r v).load w a = s.load w a := by
  cases w
  · exact load32_congr rfl rfl rfl rfl
  · exact load64_congr rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## Checked access -/

/-- Whether all `n` bytes starting at `a` are readable. -/
def canRead (s : State) (a : BitVec 64) (n : Nat) : Bool :=
  (List.range n).all fun i => (s.perm (a + BitVec.ofNat 64 i)).readable

/-- Whether all `n` bytes starting at `a` are writable. -/
def canWrite (s : State) (a : BitVec 64) (n : Nat) : Bool :=
  (List.range n).all fun i => (s.perm (a + BitVec.ofNat 64 i)).writable

theorem canRead_of_canWrite {s : State} {a : BitVec 64} {n : Nat} (h : s.canWrite a n = true) :
    s.canRead a n = true := by
  simp only [canRead, canWrite, List.all_eq_true] at *
  exact fun i hi => Perm.readable_of_writable (h i hi)

def read8 (s : State) (a : BitVec 64) : Result (BitVec 8) :=
  if s.canRead a 1 then .next (s.load8 a) else .fault .pageFault

def read16 (s : State) (a : BitVec 64) : Result (BitVec 16) :=
  if s.canRead a 2 then .next (s.load16 a) else .fault .pageFault

def read64 (s : State) (a : BitVec 64) : Result (BitVec 64) :=
  if s.canRead a 8 then .next (s.load64 a) else .fault .pageFault

/-- Load a value of the given width, faulting unless every byte is readable. -/
def read (s : State) (w : Width) (a : BitVec 64) : Result (BitVec w.bits) :=
  if s.canRead a w.bytes.toNat then .next (s.load w a) else .fault .pageFault

def write8 (s : State) (a : BitVec 64) (v : BitVec 8) : Result State :=
  if s.canWrite a 1 then .next (s.store8 a v) else .fault .pageFault

def write64 (s : State) (a : BitVec 64) (v : BitVec 64) : Result State :=
  if s.canWrite a 8 then .next (s.store64 a v) else .fault .pageFault

/-- Store a value of the given width, faulting unless every byte is writable.
A faulting store changes nothing. -/
def write (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) : Result State :=
  if s.canWrite a w.bytes.toNat then .next (s.store w a v) else .fault .pageFault

/-- A successful write is the raw store. -/
theorem write_eq_next {s s' : State} {w : Width} {a : BitVec 64} {v : BitVec w.bits}
    (h : s.write w a v = .next s') : s' = s.store w a v := by
  simp only [write] at h
  split at h <;> simp_all

/-- A value just written can be read back. -/
theorem read_write_same {s s' : State} {w : Width} {a : BitVec 64} {v : BitVec w.bits}
    (h : s.write w a v = .next s') : s'.read w a = .next v := by
  simp only [write] at h
  split at h
  next hw =>
    cases h
    have hr : (s.store w a v).canRead a w.bytes.toNat = true := by
      simp only [canRead, perm_store]
      exact canRead_of_canWrite hw
    simp only [read, hr, ite_true, load_store_same]
  next => cases h

end State

end TypedAsm
