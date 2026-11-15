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
  { s with memory := s.memory.set a v }

/-- Storing a byte does not change the registers. -/
theorem regs_store8 (s : State) (a : BitVec 64) (v : BitVec 8) : (s.store8 a v).regs = s.regs :=
  rfl

/-- Storing a byte changes that byte and no other. -/
theorem mem_store8 (s : State) (a x : BitVec 64) (v : BitVec 8) :
    (s.store8 a v).mem x = if x = a then v else s.mem x :=
  Memory.get_set _ _ _ _

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
  simp [load8, mem_store8]

/-- Loading from an address just stored to returns the stored value. -/
theorem load_store_same (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.store w a v).load w a = v := by
  cases w <;>
    simp [load, store, load64, load32, load16, load8, store64, store32, store16, mem_store8,
      BitVec.add_assoc] <;>
    bv_decide

/-- A store changes only the bytes in its own range. -/
theorem mem_store_of_disjoint (s : State) (w : Width) (a x : BitVec 64) (v : BitVec w.bits)
    (h : w.bytes ≤ x - a) : (s.store w a v).mem x = s.mem x := by
  cases w <;>
    simp only [store, store64, store32, store16, mem_store8, Width.bytes] at * <;>
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

/-- Two states with the same eight bytes at an address load the same 64-bit
value from it. -/
theorem load64_congr_bytes {s t : State} {b : BitVec 64}
    (h : ∀ j : BitVec 64, j < 8 → t.mem (b + j) = s.mem (b + j)) : t.load64 b = s.load64 b := by
  refine load64_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using h 0 (by decide)
  · exact h 1 (by decide)
  · exact h 2 (by decide)
  · have := h 3 (by decide); rwa [show b + 3 = b + 2 + 1 by bv_omega] at this
  · exact h 4 (by decide)
  · have := h 5 (by decide); rwa [show b + 5 = b + 4 + 1 by bv_omega] at this
  · have := h 6 (by decide); rwa [show b + 6 = b + 4 + 2 by bv_omega] at this
  · have := h 7 (by decide); rwa [show b + 7 = b + 4 + 2 + 1 by bv_omega] at this

/-- A byte store leaves a 64-bit load unchanged if the byte is outside the loaded range. -/
theorem load64_store8_disjoint (s : State) {a b : BitVec 64} (v : BitVec 8) (h : 8 ≤ a - b) :
    (s.store8 a v).load64 b = s.load64 b := by
  apply load64_congr <;>
    (simp only [mem_store8]
     split
     · next hx => exact absurd hx (by bv_decide)
     · rfl)

/-- A store does not change `rip`. -/
theorem rip_store (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.store w a v).rip = s.rip := by
  cases w <;> simp only [store, store64, store32, store16, store8]

/-- A store does not change the flags. -/
theorem flags_store (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.store w a v).flags = s.flags := by
  cases w <;> simp only [store, store64, store32, store16, store8]

/-- A store does not change the registers. -/
theorem regs_store (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.store w a v).regs = s.regs := by
  cases w <;> simp only [store, store64, store32, store16, regs_store8]

/-- A store does not change any permission. -/
theorem perm_store (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.store w a v).perm = s.perm := by
  cases w <;> simp only [store, store64, store32, store16, store8, State.perm]

/-- A store does not change any register. -/
theorem getReg_store (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) (r : Reg) :
    (s.store w a v).getReg r = s.getReg r := by
  cases w <;> simp only [store, store64, store32, store16, getReg, regs_store8]

/-- A register write does not change memory. -/
theorem load_setReg (s : State) (r : Reg) (v : BitVec 64) (w : Width) (a : BitVec 64) :
    (s.setReg r v).load w a = s.load w a := by
  cases w
  · exact load32_congr rfl rfl rfl rfl
  · exact load64_congr rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## Checked access -/

/-- Store a list of bytes at consecutive addresses. -/
def storeBytes (s : State) (a : BitVec 64) (l : List (BitVec 8)) : State :=
  { s with memory := s.memory.setBytes a l }

/-- Storing no bytes changes nothing. -/
theorem storeBytes_nil (s : State) (a : BitVec 64) : s.storeBytes a [] = s := by
  simp only [storeBytes, Memory.setBytes_nil]

/-- Storing bytes changes the addresses they cover and no other. -/
theorem mem_storeBytes (s : State) (a x : BitVec 64) (l : List (BitVec 8))
    (hlen : l.length ≤ 2 ^ 64) :
    (s.storeBytes a l).mem x = (l[(x - a).toNat]?).getD (s.mem x) :=
  Memory.get_setBytes _ _ _ _ hlen

/-- The `n` bytes starting at `a`. -/
def loadBytes (s : State) (a : BitVec 64) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => s.mem (a + BitVec.ofNat 64 i)

/-- Storing bytes leaves a 64-bit value that does not overlap them unchanged. -/
theorem load64_storeBytes_disjoint (s : State) {a y : BitVec 64} (l : List (BitVec 8))
    (hlen : l.length < 2 ^ 64) (h1 : BitVec.ofNat 64 l.length ≤ y - a)
    (h2 : BitVec.ofNat 64 8 ≤ a - y) : (s.storeBytes a l).load64 y = s.load64 y := by
  apply load64_congr <;>
    (rw [mem_storeBytes s a _ l (Nat.le_of_lt hlen), List.getElem?_eq_none (by bv_omega)]
     rfl)

/-- Whether all `n` bytes starting at `a` are readable. -/
def canRead (s : State) (a : BitVec 64) (n : Nat) : Bool :=
  (List.range n).all fun i => (s.perm (a + BitVec.ofNat 64 i)).readable

/-- Whether all `n` bytes starting at `a` are writable. -/
def canWrite (s : State) (a : BitVec 64) (n : Nat) : Bool :=
  (List.range n).all fun i => (s.perm (a + BitVec.ofNat 64 i)).writable

/-- Whether `p` holds of every number below `n`. -/
def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => if p n then allBelow p n else false

theorem allBelow_iff {p : Nat → Bool} {n : Nat} :
    allBelow p n = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow]
    constructor
    · intro h i hi
      split at h
      · next hp =>
        by_cases hin : i = n
        · rw [hin]; exact hp
        · exact ih.mp h i (by omega)
      · cases h
    · intro h
      simp only [h n (by omega), ↓reduceIte]
      exact ih.mpr (fun i hi => h i (by omega))

/-- Whether none of the `n` bytes starting at `a` is accessible. Where the
whole range lies beyond anything that was accessible to begin with, it is
enough that no page of it has been made accessible since; otherwise every
byte is asked. `unmapped_iff` says the two ways agree. -/
def unmapped (s : State) (a : BitVec 64) (n : Nat) : Bool :=
  (decide (s.perms.clearFrom ≤ a.toNat) &&
    allBelow (fun j => decide ((s.perms.pages[a.toNat / 4096 + j]?).getD .none = .none))
      ((n + 4095) / 4096)) ||
  allBelow (fun i => decide (s.perm (a + BitVec.ofNat 64 i) = .none)) n

theorem unmapped_iff {s : State} {a : BitVec 64} {n : Nat} (hal : a.toNat % 4096 = 0)
    (hfit : a.toNat + n ≤ 2 ^ 64) :
    s.unmapped a n = true ↔ ∀ i, i < n → s.perm (a + BitVec.ofNat 64 i) = .none := by
  simp only [unmapped, Bool.or_eq_true, Bool.and_eq_true, allBelow_iff, decide_eq_true_eq]
  have hnat : ∀ i, i < n → (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    intro i hi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  constructor
  · rintro (⟨hclear, hp⟩ | hall) i hin
    · show s.perms.get _ = _
      have hpg : (a + BitVec.ofNat 64 i).toNat / 4096 = a.toNat / 4096 + i / 4096 := by
        rw [hnat i hin]; omega
      have hq := hp (i / 4096) (by omega)
      simp only [Perms.get, hpg]
      cases hc : s.perms.pages[a.toNat / 4096 + i / 4096]? with
      | none => exact s.perms.clear _ (by rw [hnat i hin]; omega)
      | some q => rw [hc] at hq; exact hq
    · exact hall i hin
  · exact fun h => .inr h

/-- Make the `size` bytes starting at `a` readable and writable, holding zero.
This is what the kernel does when it hands a program fresh memory. It is
meant for whole pages: the facts below are for a range that starts on a
page, is a whole number of pages, and does not wrap. -/
def mapZero (s : State) (a : BitVec 64) (size : Nat) : State :=
  { s with perms := s.perms.mapRange a size, memory := s.memory.zero a size }

section MapZero

variable (s : State) {a : BitVec 64} {size : Nat} (hal : a.toNat % 4096 = 0)
  (hsz : size % 4096 = 0) (hfit : a.toNat + size ≤ 2 ^ 64)

include hal hsz hfit

theorem perm_mapZero (x : BitVec 64) :
    (s.mapZero a size).perm x = if (x - a).toNat < size then .rw else s.perm x :=
  Perms.get_mapRange _ x hal hsz hfit

theorem mem_mapZero (x : BitVec 64) :
    (s.mapZero a size).mem x = if (x - a).toNat < size then 0 else s.mem x :=
  Memory.get_zero _ x hal hsz hfit

/-- A 64-bit value keeps its value when none of its bytes is in the fresh memory. -/
theorem load64_mapZero_out {y : BitVec 64}
    (h : ∀ j : BitVec 64, j < 8 → ¬ ((y + j) - a).toNat < size) :
    (s.mapZero a size).load64 y = s.load64 y := by
  refine load64_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [mem_mapZero s hal hsz hfit]
  · split
    · next hc => exact absurd hc (by simpa using h 0 (by decide))
    · rfl
  · split
    · next hc => exact absurd hc (h 1 (by decide))
    · rfl
  · split
    · next hc => exact absurd hc (h 2 (by decide))
    · rfl
  · split
    · next hc => exact absurd hc (by have := h 3 (by decide); rwa [show y + 3 = y + 2 + 1 by bv_omega] at this)
    · rfl
  · split
    · next hc => exact absurd hc (h 4 (by decide))
    · rfl
  · split
    · next hc => exact absurd hc (by have := h 5 (by decide); rwa [show y + 5 = y + 4 + 1 by bv_omega] at this)
    · rfl
  · split
    · next hc => exact absurd hc (by have := h 6 (by decide); rwa [show y + 6 = y + 4 + 2 by bv_omega] at this)
    · rfl
  · split
    · next hc => exact absurd hc (by have := h 7 (by decide); rwa [show y + 7 = y + 4 + 2 + 1 by bv_omega] at this)
    · rfl

/-- A 64-bit value that lies in the fresh memory is zero. -/
theorem load64_mapZero_in {y : BitVec 64}
    (h : ∀ j : BitVec 64, j < 8 → ((y + j) - a).toNat < size) :
    (s.mapZero a size).load64 y = 0 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h6 := h 6 (by decide)
  have h7 := h 7 (by decide)
  rw [show y + 0 = y by simp] at h0
  rw [show y + 3 = y + 2 + 1 by bv_omega] at h3
  rw [show y + 5 = y + 4 + 1 by bv_omega] at h5
  rw [show y + 6 = y + 4 + 2 by bv_omega] at h6
  rw [show y + 7 = y + 4 + 2 + 1 by bv_omega] at h7
  simp only [load64, load32, load16, load8, mem_mapZero s hal hsz hfit, h0, h1, h2, h3, h4, h5,
    h6, h7, ↓reduceIte]
  rfl

end MapZero

/-- Make the `size` bytes starting at `a` inaccessible again. What they hold
is of no account: nothing can look. -/
def unmap (s : State) (a : BitVec 64) (size : Nat) : State :=
  { s with perms := s.perms.setRange a size .none }

theorem perm_unmap (s : State) {a : BitVec 64} {size : Nat} (hal : a.toNat % 4096 = 0)
    (hsz : size % 4096 = 0) (hfit : a.toNat + size ≤ 2 ^ 64) (x : BitVec 64) :
    (s.unmap a size).perm x = if (x - a).toNat < size then .none else s.perm x :=
  Perms.get_setRange _ .none x hal hsz hfit


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

def write16 (s : State) (a : BitVec 64) (v : BitVec 16) : Result State :=
  if s.canWrite a 2 then .next (s.store16 a v) else .fault .pageFault

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
