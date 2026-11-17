import TypedAsm.Safety

/-!
# Shapes of bytes, ranges apart, and error numbers

What the machine-level statements of a type system are made of, and that no
type system is needed to say: what a block of memory holds byte for byte,
over some notion of what may be known of a value; when two ranges of bytes
do not overlap; and which values a system call hands back for an error.
-/

namespace TypedAsm

/-- What a block of memory holds, byte for byte, over some notion `τ` of
type: so many bytes, of which some stretches of eight hold a value of a
known type. Every other byte is a plain number, of which nothing is said. A
typed value may sit at any byte, not only at a multiple of eight. -/
structure ShapeOf (τ : Type) where
  /-- The size of the block in bytes. -/
  size : Nat
  /-- The typed values: where each starts, and its type. -/
  vals : List (Nat × τ) := []

namespace ShapeOf

variable {τ : Type}

/-- A block of plain bytes. -/
def raw (n : Nat) : ShapeOf τ := ⟨n, []⟩

@[simp] theorem raw_size (n : Nat) : (raw n : ShapeOf τ).size = n := rfl

@[simp] theorem raw_vals (n : Nat) : (raw n : ShapeOf τ).vals = [] := rfl

/-- Whether the typed value at `p` keeps clear of the `n` bytes from `o`. -/
def clearOf (o n : Nat) (p : Nat × τ) : Bool :=
  p.1 + 8 ≤ o || o + n ≤ p.1

/-- The type of the value that starts at byte `o`, if a typed value does. -/
def valAt (S : ShapeOf τ) (o : Nat) : Option τ :=
  (S.vals.find? fun p => p.1 == o).map (·.2)

/-- Whether the `n` bytes from `o` are all plain: no typed value reaches into them. -/
def free (S : ShapeOf τ) (o n : Nat) : Bool :=
  S.vals.all (clearOf o n)

/-- The block with the `n` bytes from `o` made plain: any typed value that
reaches into them is forgotten. -/
def clear (S : ShapeOf τ) (o n : Nat) : ShapeOf τ :=
  ⟨S.size, S.vals.filter (clearOf o n)⟩

/-- The block with a value of type `t` at byte `o`, in place of whatever
reached into those eight bytes. -/
def set (S : ShapeOf τ) (o : Nat) (t : τ) : ShapeOf τ :=
  ⟨S.size, (o, t) :: (S.clear o 8).vals⟩

/-- Whether exactly one typed value reaches into the eight bytes from `o`. -/
def sole (S : ShapeOf τ) (o : Nat) : Bool :=
  (S.vals.filter fun p => !clearOf o 8 p).length == 1

/-- The first `m` bytes of the block, as a block. -/
def take (S : ShapeOf τ) (m : Nat) : ShapeOf τ :=
  ⟨m, S.vals.filter fun p => p.1 + 8 ≤ m⟩

/-- The block from byte `m` on, as a block. -/
def drop (S : ShapeOf τ) (m : Nat) : ShapeOf τ :=
  ⟨S.size - m, (S.vals.filter fun p => m ≤ p.1).map fun p => (p.1 - m, p.2)⟩

/-- One block followed by another, as one block. -/
def append (S T : ShapeOf τ) : ShapeOf τ :=
  ⟨S.size + T.size, S.vals ++ T.vals.map fun p => (S.size + p.1, p.2)⟩

/-- Whether every typed value lies wholly inside the block. -/
def fits (S : ShapeOf τ) : Bool :=
  S.vals.all fun p => p.1 + 8 ≤ S.size

theorem mem_of_valAt {S : ShapeOf τ} {o : Nat} {t : τ} (h : S.valAt o = some t) :
    (o, t) ∈ S.vals := by
  simp only [valAt, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hp
  have he := List.find?_some hp
  simp only [beq_iff_eq] at he
  rw [← he]
  exact hm

theorem clearOf_of_free {S : ShapeOf τ} {o n : Nat} (h : S.free o n = true) (p : Nat × τ)
    (hp : p ∈ S.vals) : p.1 + 8 ≤ o ∨ o + n ≤ p.1 := by
  have := List.all_eq_true.mp h p hp
  simpa [clearOf] using this

theorem mem_clear {S : ShapeOf τ} {o n : Nat} {p : Nat × τ} (hp : p ∈ (S.clear o n).vals) :
    p ∈ S.vals ∧ (p.1 + 8 ≤ o ∨ o + n ≤ p.1) := by
  simp only [clear, List.mem_filter, clearOf, Bool.or_eq_true, decide_eq_true_eq] at hp
  exact hp

theorem fits_mem {S : ShapeOf τ} (h : S.fits = true) (p : Nat × τ) (hp : p ∈ S.vals) :
    p.1 + 8 ≤ S.size := by
  have := List.all_eq_true.mp h p hp
  simpa using this

/-- Where one typed value alone reaches into eight bytes, any two that do
are the same one. -/
theorem eq_of_sole {S : ShapeOf τ} {o : Nat} (h : S.sole o = true) {p q : Nat × τ}
    (hp : p ∈ S.vals) (hq : q ∈ S.vals) (hpc : ¬(p.1 + 8 ≤ o ∨ o + 8 ≤ p.1))
    (hqc : ¬(q.1 + 8 ≤ o ∨ o + 8 ≤ q.1)) : p = q := by
  simp only [sole, beq_iff_eq] at h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h
  have hp' : p ∈ S.vals.filter fun p => !clearOf o 8 p :=
    List.mem_filter.mpr ⟨hp, by simpa [clearOf] using hpc⟩
  have hq' : q ∈ S.vals.filter fun p => !clearOf o 8 p :=
    List.mem_filter.mpr ⟨hq, by simpa [clearOf] using hqc⟩
  rw [hx] at hp' hq'
  rw [List.mem_singleton.mp hp', List.mem_singleton.mp hq']

/-- The typed values of `n` copies of a block laid end to end from byte `o`. -/
def repFrom (S : ShapeOf τ) (o : Nat) : Nat → List (Nat × τ)
  | 0 => []
  | n + 1 => S.vals.map (fun p => (o + p.1, p.2)) ++ repFrom S (o + S.size) n

/-- `n` copies of a block laid end to end: an array of `n` elements of that
shape. -/
def rep (n : Nat) (S : ShapeOf τ) : ShapeOf τ := ⟨n * S.size, repFrom S 0 n⟩

@[simp] theorem rep_size (n : Nat) (S : ShapeOf τ) : (S.rep n).size = n * S.size := rfl

/-- Every typed value of the copies lies at or after where they start. -/
theorem le_of_mem_repFrom {S : ShapeOf τ} {o n : Nat} {q : Nat × τ}
    (h : q ∈ repFrom S o n) : o ≤ q.1 := by
  induction n generalizing o with
  | zero => cases h
  | succ n ih =>
    simp only [repFrom, List.mem_append, List.mem_map] at h
    rcases h with ⟨p, -, rfl⟩ | h
    · simp
    · have := ih h; omega

/-- And before where they end, when each typed value lies inside its block. -/
theorem lt_of_mem_repFrom {S : ShapeOf τ} (hf : S.fits = true) {o n : Nat} {q : Nat × τ}
    (h : q ∈ repFrom S o n) : q.1 + 8 ≤ o + n * S.size := by
  induction n generalizing o with
  | zero => cases h
  | succ n ih =>
    simp only [repFrom, List.mem_append, List.mem_map] at h
    rw [Nat.succ_mul]
    rcases h with ⟨p, hp, rfl⟩ | h
    · have := fits_mem hf p hp
      simp only
      omega
    · have := ih h; omega

/-- Each typed value of the copies is one of the block's, in one of them. -/
theorem mem_repFrom {S : ShapeOf τ} {o n : Nat} {q : Nat × τ} (h : q ∈ repFrom S o n) :
    ∃ i, i < n ∧ ∃ p ∈ S.vals, q = (o + i * S.size + p.1, p.2) := by
  induction n generalizing o with
  | zero => cases h
  | succ n ih =>
    simp only [repFrom, List.mem_append, List.mem_map] at h
    rcases h with ⟨p, hp, rfl⟩ | h
    · exact ⟨0, by omega, p, hp, by simp⟩
    · obtain ⟨i, hi, p, hp, rfl⟩ := ih h
      exact ⟨i + 1, by omega, p, hp, by rw [Nat.succ_mul]; congr 1; omega⟩

theorem fits_rep {S : ShapeOf τ} (hf : S.fits = true) (n : Nat) : (S.rep n).fits = true := by
  refine List.all_eq_true.mpr fun q hq => decide_eq_true ?_
  have := lt_of_mem_repFrom hf (o := 0) hq
  show q.1 + 8 ≤ n * S.size
  omega

/-- Element `i` of the copies holds what the block holds, `i` blocks on. -/
theorem find_repFrom {S : ShapeOf τ} (hf : S.fits = true) {o n i f : Nat} {t : τ}
    (hi : i < n) (hv : S.valAt f = some t) :
    ((repFrom S o n).find? fun q => q.1 == o + i * S.size + f).map (·.2) = some t := by
  induction n generalizing o i with
  | zero => omega
  | succ n ih =>
    simp only [repFrom, List.find?_append]
    cases i with
    | zero =>
      have e : (S.vals.map fun p => (o + p.1, p.2)).find? (fun q => q.1 == o + 0 * S.size + f)
          = (S.vals.find? fun p => p.1 == f).map fun p => (o + p.1, p.2) := by
        rw [List.find?_map]
        congr 2
        funext p
        simp only [Function.comp, Nat.zero_mul, Nat.add_zero]
        rw [Bool.eq_iff_iff]
        simp only [beq_iff_eq]
        omega
      rw [e]
      simp only [valAt, Option.map_eq_some_iff] at hv
      obtain ⟨p, hp, rfl⟩ := hv
      simp [hp]
    | succ j =>
      have hnone : (S.vals.map fun p => (o + p.1, p.2)).find?
          (fun q => q.1 == o + (j + 1) * S.size + f) = none := by
        rw [List.find?_eq_none]
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        have := fits_mem hf p hp
        rw [Nat.succ_mul]
        simp only [beq_iff_eq]
        omega
      rw [hnone, Option.none_or]
      have := ih (o := o + S.size) (i := j) (by omega)
      rw [Nat.succ_mul]
      rw [show o + (j * S.size + S.size) + f = o + S.size + j * S.size + f by omega]
      exact this

theorem valAt_rep {S : ShapeOf τ} (hf : S.fits = true) {n i f : Nat} {t : τ} (hi : i < n)
    (hv : S.valAt f = some t) : (S.rep n).valAt (i * S.size + f) = some t := by
  have := find_repFrom hf (o := 0) hi hv
  simpa [valAt, rep] using this

/-- Typed values of copies that start at or after the end of a run of bytes
keep clear of it. -/
theorem clear_after {S : ShapeOf τ} {o n x m : Nat} (hx : x + m ≤ o) :
    ∀ q ∈ repFrom S o n, clearOf x m q = true := by
  intro q hq
  have := le_of_mem_repFrom hq
  simp only [clearOf, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem free_repFrom {S : ShapeOf τ} (hf : S.fits = true) {o n i f m : Nat} (hi : i < n)
    (hin : f + m ≤ S.size) (hfree : S.free f m = true) :
    (repFrom S o n).all (clearOf (o + i * S.size + f) m) = true := by
  induction n generalizing o i with
  | zero => omega
  | succ n ih =>
    simp only [repFrom, List.all_append, Bool.and_eq_true]
    cases i with
    | zero =>
      constructor
      · refine List.all_eq_true.mpr fun q hq => ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        have := clearOf_of_free hfree p hp
        simp only [clearOf, Bool.or_eq_true, decide_eq_true_eq]
        omega
      · exact List.all_eq_true.mpr fun q hq => clear_after (by omega) q hq
    | succ j =>
      constructor
      · refine List.all_eq_true.mpr fun q hq => ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        have := fits_mem hf p hp
        rw [Nat.succ_mul]
        simp only [clearOf, Bool.or_eq_true, decide_eq_true_eq]
        omega
      · have := ih (o := o + S.size) (i := j) (by omega)
        rw [Nat.succ_mul,
          show o + (j * S.size + S.size) + f = o + S.size + j * S.size + f by omega]
        exact this

/-- Bytes that are plain in the block are plain in each element of the array. -/
theorem free_rep {S : ShapeOf τ} (hf : S.fits = true) {n i f m : Nat} (hi : i < n)
    (hin : f + m ≤ S.size) (hfree : S.free f m = true) :
    (S.rep n).free (i * S.size + f) m = true := by
  have := free_repFrom hf (o := 0) hi hin hfree
  simpa [free, rep] using this

theorem sole_repFrom {S : ShapeOf τ} (hf : S.fits = true) {o n i f : Nat} (hi : i < n)
    (hin : f + 8 ≤ S.size) (hs : S.sole f = true) :
    ((repFrom S o n).filter fun q => !clearOf (o + i * S.size + f) 8 q).length = 1 := by
  induction n generalizing o i with
  | zero => omega
  | succ n ih =>
    simp only [repFrom, List.filter_append, List.length_append]
    cases i with
    | zero =>
      have hrest : (repFrom S (o + S.size) n).filter
          (fun q => !clearOf (o + 0 * S.size + f) 8 q) = [] :=
        List.filter_eq_nil_iff.mpr fun q hq => by
          rw [clear_after (by omega) q hq]; decide
      have hfirst : ((S.vals.map fun p => (o + p.1, p.2)).filter
          fun q => !clearOf (o + 0 * S.size + f) 8 q).length
            = (S.vals.filter fun p => !clearOf f 8 p).length := by
        rw [List.filter_map, List.length_map]
        congr 2
        funext p
        simp only [Function.comp, clearOf, Nat.zero_mul, Nat.add_zero]
        congr 1
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega
      simp only [sole, beq_iff_eq] at hs
      rw [hfirst, hrest, hs]
      rfl
    | succ j =>
      have hfirst : (S.vals.map fun p => (o + p.1, p.2)).filter
          (fun q => !clearOf (o + (j + 1) * S.size + f) 8 q) = [] :=
        List.filter_eq_nil_iff.mpr fun q hq => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
          have := fits_mem hf p hp
          rw [Nat.succ_mul]
          simp only [clearOf, Bool.or_eq_false_iff, decide_eq_false_iff_not,
            Bool.not_eq_eq_eq_not, Bool.not_true]
          omega
      have := ih (o := o + S.size) (i := j) (by omega)
      rw [hfirst, Nat.succ_mul,
        show o + (j * S.size + S.size) + f = o + S.size + j * S.size + f by omega]
      simpa using this

/-- A typed value alone in its eight bytes of the block is alone in them in
each element of the array. -/
theorem sole_rep {S : ShapeOf τ} (hf : S.fits = true) {n i f : Nat} (hi : i < n)
    (hin : f + 8 ≤ S.size) (hs : S.sole f = true) : (S.rep n).sole (i * S.size + f) = true := by
  have := sole_repFrom hf (o := 0) hi hin hs
  simpa [sole, rep] using this

/-- Eight bytes holding one typed value: what a `push` puts on the stack. -/
def slot (t : τ) : ShapeOf τ := ⟨8, [(0, t)]⟩

@[simp] theorem slot_size (t : τ) : (slot t).size = 8 := rfl

@[simp] theorem valAt_slot (t : τ) : (slot t).valAt 0 = some t := rfl

end ShapeOf

/-- A system call's error result: one of the values from -4095 to -1. -/
def SysErr (v : BitVec 64) : Prop :=
  (-4095 : BitVec 64) ≤ v

instance (v : BitVec 64) : Decidable (SysErr v) := by
  unfold SysErr
  infer_instance

/-- Two byte ranges, given by start and length, do not overlap. Stated so that
it also covers ranges that wrap around the end of the address space. An
empty range overlaps nothing, wherever it starts. -/
def Disjoint (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Prop :=
  (m ≠ 0 → BitVec.ofNat 64 n ≤ b - a) ∧ (n ≠ 0 → BitVec.ofNat 64 m ≤ a - b)

/-- For two ranges that are not empty, what not overlapping comes to. -/
theorem Disjoint.of_pos {a b : BitVec 64} {n m : Nat} (h : Disjoint a n b m) (hn : n ≠ 0)
    (hm : m ≠ 0) : BitVec.ofNat 64 n ≤ b - a ∧ BitVec.ofNat 64 m ≤ a - b :=
  ⟨h.1 hm, h.2 hn⟩

end TypedAsm
