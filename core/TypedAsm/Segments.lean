import TypedAsm.Image
import TypedAsm.Elf
import TypedAsm.Entry

/-!
# Where a program is loaded, and the file made of it

A program is one list of lines, in segments. This module says where such a
program is loaded, what the executable file is, and what the state of a
machine that has loaded it is.

The file's layout follows from the program. What the program begins with
comes straight after the file's headers, whose size depends on how many
segments there are; every other segment starts on the next page boundary
after what comes before it, in the file and in memory alike, and is loaded
with the permission the program gave it.
-/

namespace TypedAsm

/-! ## What loading puts in memory

A program is loaded by placing each segment's bytes in turn and giving the
pages they touch the segment's permission. That every line of the program
is then in memory, executable where it is to be executed, is proved here
once for any list of segments, from a comparison of the lines with the
segments: each line lies inside a segment, with that segment's bytes, and
no segment loaded after it touches its bytes or, if it is code, its pages.
A program's own proof is then that comparison and nothing else: no byte of
memory is looked at. -/

/-- A state with these segments placed in turn. -/
def State.loadSegs (s : State) (segs : List (Nat × Perm × List Byte)) : State :=
  segs.foldl (fun s g => s.loadData (BitVec.ofNat 64 g.1) g.2.2 g.2.1) s

namespace Loaded

/-- Whether a run of bytes lies inside a segment, with the segment's bytes
there, and is executable if the segment is. -/
def inside (seg g : Nat × Perm × List Byte) : Bool :=
  decide (seg.1 ≤ g.1) && decide (g.1 + g.2.2.length ≤ seg.1 + seg.2.2.length) &&
    decide (seg.1 + seg.2.2.length ≤ addrTop) &&
    ((seg.2.2.drop (g.1 - seg.1)).take g.2.2.length == g.2.2) &&
    (g.2.1 != .rx || seg.2.1 == .rx)

/-- Whether placing a segment leaves a run of bytes as it was: the segment
is empty, or its bytes are elsewhere and, if the run is code, so are its
pages. -/
def clear (seg g : Nat × Perm × List Byte) : Bool :=
  seg.2.2.isEmpty ||
    (decide (seg.1 + seg.2.2.length ≤ addrTop) && decide (g.1 + g.2.2.length ≤ addrTop) &&
      (decide (g.1 + g.2.2.length ≤ seg.1) || decide (seg.1 + seg.2.2.length ≤ g.1)) &&
      (g.2.1 != .rx || decide ((g.1 + g.2.2.length - 1) / 4096 < seg.1 / 4096) ||
        decide ((seg.1 + seg.2.2.length - 1) / 4096 < g.1 / 4096)))

/-- Whether a run of bytes is in memory once the segments are placed: some
segment holds it, and none placed after that one disturbs it. -/
def holdsIn : List (Nat × Perm × List Byte) → Nat × Perm × List Byte → Bool
  | [], _ => false
  | seg :: rest, g => (inside seg g && rest.all (clear · g)) || holdsIn rest g

/-- Whether every run of bytes is in memory once the segments are placed. -/
def holdsAll (segs parts : List (Nat × Perm × List Byte)) : Bool :=
  parts.all fun g => g.2.2.isEmpty || holdsIn segs g

theorem top : addrTop = 0x7ffffffff000 := rfl

theorem holds_inside {s : State} {seg g : Nat × Perm × List Byte} (h : inside seg g = true) :
    (s.loadData (BitVec.ofNat 64 seg.1) seg.2.2 seg.2.1).Holds g := by
  simp only [inside, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hlo, hhi⟩, htop⟩, hbytes⟩, hperm⟩ := h
  have hT := top
  intro k hk
  have hx : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k).toNat = g.1 + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have ha : (BitVec.ofNat 64 seg.1 : BitVec 64).toNat = seg.1 := by
    rw [BitVec.toNat_ofNat]; omega
  refine ⟨?_, fun hrx => ?_⟩
  · show ((s.setPerm _ _ _).storeBytes (BitVec.ofNat 64 seg.1) seg.2.2).mem _ = _
    rw [State.mem_storeBytes _ _ _ _ (by omega)]
    have hi : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k - BitVec.ofNat 64 seg.1).toNat
        = g.1 - seg.1 + k := by
      rw [BitVec.toNat_sub, hx, ha]
      omega
    have hget : seg.2.2[g.1 - seg.1 + k]? = some g.2.2[k] := by
      have h1 : ((seg.2.2.drop (g.1 - seg.1)).take g.2.2.length)[k]? = g.2.2[k]? := by rw [hbytes]
      rw [List.getElem?_take, if_pos hk, List.getElem?_drop] at h1
      rw [h1, List.getElem?_eq_getElem hk]
    rw [hi, hget]
    rfl
  · show (s.setPerm (BitVec.ofNat 64 seg.1) (BitVec.ofNat 64 seg.2.2.length) seg.2.1).perm _ = _
    have hp : seg.2.1 = .rx := by
      rcases hperm with h | h
      · exact absurd hrx h
      · exact h
    rw [State.perm_setPerm_in s seg.2.1 (by omega) (by
      rw [hx, ha, BitVec.toNat_ofNat]
      omega)]
    exact hp

theorem holds_clear {s : State} {seg g : Nat × Perm × List Byte} (h : clear seg g = true)
    (hg : s.Holds g) : (s.loadData (BitVec.ofNat 64 seg.1) seg.2.2 seg.2.1).Holds g := by
  have hT := top
  simp only [clear, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    List.isEmpty_iff] at h
  intro k hk
  obtain ⟨hm, hp⟩ := hg k hk
  rcases h with hempty | ⟨⟨⟨hstop, hgtop⟩, hapart⟩, hpages⟩
  · -- nothing is placed and no page is touched
    refine ⟨?_, fun hrx => ?_⟩
    · show ((s.setPerm _ _ _).storeBytes _ seg.2.2).mem _ = _
      rw [hempty, State.storeBytes_nil]
      exact hm
    · show (s.setPerm (BitVec.ofNat 64 seg.1) (BitVec.ofNat 64 seg.2.2.length) seg.2.1).perm _ = _
      rw [State.perm_setPerm, hempty]
      simp only [List.length_nil, State.pagesOf, BitVec.toNat_ofNat, Nat.zero_mod, ↓reduceIte,
        Nat.add_zero]
      rw [if_neg (by omega)]
      exact hp hrx
  · have hx : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k).toNat = g.1 + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have ha : (BitVec.ofNat 64 seg.1 : BitVec 64).toNat = seg.1 := by
      rw [BitVec.toNat_ofNat]; omega
    refine ⟨?_, fun hrx => ?_⟩
    · show ((s.setPerm _ _ _).storeBytes (BitVec.ofNat 64 seg.1) seg.2.2).mem _ = _
      rw [State.mem_storeBytes _ _ _ _ (by omega), List.getElem?_eq_none (by
        rw [BitVec.toNat_sub, hx, ha]
        omega)]
      exact hm
    · show (s.setPerm (BitVec.ofNat 64 seg.1) (BitVec.ofNat 64 seg.2.2.length) seg.2.1).perm _ = _
      rw [State.perm_setPerm_out s seg.2.1 (by
        rw [hx, ha, BitVec.toNat_ofNat]
        rcases hpages with (h | h) | h
        · exact absurd hrx h
        · left; omega
        · right; omega)]
      exact hp hrx

theorem holds_rest {g : Nat × Perm × List Byte} :
    ∀ (rest : List (Nat × Perm × List Byte)) (s : State),
      rest.all (clear · g) = true → s.Holds g → (s.loadSegs rest).Holds g
  | [], _, _, hg => hg
  | seg :: rest, s, h, hg => by
    rw [List.all_cons, Bool.and_eq_true] at h
    exact holds_rest rest _ h.2 (holds_clear h.1 hg)

theorem holds_of_holdsIn {g : Nat × Perm × List Byte} :
    ∀ (segs : List (Nat × Perm × List Byte)) (s : State),
      holdsIn segs g = true → (s.loadSegs segs).Holds g
  | [], _, h => by cases h
  | seg :: rest, s, h => by
    simp only [holdsIn, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨hin, hrest⟩ | h
    · exact holds_rest rest _ hrest (holds_inside hin)
    · exact holds_of_holdsIn rest _ h

/-- **Every run of bytes is in memory once the segments are placed**, if the
comparison of the runs with the segments says so. -/
theorem holds_of_holdsAll {segs parts : List (Nat × Perm × List Byte)} (s : State)
    (h : holdsAll segs parts = true) : ∀ g ∈ parts, (s.loadSegs segs).Holds g := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  rw [Bool.or_eq_true] at this
  rcases this with he | hin
  · intro k hk
    rw [List.isEmpty_iff.mp he] at hk
    cases hk
  · exact holds_of_holdsIn segs s hin

/-- Whether giving the `len` bytes at `base` a permission leaves a run of
bytes as it was: it is not code, or its pages are others. -/
def offPages (base len : Nat) (g : Nat × Perm × List Byte) : Bool :=
  g.2.1 != .rx || g.2.2.isEmpty || decide (len = 0) ||
    (decide (base + len ≤ 2 ^ 64) && decide (g.1 + g.2.2.length ≤ 2 ^ 64) &&
      (decide ((g.1 + g.2.2.length - 1) / 4096 < base / 4096) ||
        decide ((base + len - 1) / 4096 < g.1 / 4096)))

/-- A run of bytes is still in memory after some other bytes are given a
permission, if they share no page with it or it is not code. -/
theorem holds_setPerm {s : State} {g : Nat × Perm × List Byte} {base len : BitVec 64} {p : Perm}
    (h : offPages base.toNat len.toNat g = true) (hg : s.Holds g) :
    (s.setPerm base len p).Holds g := by
  simp only [offPages, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    List.isEmpty_iff] at h
  intro k hk
  obtain ⟨hm, hp⟩ := hg k hk
  refine ⟨hm, fun hrx => ?_⟩
  rcases h with ((h | h) | h) | ⟨⟨hb, hgt⟩, hpages⟩
  · exact absurd hrx h
  · rw [h] at hk; cases hk
  · rw [State.perm_setPerm]
    simp only [State.pagesOf, h, ↓reduceIte, Nat.add_zero]
    rw [if_neg (by omega)]
    exact hp hrx
  · have hx : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k).toNat = g.1 + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    rw [State.perm_setPerm_out s p (by
      rw [hx]
      rcases hpages with h | h
      · left; omega
      · right; omega)]
    exact hp hrx

end Loaded

namespace Asm

variable {L : Type} [DecidableEq L]

/-- How many `segment` lines a program has: its segments after the first. -/
def segCount (prog : List (Asm L)) : Nat :=
  (prog.filter fun x => match x with
    | .segment _ => true
    | _ => false).length

/-- Where a program's first line is loaded: straight after the headers of
its executable file. -/
def base (prog : List (Asm L)) : BitVec 64 :=
  BitVec.ofNat 64 (Elf.codeBase (segCount prog))

/-- The program as a Linux executable that starts at the given label. -/
def elf (base : BitVec 64) (prog : List (Asm L)) (start : L) : List Byte :=
  match segments base prog with
  | [] => []
  | (_, _, first) :: rest => Elf.file (addr prog base start).toNat first rest

/-- What the kernel puts in memory from the executable file: each segment's
address, permission and bytes. The first segment of the file begins with the
file's headers, so they are in memory in front of the program, executable
like it, even when the program's own first segment is empty. -/
def image (base : BitVec 64) (prog : List (Asm L)) (start : L) : List (Nat × Perm × List Byte) :=
  match segments base prog with
  | [] => []
  | (a, p, first) :: rest =>
    let head := Elf.headers (addr prog base start).toNat first.length rest
    (a - head.length, p, head ++ first) :: rest

/-- A state with the program in memory as the kernel puts the executable
file there: each segment's bytes where the program puts them, and every
page a segment touches with the segment's permission. -/
def load (s : State) (base : BitVec 64) (prog : List (Asm L)) (start : L) : State :=
  s.loadSegs (image base prog start)

/-- The `n` bytes a program puts in memory from a label on, whatever lines
they come from. Where it puts none, zero. -/
def dataAt (base : BitVec 64) (prog : List (Asm L)) (l : L) (n : Nat) : List Byte :=
  (List.range n).map fun k => (partsByte (parts base prog) ((addr prog base l).toNat + k)).getD 0

/-- **A loaded program is in memory**, line by line, if the comparison of
its lines with what the kernel maps says so. -/
theorem load_holds (s : State) (base : BitVec 64) (prog : List (Asm L)) (start : L)
    (h : Loaded.holdsAll (image base prog start) (parts base prog) = true) :
    ∀ g ∈ parts base prog, (load s base prog start).Holds g :=
  Loaded.holds_of_holdsAll s h

/-- The same, in the state a program declared with `asm_program` starts in:
the program loaded, a stack given, and the stack pointer set. -/
theorem prepared_holds (s : State) (base : BitVec 64) (prog : List (Asm L)) (start : L)
    (sb len v : BitVec 64)
    (h : Loaded.holdsAll (image base prog start) (parts base prog) = true)
    (hs : (parts base prog).all (Loaded.offPages sb.toNat len.toNat) = true) :
    ∀ g ∈ parts base prog,
      (((load s base prog start).setPerm sb len .rw).setReg .rsp v).Holds g :=
  fun g hg =>
    (Loaded.holds_setPerm (List.all_eq_true.mp hs g hg) (load_holds s base prog start h g hg)).congr
      rfl rfl

end Asm

end TypedAsm
