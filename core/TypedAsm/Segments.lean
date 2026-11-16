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
      rw [List.getElem?_take, ite_eq_left hk, List.getElem?_drop] at h1
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
      rw [ite_eq_right (by omega)]
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

/-! ### The comparison without the bytes

That a line's bytes are the ones its segment has where the line is, is so
for every program: the segments are made of the lines. What a program's own
proof has left to compare is then where things are, and no byte. -/

/-- Whether a run of bytes is within a segment's extent. -/
def rangeIn (seg g : Nat × Perm × List Byte) : Bool :=
  decide (seg.1 ≤ g.1) && decide (g.1 + g.2.2.length ≤ seg.1 + seg.2.2.length)

/-- What `inside` asks besides the extent and the bytes. -/
def insideLen (seg g : Nat × Perm × List Byte) : Bool :=
  decide (seg.1 + seg.2.2.length ≤ addrTop) && (g.2.1 != .rx || seg.2.1 == .rx)

/-- Whether a run of bytes is in memory once the segments are placed, if the
first segment whose extent it is within has its bytes there. -/
def holdsInLen : List (Nat × Perm × List Byte) → Nat × Perm × List Byte → Bool
  | [], _ => false
  | seg :: rest, g =>
    if rangeIn seg g then insideLen seg g && rest.all (clear · g) else holdsInLen rest g

/-- Whether every run of bytes is in memory once the segments are placed, if
each has its bytes in the first segment whose extent it is within. -/
def holdsAllLen (segs parts : List (Nat × Perm × List Byte)) : Bool :=
  parts.all fun g => g.2.2.isEmpty || holdsInLen segs g

/-- A segment has a run of bytes: within its extent, with those bytes there. -/
def Has (seg g : Nat × Perm × List Byte) : Prop :=
  rangeIn seg g = true ∧ (seg.2.2.drop (g.1 - seg.1)).take g.2.2.length = g.2.2

theorem not_clear_of_has {seg g : Nat × Perm × List Byte} (h : Has seg g) (hne : g.2.2 ≠ []) :
    clear seg g = false := by
  obtain ⟨hr, _⟩ := h
  simp only [rangeIn, Bool.and_eq_true, decide_eq_true_eq] at hr
  have hlen : 0 < g.2.2.length := List.length_pos_iff.mpr hne
  have hseg : seg.2.2 ≠ [] := by
    intro e
    rw [e] at hr
    simp only [List.length_nil] at hr
    omega
  cases hc : clear seg g with
  | false => rfl
  | true =>
    simp only [clear, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hc
    rcases hc with he | ⟨⟨_, hd⟩, _⟩
    · exact absurd he hseg
    · omega

theorem holdsIn_of_len {g : Nat × Perm × List Byte} (hne : g.2.2 ≠ []) :
    ∀ segs : List (Nat × Perm × List Byte), (∃ seg ∈ segs, Has seg g) →
      holdsInLen segs g = true → holdsIn segs g = true
  | [], _, h => by cases h
  | seg :: rest, hhas, h => by
    unfold holdsInLen at h
    unfold holdsIn
    by_cases hr : rangeIn seg g = true
    · simp only [hr, ↓reduceIte] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hi, hc⟩ := h
      have hseg : Has seg g := by
        obtain ⟨s', hs', hH⟩ := hhas
        rcases List.mem_cons.mp hs' with rfl | hin
        · exact hH
        · have := List.all_eq_true.mp hc s' hin
          rw [not_clear_of_has hH hne] at this
          cases this
      have hin : inside seg g = true := by
        simp only [rangeIn, Bool.and_eq_true, decide_eq_true_eq] at hr
        simp only [insideLen, Bool.and_eq_true, decide_eq_true_eq] at hi
        simp only [inside, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨⟨⟨hr.1, hr.2⟩, hi.1⟩, hseg.2⟩, hi.2⟩
      rw [hin, hc]; rfl
    · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
      have : ∃ seg ∈ rest, Has seg g := by
        obtain ⟨s', hs', hH⟩ := hhas
        rcases List.mem_cons.mp hs' with rfl | hin
        · exact absurd hH.1 hr
        · exact ⟨s', hin, hH⟩
      rw [holdsIn_of_len hne rest this h, Bool.or_true]

/-- The comparison without the bytes says what the one with them does, where
each run of bytes is some segment's. -/
theorem holdsAll_of_len {segs parts : List (Nat × Perm × List Byte)}
    (hhas : ∀ g ∈ parts, g.2.2 ≠ [] → ∃ seg ∈ segs, Has seg g)
    (h : holdsAllLen segs parts = true) : holdsAll segs parts = true := by
  refine List.all_eq_true.mpr fun g hg => ?_
  have := List.all_eq_true.mp h g hg
  rw [Bool.or_eq_true] at this ⊢
  rcases this with he | hl
  · exact .inl he
  · by_cases hne : g.2.2 = []
    · exact .inl (List.isEmpty_iff.mpr hne)
    · exact .inr (holdsIn_of_len hne segs (hhas g hg hne) hl)

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
    rw [ite_eq_right (by omega)]
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

/-! ### Every line is in its segment

The segments are made of the lines, so each line's bytes are in the segment
it belongs to, where the line is. This is so for every program. -/

theorem le_alignUp (a n : Nat) : a ≤ alignUp a n := by
  unfold alignUp
  split
  · exact Nat.le_refl a
  · next hn =>
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have h := Nat.lt_mul_div_succ (a + (n - 1)) hn'
    rw [Nat.mul_succ, Nat.mul_comm] at h
    omega

omit [DecidableEq L] in
/-- A line that does not start a segment ends where the next begins. -/
theorem next_eq (target : L → BitVec 64) (a : Nat) (x : Asm L) (hx : ∀ q, x ≠ .segment q) :
    next a x = a + (lineBytes target a x).length := by
  cases x with
  | segment q => exact absurd rfl (hx q)
  | align n =>
    show alignUp a n = a + (List.replicate (alignUp a n - a) (0 : Byte)).length
    rw [List.length_replicate]
    have := le_alignUp a n
    omega
  | ins i => rfl
  | label l => rfl
  | jmp l => show a + _ = a + _; simp [len, lineBytes, instr, Instr.length, Instr.encode, le32]
  | jcc c l => show a + _ = a + _; simp [len, lineBytes, instr, Instr.length, Instr.encode, le32]
  | call l => show a + _ = a + _; simp [len, lineBytes, instr, Instr.length, Instr.encode, le32]
  | ref i l past =>
    show a + i.length = a + ((i.aim _ _).encode).length
    rw [← Instr.length_aim i]; rfl
  | bytes bs => rfl
  | quad l => show a + 8 = a + (le64 _).length; simp [le64, le32]
  | space n => show a + n = a + (List.replicate n (0 : Byte)).length; rw [List.length_replicate]

omit [DecidableEq L] in
/-- The segment being put together is among the segments, with what was
put in it so far at its start. -/
theorem segmentsFrom_grows (target : L → BitVec 64) :
    ∀ (prog : List (Asm L)) (a : Nat) (cur : Nat × Perm × List Byte),
      ∃ seg ∈ segmentsFrom target a cur prog,
        seg.1 = cur.1 ∧ seg.2.1 = cur.2.1 ∧ ∃ more, seg.2.2 = cur.2.2 ++ more
  | [], _, cur => ⟨cur, List.mem_singleton.mpr rfl, rfl, rfl, [], (List.append_nil _).symm⟩
  | x :: rest, a, cur => by
    by_cases hx : ∃ q, x = .segment q
    · obtain ⟨q, rfl⟩ := hx
      exact ⟨cur, List.mem_cons_self, rfl, rfl, [], (List.append_nil _).symm⟩
    · have hx' : ∀ q, x ≠ .segment q := fun q e => hx ⟨q, e⟩
      have hstep : segmentsFrom target a cur (x :: rest) =
          segmentsFrom target (next a x) (cur.1, cur.2.1, cur.2.2 ++ lineBytes target a x) rest := by
        cases x <;> first | rfl | exact absurd rfl (hx' _)
      obtain ⟨seg, hs, h1, h2, more, hm⟩ := segmentsFrom_grows target rest (next a x)
        (cur.1, cur.2.1, cur.2.2 ++ lineBytes target a x)
      exact ⟨seg, by rw [hstep]; exact hs, h1, h2, lineBytes target a x ++ more,
        by rw [hm]; exact List.append_assoc _ _ _⟩

omit [DecidableEq L] in
/-- **Each line's bytes are in a segment, where the line is.** -/
theorem partsFrom_has (target : L → BitVec 64) :
    ∀ (prog : List (Asm L)) (a : Nat) (p : Perm) (cur : Nat × Perm × List Byte),
      a = cur.1 + cur.2.2.length →
      ∀ g ∈ partsFrom target a p prog, g.2.2 ≠ [] →
        ∃ seg ∈ segmentsFrom target a cur prog, Loaded.Has seg g
  | [], _, _, _, _, g, hg, _ => by cases hg
  | x :: rest, a, p, cur, ha, g, hg, hne => by
    rcases List.mem_cons.mp hg with rfl | hin
    · -- the line itself: in the segment being put together
      by_cases hx : ∃ q, x = .segment q
      · obtain ⟨q, rfl⟩ := hx
        exact absurd rfl hne
      · have hx' : ∀ q, x ≠ .segment q := fun q e => hx ⟨q, e⟩
        have hstep : segmentsFrom target a cur (x :: rest) =
            segmentsFrom target (next a x) (cur.1, cur.2.1, cur.2.2 ++ lineBytes target a x) rest := by
          cases x <;> first | rfl | exact absurd rfl (hx' _)
        obtain ⟨seg, hs, h1, _, more, hm⟩ := segmentsFrom_grows target rest (next a x)
          (cur.1, cur.2.1, cur.2.2 ++ lineBytes target a x)
        refine ⟨seg, by rw [hstep]; exact hs, ?_, ?_⟩
        · simp only [Loaded.rangeIn, Bool.and_eq_true, decide_eq_true_eq]
          rw [h1, hm]
          simp only [List.length_append]
          omega
        · show (seg.2.2.drop (a - seg.1)).take (lineBytes target a x).length = lineBytes target a x
          rw [h1, hm, show a - cur.1 = cur.2.2.length from by omega, List.append_assoc,
            List.drop_left, List.take_left]
    · -- a later line
      by_cases hx : ∃ q, x = .segment q
      · obtain ⟨q, rfl⟩ := hx
        obtain ⟨seg, hs, hH⟩ := partsFrom_has target rest (pageUp a) q (pageUp a, q, [])
          (by simp) g hin hne
        exact ⟨seg, List.mem_cons_of_mem _ hs, hH⟩
      · have hx' : ∀ q, x ≠ .segment q := fun q e => hx ⟨q, e⟩
        have hstep : segmentsFrom target a cur (x :: rest) =
            segmentsFrom target (next a x) (cur.1, cur.2.1, cur.2.2 ++ lineBytes target a x) rest := by
          cases x <;> first | rfl | exact absurd rfl (hx' _)
        have hperm : perm p x = p := by
          cases x <;> first | rfl | exact absurd rfl (hx' _)
        rw [hstep]
        refine partsFrom_has target rest (next a x) p _ ?_ g (by rw [← hperm]; exact hin) hne
        rw [next_eq target a x hx']
        simp only [List.length_append]
        omega

/-- Whether the file's headers fit in front of the program's first segment. -/
def headOk (base : BitVec 64) (prog : List (Asm L)) (start : L) : Bool :=
  match segments base prog with
  | [] => true
  | (a, _, first) :: rest =>
    decide ((Elf.headers (addr prog base start).toNat first.length rest).length ≤ a)

/-- Each line's bytes are in what the kernel maps, where the line is. -/
theorem image_has (base : BitVec 64) (prog : List (Asm L)) (start : L)
    (hh : headOk base prog start = true) :
    ∀ g ∈ parts base prog, g.2.2 ≠ [] → ∃ seg ∈ image base prog start, Loaded.Has seg g := by
  intro g hg hne
  obtain ⟨seg, hs, hH⟩ := partsFrom_has (addr prog base) prog base.toNat .rx
    (base.toNat, .rx, []) (by simp) g hg hne
  unfold headOk at hh
  unfold image
  have hs' : seg ∈ segments base prog := hs
  cases hsegs : segments base prog with
  | nil => rw [hsegs] at hs'; cases hs'
  | cons s₀ rest =>
    obtain ⟨a, p, first⟩ := s₀
    rw [hsegs] at hs' hh
    simp only [decide_eq_true_eq] at hh
    rcases List.mem_cons.mp hs' with rfl | hin
    · -- in the first segment, which the headers are put in front of
      refine ⟨_, List.mem_cons_self, ?_, ?_⟩
      · obtain ⟨hr, _⟩ := hH
        simp only [Loaded.rangeIn, Bool.and_eq_true, decide_eq_true_eq, List.length_append] at hr ⊢
        omega
      · obtain ⟨hr, hb⟩ := hH
        simp only [Loaded.rangeIn, Bool.and_eq_true, decide_eq_true_eq] at hr
        show (List.drop (g.1 - (a - _)) (_ ++ first)).take _ = _
        rw [show g.1 - (a - (Elf.headers (addr prog base start).toNat first.length rest).length)
            = (Elf.headers (addr prog base start).toNat first.length rest).length + (g.1 - a)
          from by omega, List.drop_append, List.drop_of_length_le (Nat.le_add_right _ _),
          List.nil_append, Nat.add_sub_cancel_left]
        exact hb
    · exact ⟨seg, List.mem_cons_of_mem _ hin, hH⟩

/-- **A loaded program is in memory**, line by line, if the comparison of
where its lines are with what the kernel maps says so: that each line's
bytes are the ones mapped there is so for every program. -/
theorem load_holds (s : State) (base : BitVec 64) (prog : List (Asm L)) (start : L)
    (h : Loaded.holdsAllLen (image base prog start) (parts base prog) = true)
    (hh : headOk base prog start = true) :
    ∀ g ∈ parts base prog, (load s base prog start).Holds g :=
  Loaded.holds_of_holdsAll s (Loaded.holdsAll_of_len (image_has base prog start hh) h)

/-- The same, in the state a program declared with `asm_program` starts in:
the program loaded, a stack given, and the stack pointer set. -/
theorem prepared_holds (s : State) (base : BitVec 64) (prog : List (Asm L)) (start : L)
    (sb len v : BitVec 64)
    (h : Loaded.holdsAllLen (image base prog start) (parts base prog) = true)
    (hh : headOk base prog start = true)
    (hs : (parts base prog).all (Loaded.offPages sb.toNat len.toNat) = true) :
    ∀ g ∈ parts base prog,
      (((load s base prog start).setPerm sb len .rw).setReg .rsp v).Holds g :=
  fun g hg =>
    (Loaded.holds_setPerm (List.all_eq_true.mp hs g hg) (load_holds s base prog start h hh g hg)).congr
      rfl rfl

end Asm

end TypedAsm
