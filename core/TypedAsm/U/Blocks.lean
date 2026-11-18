import TypedAsm.U.Loaded

/-!
# The blocks a program says its segments are

A program's first memory typing is of blocks it says: a record, the nodes
of a list, a table, a line of text, each some bytes of one of its segments.
Whether they are so is seen from the segments: each block lies in the pages
of one, may be written only where the segment may, and says of its bytes
only what the segment's are.
-/

namespace TypedAsm.U

open TypedAsm

/-- The bytes of a segment's pages: its own, and nought to the end. -/
def pageData (g : Nat × Perm × List Byte) : List Byte :=
  g.2.2 ++ List.replicate (pageBytes g.2.2.length - g.2.2.length) 0

theorem pageData_length (g : Nat × Perm × List Byte) :
    (pageData g).length = pageBytes g.2.2.length := by
  have := le_pageBytes g.2.2.length
  simp only [pageData, List.length_append, List.length_replicate]
  omega

/-- **Each byte of a segment's pages is in memory once the segments are
placed.** -/
theorem mem_pageData {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    {g : Nat × Perm × List Byte} (hg : g ∈ segs) {t : State}
    (hmem : t.mem = (State.init.loadSegs segs).mem) {j : Nat} (hj : j < (pageData g).length) :
    t.mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 j) = (pageData g)[j] := by
  rw [hmem]
  by_cases h : j < g.2.2.length
  · rw [mem_segByte segs _ hok g hg j h]
    simp only [pageData, List.getElem_append_left h]
  · rw [mem_segTail hok hg _ (Nat.le_of_not_lt h) (by rw [← pageData_length]; exact hj), mem_init]
    simp only [pageData, List.getElem_append_right (Nat.le_of_not_lt h), List.getElem_replicate]

/-- A state's memory is the segments' on their pages: each byte of each is
there. What lies elsewhere, a program's arguments say, is not asked of. -/
def MemOn (segs : List (Nat × Perm × List Byte)) (t : State) : Prop :=
  ∀ g ∈ segs, ∀ j (hj : j < (pageData g).length),
    t.mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 j) = (pageData g)[j]

/-- It is so of a state whose memory is that of the segments placed. -/
theorem MemOn.of_load {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    {t : State} (hmem : t.mem = (State.init.loadSegs segs).mem) : MemOn segs t :=
  fun _ hg _ hj => mem_pageData hok hg hmem hj

/-- Whether a block is some bytes of a segment's pages: it lies in them; it
may be written only if the segment may; what it says of its bytes, which it
may only of a segment that is not written, is what they are; and its text,
if it has any, ends in a byte of nought. -/
def blockOf (g : Nat × Perm × List Byte) (x : BitVec 64 × Layout) : Bool :=
  decide (g.1 ≤ x.1.toNat) && decide (x.1.toNat + x.2.size ≤ g.1 + pageBytes g.2.2.length) &&
    (!x.2.writable || g.2.1.writable) &&
    (match x.2.said with
     | none => true
     | some bs => !g.2.1.writable && bs.isPrefixOf ((pageData g).drop (x.1.toNat - g.1))) &&
    (x.2.text == 0 ||
      (!g.2.1.writable && (pageData g)[x.1.toNat - g.1 + (x.2.size - 1)]? == some 0))

/-- Whether each of some blocks is of one of the segments. -/
def blocksIn (segs : List (Nat × Perm × List Byte)) (blocks : List (BitVec 64 × Layout)) : Bool :=
  blocks.all fun x => segs.any fun g => blockOf g x

/-- A byte of a block of a segment is a byte of the segment's pages. -/
theorem block_addr {g : Nat × Perm × List Byte} {x : BitVec 64 × Layout}
    (h1 : g.1 ≤ x.1.toNat) (k : Nat) :
    x.1 + BitVec.ofNat 64 k = BitVec.ofNat 64 g.1 + BitVec.ofNat 64 (x.1.toNat - g.1 + k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.1.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

section
variable {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
  (hfull : segsFull segs = true) {sb len : BitVec 64}
  (hoff : segs.all (offStack sb.toNat len.toNat) = true) {t : State}
  (hmem : MemOn segs t)
  (hperm : t.perm = ((State.init.loadSegs segs).setPerm sb len .rw).perm)
  {blocks : List (BitVec 64 × Layout)} (hin : blocksIn segs blocks = true)

include hok hfull hoff hperm hin in
/-- **Each such block may be read, and written if it says so.** -/
theorem blocksPerm_in : blocksPerm t blocks = true := by
  have hT : addrTop = 0x7ffffffff000 := rfl
  have hok' := hok
  have hfull' := hfull
  simp only [segsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  simp only [segsFull, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfull
  simp only [blocksPerm, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  intro x hx
  obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp hin x hx)
  simp only [blockOf, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨⟨h1, h2⟩, hw⟩, _⟩, _⟩ := hb
  have htop := (hok.2 g hg).2
  have key : ∀ k, k < x.2.size → t.perm (x.1 + BitVec.ofNat 64 k) = g.2.1 := fun k hk => by
    rw [block_addr h1 k]
    exact perm_pageByte hok' hfull' hoff hperm hg (by omega)
  refine ⟨State.canRead_iff.mpr fun k hk =>
    (congrArg Perm.readable (key k hk)).trans (hfull g hg).2, ?_⟩
  rcases hw with hw | hw
  · exact .inl hw
  · exact .inr (State.canWrite_iff.mpr fun k hk => (congrArg Perm.writable (key k hk)).trans hw)

include hok hmem hin in
/-- **A block that says its bytes holds them.** -/
theorem said_in : ∀ x ∈ blocks, ∀ bs : List (BitVec 8), x.2.said = some bs →
    ∀ k (hk : k < bs.length), t.mem (x.1 + BitVec.ofNat 64 k) = bs[k] := by
  have hT : addrTop = 0x7ffffffff000 := rfl
  intro x hx bs hs k hk
  obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp hin x hx)
  have hok' := hok
  simp only [segsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  have htop := (hok.2 g hg).2
  simp only [blockOf, hs, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', List.isPrefixOf_iff_prefix] at hb
  obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, _, hpre⟩, _⟩ := hb
  have hlen := hpre.length_le
  rw [List.length_drop] at hlen
  have hj : x.1.toNat - g.1 + k < (pageData g).length := by omega
  rw [block_addr h1 k, hmem g hg _ hj, hpre.getElem hk, List.getElem_drop]

include hok hmem hin in
/-- **The text of each block that has some ends in a byte of nought.** -/
theorem text_in : ∀ x ∈ blocks, x.2.text ≠ 0 →
    t.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0 := by
  have hT : addrTop = 0x7ffffffff000 := rfl
  intro x hx ht
  obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp hin x hx)
  have hok' := hok
  simp only [segsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  have htop := (hok.2 g hg).2
  simp only [blockOf, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, hz⟩ := hb
  rcases hz with hz | ⟨_, hz⟩
  · exact absurd hz ht
  · have hpl := pageData_length g
    have hsz : 0 < x.2.size := by
      unfold Layout.size
      omega
    have hj : x.1.toNat - g.1 + (x.2.size - 1) < (pageData g).length := by omega
    rw [block_addr h1 _, hmem g hg _ hj]
    rw [List.getElem?_eq_getElem hj] at hz
    exact Option.some.inj hz

end

end TypedAsm.U
