import TypedAsm.U.SegPerm

/-!
# A loaded segment, as a block

A segment placed at the start of a page is given the pages it is on, whole.
As a block of the memory typing it is those pages: of plain bytes, that may
be written if the segment may; and where it may not, the block says its
bytes: the segment's, and nought after them to the end of the page.
-/

namespace TypedAsm.U

open TypedAsm

/-- The bytes of the whole pages that so many bytes from the start of a
page are on. -/
def pageBytes (len : Nat) : Nat := (len + 4095) / 4096 * 4096

/-- The block a segment is. -/
def segBlock (g : Nat × Perm × List Byte) : BitVec 64 × Layout :=
  (BitVec.ofNat 64 g.1,
    { shape := ⟨pageBytes g.2.2.length, []⟩
      writable := g.2.1.writable
      tag := none
      text := 0
      said := if g.2.1.writable then none
        else some (g.2.2 ++ List.replicate (pageBytes g.2.2.length - g.2.2.length) 0) })

/-- **Every byte of a segment's pages has the segment's permission**, once
the segments are placed: where they are on pages of their own, and this one
starts a page, is not empty, and lies where a program can have memory. -/
theorem perm_segPages {segs : List (Nat × Perm × List Byte)} (hap : pagesApart segs = true)
    {g : Nat × Perm × List Byte} (hg : g ∈ segs) (hal : g.1 % 4096 = 0) (hne : 0 < g.2.2.length)
    (htop : g.1 + pageBytes g.2.2.length ≤ addrTop) (s : State) {k : Nat}
    (hk : k < pageBytes g.2.2.length) :
    (s.loadSegs segs).perm (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) = g.2.1 := by
  have hT : addrTop = 0x7ffffffff000 := rfl
  have hx : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k).toNat = g.1 + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine perm_loadSegs_in (by rw [hx]; omega) segs s hap g hg ?_
  rw [hx]
  unfold onPages State.pagesOf
  unfold pageBytes at hk htop
  simp only [show g.2.2.length ≠ 0 by omega, ↓reduceIte]
  omega

/-- Two segments of a list on pages of their own are the same, or on no
page in common. -/
theorem pagesApart_pair : (segs : List (Nat × Perm × List Byte)) → pagesApart segs = true →
    ∀ g ∈ segs, ∀ g' ∈ segs, g = g' ∨ pagesApart2 g g' = true ∨ pagesApart2 g' g = true
  | [], _, g, hg, _, _ => nomatch hg
  | h :: t, hap, g, hg, g', hg' => by
    simp only [pagesApart, Bool.and_eq_true, List.all_eq_true] at hap
    rcases List.mem_cons.mp hg with rfl | hgt <;> rcases List.mem_cons.mp hg' with rfl | hgt'
    · exact .inl rfl
    · exact .inr (.inl (hap.1.2 g' hgt'))
    · exact .inr (.inr (hap.1.2 g hgt))
    · exact pagesApart_pair t hap.2 g hgt g' hgt'

/-- A byte on a page of a segment that starts a page is outside the bytes
of a segment on no page in common with it. -/
theorem out_of_apart {g g' : Nat × Perm × List Byte} (hal : g.1 % 4096 = 0)
    (h : pagesApart2 g g' = true ∨ pagesApart2 g' g = true)
    (hb : g'.1 + g'.2.2.length ≤ addrTop) (htop : g.1 + pageBytes g.2.2.length ≤ addrTop)
    {k : Nat} (hk : k < pageBytes g.2.2.length) :
    BitVec.ofNat 64 g'.2.2.length ≤ BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k - BitVec.ofNat 64 g'.1 := by
  have hT : addrTop = 0x7ffffffff000 := rfl
  simp only [pagesApart2, decide_eq_true_eq] at h
  unfold State.pagesOf at h
  unfold pageBytes at hk htop
  generalize g'.2.2.length = n' at *
  generalize g.2.2.length = n at *
  generalize g.1 = a at *
  generalize g'.1 = a' at *
  by_cases hn' : n' = 0
  · subst hn'
    bv_omega
  · by_cases hn : n = 0
    · subst hn; omega
    · simp only [hn, hn', ↓reduceIte] at h
      have hnat : a' + n' ≤ a + k ∨ a + k < a' := by omega
      bv_omega

/-- Whether the segments of a list are on pages of their own, each starting
a page and with its pages where a program can have memory. -/
def segsOk (segs : List (Nat × Perm × List Byte)) : Bool :=
  pagesApart segs &&
    segs.all fun g => decide (g.1 % 4096 = 0) && decide (g.1 + pageBytes g.2.2.length ≤ addrTop)

theorem le_pageBytes (n : Nat) : n ≤ pageBytes n := by
  unfold pageBytes
  omega

/-- **A segment's bytes are in memory once the segments are placed.** -/
theorem mem_segByte : (segs : List (Nat × Perm × List Byte)) → (s : State) → segsOk segs = true →
    ∀ g ∈ segs, ∀ k (hk : k < g.2.2.length),
      (s.loadSegs segs).mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) = g.2.2[k]
  | [], _, _, g, hg, _, _ => nomatch hg
  | h :: t, s, hok, g, hg, k, hk => by
    have hT : addrTop = 0x7ffffffff000 := rfl
    have hok' := hok
    simp only [segsOk, pagesApart, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      List.mem_cons, forall_eq_or_imp] at hok
    obtain ⟨⟨⟨⟨h1, h2⟩, hall⟩, hrest⟩, ⟨hal, htop⟩, hlow⟩ := hok
    show ((s.loadData (BitVec.ofNat 64 h.1) h.2.2 h.2.1).loadSegs t).mem _ = _
    rcases List.mem_cons.mp hg with rfl | hgt
    · rw [mem_loadSegs_out t _ fun g' hg' => ?_]
      · exact State.hasData_loadData s _ _ _ (by omega) k hk
      · have hg'low := hlow g' hg'
        have := le_pageBytes g'.2.2.length
        exact ⟨by omega, out_of_apart hal (.inl (hall g' hg')) (by omega) htop
          (Nat.lt_of_lt_of_le hk (le_pageBytes _))⟩
    · refine mem_segByte t _ ?_ g hgt k hk
      simp only [segsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      exact ⟨hrest, hlow⟩

/-- **And the rest of its pages is as it was before.** -/
theorem mem_segTail {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    {g : Nat × Perm × List Byte} (hg : g ∈ segs) (s : State) {k : Nat} (hk : g.2.2.length ≤ k)
    (hk2 : k < pageBytes g.2.2.length) :
    (s.loadSegs segs).mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k)
      = s.mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) := by
  have hT : addrTop = 0x7ffffffff000 := rfl
  simp only [segsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hap, hlow⟩ := hok
  refine mem_loadSegs_out segs s fun g' hg' => ?_
  have hg'low := hlow g' hg'
  have hglow := hlow g hg
  have := le_pageBytes g'.2.2.length
  refine ⟨by omega, ?_⟩
  rcases pagesApart_pair segs hap g hg g' hg' with rfl | hapart
  · generalize g.2.2.length = n at *
    generalize g.1 = a at *
    bv_omega
  · exact out_of_apart hglow.1 hapart (by omega) hglow.2 hk2

/-- **So a segment that may not be written, as a block, holds the bytes it
says**: its own, and nought to the end of its pages, in any state whose
memory is that of the segments placed in a state with none. -/
theorem said_segBlock {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    {g : Nat × Perm × List Byte} (hg : g ∈ segs) {t : State}
    (hmem : t.mem = (State.init.loadSegs segs).mem) (bs : List (BitVec 8))
    (hs : (segBlock g).2.said = some bs) :
    ∀ k (hk : k < bs.length), t.mem ((segBlock g).1 + BitVec.ofNat 64 k) = bs[k] := by
  have hs' : (if g.2.1.writable then none
      else some (g.2.2 ++ List.replicate (pageBytes g.2.2.length - g.2.2.length) 0)) = some bs := hs
  split at hs'
  · cases hs'
  · cases hs'
    refine said_of_data_zeros (A := BitVec.ofNat 64 g.1) (fun k hk => ?_) (fun k hk => ?_)
    · rw [hmem]
      exact mem_segByte segs _ hok g hg k hk
    · rw [hmem, mem_segTail hok hg _ (Nat.le_add_right _ _) (by omega)]
      exact mem_init _

end TypedAsm.U
