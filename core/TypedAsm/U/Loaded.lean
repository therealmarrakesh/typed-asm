import TypedAsm.U.SegBlock

/-!
# The state a program is loaded into starts as its entry asks

One statement for every program. The segments are placed in a state with
no memory, on pages of their own; a stack's pages are given below the stack
pointer. Then, with each segment as the block of its pages and the stack's
pages as the one region held, the state starts as the entry context asks.
What is asked for this is decided by looking at where the segments and the
stack are: no byte of the state is looked at.
-/

namespace TypedAsm.U

open TypedAsm

/-- Whether a stretch given to a stack is on no page of a segment. -/
def offStack (sb len : Nat) (g : Nat × Perm × List Byte) : Bool :=
  decide ((State.pagesOf sb len).1 + (State.pagesOf sb len).2 ≤ (State.pagesOf g.1 g.2.2.length).1 ∨
    (State.pagesOf g.1 g.2.2.length).1 + (State.pagesOf g.1 g.2.2.length).2 ≤ (State.pagesOf sb len).1)

/-- Whether each segment has bytes and a permission. -/
def segsFull (segs : List (Nat × Perm × List Byte)) : Bool :=
  segs.all fun g => decide (0 < g.2.2.length) && g.2.1.readable

/-- **Each segment's block may be read, and written if it says so**, in a
state whose permissions are those of the segments placed and a stack given,
the stack off the segments' pages. -/
theorem blocksPerm_loaded {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    (hfull : segsFull segs = true) {sb len : BitVec 64}
    (hoff : segs.all (offStack sb.toNat len.toNat) = true) {t : State}
    (hperm : t.perm = ((State.init.loadSegs segs).setPerm sb len .rw).perm) :
    blocksPerm t (segs.map segBlock) = true := by
  have hok' := hok
  simp only [segsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hap, hlow⟩ := hok
  simp only [segsFull, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfull
  have key : ∀ g ∈ segs, ∀ k, k < pageBytes g.2.2.length →
      t.perm (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) = g.2.1 := by
    intro g hg k hk
    have hT : addrTop = 0x7ffffffff000 := rfl
    have hx : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k).toNat = g.1 + k := by
      have := (hlow g hg).2
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hperm, State.perm_setPerm]
    split
    · next hc =>
      exfalso
      have ho := List.all_eq_true.mp hoff g hg
      simp only [offStack, decide_eq_true_eq] at ho
      have hlen := (hfull g hg).1
      have hal := (hlow g hg).1
      rw [hx] at hc
      generalize State.pagesOf sb.toNat len.toNat = pc at hc ho
      unfold State.pagesOf at ho
      unfold pageBytes at hk
      simp only [show g.2.2.length ≠ 0 by omega, ↓reduceIte] at ho
      omega
    · exact perm_segPages hap hg (hlow g hg).1 (hfull g hg).1 (hlow g hg).2 _ hk
  simp only [blocksPerm, List.all_eq_true, List.mem_map, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  rintro x ⟨g, hg, rfl⟩
  have keyg := key g hg
  rw [show (segBlock g).2.size = pageBytes g.2.2.length from Nat.add_zero _]
  show t.canRead (BitVec.ofNat 64 g.1) (pageBytes g.2.2.length) = true ∧
    (g.2.1.writable = false ∨ t.canWrite (BitVec.ofNat 64 g.1) (pageBytes g.2.2.length) = true)
  generalize pageBytes g.2.2.length = n at keyg ⊢
  refine ⟨State.canRead_iff.mpr fun k hk =>
    (congrArg Perm.readable (keyg k hk)).trans (hfull g hg).2, ?_⟩
  cases hw : g.2.1.writable with
  | false => exact .inl rfl
  | true =>
    exact .inr (State.canWrite_iff.mpr fun k hk =>
      (congrArg Perm.writable (keyg k hk)).trans hw)

/-- **The pages given to a stack may be written.** -/
theorem canWrite_stack {s t : State} {sb len : BitVec 64}
    (hperm : t.perm = (s.setPerm sb len .rw).perm) {base : BitVec 64} {size : Nat}
    (hb : base.toNat = 4096 * (State.pagesOf sb.toNat len.toNat).1)
    (hs : size = 4096 * (State.pagesOf sb.toNat len.toNat).2)
    (htop : base.toNat + size ≤ addrTop) : t.canWrite base size = true := by
  have hT : addrTop = 0x7ffffffff000 := rfl
  refine State.canWrite_iff.mpr fun k hk => ?_
  have hx : (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hperm, State.perm_setPerm, hx]
  generalize State.pagesOf sb.toNat len.toNat = pc at hb hs
  split
  · rfl
  · next hc => exact absurd ⟨by omega, by omega, by omega⟩ hc

/-- **The state a program with a stack is loaded into starts as its entry
asks**: each segment the block of its pages, the stack's pages the one
region held. -/
theorem loaded_starts_stack (ρ : Env) {kinds : Nat → Option Shape}
    {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    (hfull : segsFull segs = true) {sb len : BitVec 64}
    (hoff : segs.all (offStack sb.toNat len.toNat) = true) {t : State}
    (hmem : t.mem = (State.init.loadSegs segs).mem)
    (hperm : t.perm = ((State.init.loadSegs segs).setPerm sb len .rw).perm)
    {base : BitVec 64} {size : Nat}
    (hb : base.toNat = 4096 * (State.pagesOf sb.toNat len.toNat).1)
    (hs : size = 4096 * (State.pagesOf sb.toNat len.toNat).2)
    (htop : base.toNat + size ≤ addrTop)
    (hrsp : t.getReg .rsp = base + BitVec.ofNat 64 size)
    (hapart : ((segs.map segBlock).all fun x => decide (Disjoint base size x.1 x.2.size)) = true)
    (hc : ((sb, len) :: segStretches segs []).all
      (stretchIn ((base, size) :: (segs.map segBlock).map fun x => (x.1, x.2.size))) = true) :
    Starts (segs.map segBlock) kinds
      ((entryPatStack size).den { ρ with bound := Fam.ofStack t base :: ρ.bound }) t :=
  starts_stack ρ (blocksPerm_loaded hok hfull hoff hperm)
    (fun x hx bs hs => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact said_segBlock hok hg hmem bs hs)
    (fun x hx => by
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      rfl)
    (canWrite_stack hperm hb hs htop)
    (by have hT : addrTop = 0x7ffffffff000 := rfl; omega) hrsp hapart
    (((PermsWithin.init.loadSegs segs).setPerm sb len .rw).congr hperm) hc

/-- **And one with no stack**: nothing held. -/
theorem loaded_starts (ρ : Env) {kinds : Nat → Option Shape}
    {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    (hfull : segsFull segs = true) {sb len : BitVec 64}
    (hoff : segs.all (offStack sb.toNat len.toNat) = true) {t : State}
    (hmem : t.mem = (State.init.loadSegs segs).mem)
    (hperm : t.perm = ((State.init.loadSegs segs).setPerm sb len .rw).perm)
    (hc : ((sb, len) :: segStretches segs []).all
      (stretchIn ((segs.map segBlock).map fun x => (x.1, x.2.size))) = true) :
    Starts (segs.map segBlock) kinds
      (entryPat.den { ρ with bound := Fam.ofState t :: ρ.bound }) t :=
  starts_entry ρ (blocksPerm_loaded hok hfull hoff hperm)
    (fun x hx bs hs => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact said_segBlock hok hg hmem bs hs)
    (fun x hx => by
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
      rfl)
    (((PermsWithin.init.loadSegs segs).setPerm sb len .rw).congr hperm) hc

/-- Whether each of some blocks a program says the bytes of is, in a list
of blocks, one that says those bytes. -/
def saidCheck (blocks : List (BitVec 64 × Layout)) (said : List (BitVec 64 × List (BitVec 8))) :
    Bool :=
  said.all fun x => blocks.any fun b => b.1 == x.1 && b.2.said == some x.2

/-- Where it is, and no two blocks are at one address, they are blocks of
the memory typing that say those bytes. -/
theorem saidOk_of_check {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    {said : List (BitVec 64 × List (BitVec 8))} (hnd : blocks.Pairwise fun x y => x.1 ≠ y.1)
    (h : saidCheck blocks said = true) : SaidOk (MemTy.ofList blocks kinds) said := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨b, hb, h1, h2⟩ := this
  exact ⟨b.2, h1 ▸ MemTy.ofList_of_mem blocks hnd b hb, h2⟩

/-- Whether something a program says of its static data is seen in a list
of blocks: that an address written out is that of a byte of one of them, a
block of plain bytes. -/
def staticOk (blocks : List (BitVec 64 × Layout)) : Val × TyS → Bool
  | (.lit v, .ptr (.mk size .nil) w off) => blocks.any fun b =>
      decide (b.2.shape.size = size) && b.2.shape.vals.isEmpty && (!w || b.2.writable) &&
        decide (v = b.1 + BitVec.ofNat 64 off)
  | _ => false

/-- **What is seen so is so**, under the typing of those blocks and every
one it grows to. -/
theorem staticsOk_of_check {fetch : Fetch} {sys : Syscall} {blocks : List (BitVec 64 × Layout)}
    {kinds : Nat → Option Shape} {st : List (Val × TyS)}
    (hnd : blocks.Pairwise fun x y => x.1 ≠ y.1) (h : st.all (staticOk blocks) = true) :
    StaticsOk fetch sys (MemTy.ofList blocks kinds) st := by
  intro ρ f hf n Ψ' hext _
  have hc := List.all_eq_true.mp h f hf
  match f, hc with
  | (.lit v, .ptr (.mk size .nil) w off), hc =>
    simp only [staticOk, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true', List.isEmpty_iff] at hc
    obtain ⟨b, hb, ⟨⟨hsz, hvals⟩, hw⟩, hv⟩ := hc
    simp only [TyS.den, ShapeS.den, ValsS.den, Val.den, HasTy]
    refine ⟨b.1, b.2, hext.blocks _ _ (MemTy.ofList_of_mem blocks hnd b hb), ?_, fun hw' => ?_, hv⟩
    · obtain ⟨_, ⟨sz, vals⟩, _⟩ := b
      simp only at hsz hvals
      subst hsz hvals
      rfl
    · rcases hw with hw | hw
      · rw [hw] at hw'; cases hw'
      · exact hw

end TypedAsm.U
