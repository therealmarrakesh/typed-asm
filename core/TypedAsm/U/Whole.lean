import TypedAsm.U.Blocks
import TypedAsm.U.Begin
import TypedAsm.U.LayoutS
import TypedAsm.U.Typed
import TypedAsm.Linux
import TypedAsm.Declare

/-!
# A whole program, checked

One check for a program as written: that its labels' code is typed, and
that the state it is loaded into starts as its entry label asks. And one
statement of what the check shows. A program is its lines, the label it
starts at, and how many slots of stack it is given; the state it starts in
is the one the kernel makes of it.
-/

namespace TypedAsm.U

attribute [local instance] IsLabel.dec

open TypedAsm

deriving instance DecidableEq for CtxS

variable {L : Type} [IsLabel L]

/-- The blocks of a program's first memory typing: each segment, as the
block of its pages. -/
def blocksOf (code : List (Asm L)) (l : L) : List (BitVec 64 × LayoutS) :=
  (Asm.imageFast (Asm.base code) code l).map fun g =>
    (BitVec.ofNat 64 g.1,
      { shape := .mk (pageBytes g.2.2.length) .nil
        writable := g.2.1.writable
        said := if g.2.1.writable then none else some (pageData g) })

/-- Whether an address is code wanting a family, by a program's labels:
asked of each address a said block's shape says is code. -/
def codeJ (pg : Prog) (labels : List Label) (fuel : Nat) : BitVec 64 → CtxS → Bool :=
  fun a E =>
    justifyF pg pg.index (labelIx labels).find (labelIx labels).byAddr.has fuel fuel 0 a E

/-- The stretch of memory a program is given for its stack: so many slots
below where the kernel puts its arguments, and the room for those. -/
def stackStretch (n : Nat) : BitVec 64 × BitVec 64 :=
  (argBase - BitVec.ofNat 64 (8 * n), BitVec.ofNat 64 (8 * n + 0x10000))

/-- **The state a program is started in with arguments**: its segments
placed as the kernel places them, the stack given with the arguments on it
and so many slots below them, and the instruction pointer at the label it
starts at; in any world. -/
def startIn (code : List (Asm L)) (l : L) (n : Nat) (args : List (List Byte)) (w : World) :
    State :=
  { Asm.startArgs code l n args with world := w }

/-- It is the program in memory, given its stack and arguments, at its
entry, in that world. -/
theorem startIn_eq (code : List (Asm L)) (l : L) (n : Nat) (args : List (List Byte)) (w : World) :
    startIn code l n args w
      = startState (Asm.load State.init (Asm.base code) code l)
          (Asm.addr code (Asm.base code) l) n args w := rfl

/-- The state a program is started in is that state, in the world it has. -/
theorem startArgs_eq (code : List (Asm L)) (l : L) (n : Nat) (args : List (List Byte)) :
    Asm.startArgs code l n args = startIn code l n args (Asm.startArgs code l n args).world :=
  rfl

/-- **The program's bytes are in memory still once the arguments are
placed**, where they lie below the stack. -/
theorem start_holds {code : List (Asm L)} {l : L}
    (hholds : Loaded.holdsAllE (Asm.imageExt (Asm.base code) code)
      (Asm.partsExt (Asm.base code) code) = true)
    (hhead : Asm.headOkE (Asm.base code) code = true)
    {n : Nat} (hn : 8 * n ≤ 0x7fff0000)
    (hbelow : (Asm.partsExt (Asm.base code) code).all
      (fun g => decide (g.1 + g.2.2 ≤ stackLow n)) = true)
    (args : List (List Byte)) (w : World) :
    ∀ g ∈ Asm.parts (Asm.base code) code, (startIn code l n args w).Holds g := by
  intro g hg k hk
  have hl := Asm.load_holds State.init (Asm.base code) code l hholds hhead g hg k hk
  have hb : g.1 + g.2.2.length ≤ stackLow n := by
    rw [← Asm.parts_ext, List.all_map] at hbelow
    exact of_decide_eq_true (List.all_eq_true.mp hbelow g hg)
  have hlow := stackLow_le n
  have hx : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k).toNat < stackLow n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hm : (startIn code l n args w).mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k)
      = (Asm.load State.init (Asm.base code) code l).mem
          (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) :=
    State.mem_withArgs_below _ n args (by
      have : argBase.toNat = 0x7fff0000 := rfl
      omega)
  have hp : (startIn code l n args w).perm (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k)
      = (Asm.load State.init (Asm.base code) code l).perm
          (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) :=
    State.perm_withArgs_below _ n args hn hx
  rw [hm, hp]
  exact hl

section
variable {B : List (BitVec 64 × Layout)} (args : List (List Byte))

theorem argBlocks_mem {x : BitVec 64 × Layout} (hx : x ∈ argBlocks args) :
    x = (argBase + 8, argvLayout args) ∨
      x = (argBase + BitVec.ofNat 64 (argBytes args).length, restLayout args) := by
  simpa only [argBlocks, List.mem_cons, List.not_mem_nil, or_false] using hx

/-- Where the stack's two blocks are, and how long: after the count, and
within the stack's memory. -/
theorem argBlocks_at {x : BitVec 64 × Layout} (hx : x ∈ argBlocks args) :
    argBase.toNat + 8 ≤ x.1.toNat ∧ x.1.toNat + x.2.size ≤ argBase.toNat + 0x10000 ∧
      0 < x.2.size := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hL := argBytes_length_le args
  have hL' := argBytes_length args
  have hsz := argvLayout_size args
  have hA8 : (argBase + 8).toNat = 0x7fff0008 := rfl
  have hAL : (argBase + BitVec.ofNat 64 (argBytes args).length).toNat
      = 0x7fff0000 + (argBytes args).length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase]
    omega
  have hrest : (restLayout args).size = 0x10000 - (argBytes args).length := by
    simp only [restLayout, Layout.size]
    omega
  rcases argBlocks_mem args hx with rfl | rfl
  · show argBase.toNat + 8 ≤ (argBase + 8).toNat ∧
      (argBase + 8).toNat + (argvLayout args).size ≤ argBase.toNat + 0x10000 ∧
        0 < (argvLayout args).size
    omega
  · show argBase.toNat + 8 ≤ (argBase + BitVec.ofNat 64 (argBytes args).length).toNat ∧
      (argBase + BitVec.ofNat 64 (argBytes args).length).toNat + (restLayout args).size
        ≤ argBase.toNat + 0x10000 ∧ 0 < (restLayout args).size
    omega

/-- No two blocks are at one address: the program's, which lie below the
stack, and the stack's two. -/
theorem nd_args (hnd : B.Pairwise fun x y => x.1 ≠ y.1)
    (hbelow : ∀ x ∈ B, x.1.toNat + x.2.size ≤ argBase.toNat) (hpos : ∀ x ∈ B, 0 < x.2.size) :
    (B ++ argBlocks args).Pairwise fun x y => x.1 ≠ y.1 := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hL := argBytes_length_le args
  have hL' := argBytes_length args
  refine List.pairwise_append.mpr ⟨hnd, ?_, fun x hx y hy he => ?_⟩
  · refine List.pairwise_cons.mpr ⟨fun y hy he => ?_, List.pairwise_singleton _ _⟩
    cases List.mem_singleton.mp hy
    have h1 : (argBase + 8).toNat = 0x7fff0008 := rfl
    have h2 : (argBase + BitVec.ofNat 64 (argBytes args).length).toNat
        = 0x7fff0000 + (argBytes args).length := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase]
      omega
    have := congrArg BitVec.toNat he
    rw [h1, h2] at this
    omega
  · have h1 := hbelow x hx
    have h2 := hpos x hx
    have h3 := (argBlocks_at args hy).1
    rw [he] at h1
    omega

/-- **The program's blocks and the stack's two are well formed together**,
where the program's are, and lie below the stack. -/
theorem wf_args {kinds : Nat → Option Shape} (hwf : (MemTy.ofList B kinds).WF)
    (hnd : B.Pairwise fun x y => x.1 ≠ y.1)
    (hbelow : ∀ x ∈ B, x.1.toNat + x.2.size ≤ argBase.toNat) :
    (MemTy.ofList (B ++ argBlocks args) kinds).WF := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hB : ∀ {a l}, (a, l) ∈ B → MemTy.ofList B kinds a = some l :=
    fun h => MemTy.ofList_of_mem B hnd _ h
  have hsplit : ∀ {a l}, MemTy.ofList (B ++ argBlocks args) kinds a = some l →
      (a, l) ∈ B ∨ (a, l) ∈ argBlocks args :=
    fun h => List.mem_append.mp (MemTy.mem_of_ofList h)
  refine ⟨fun a l hl => ?_, fun a b la lb ha hb hab => ?_, fun a l hl => ?_,
    fun a l hl q hq => ?_, fun a l hl tag ht => ?_, fun a l bs hl hs => ?_⟩
  · rcases hsplit hl with h | h
    · exact hwf.size_lt a l (hB h)
    · have : argBase.toNat + 8 ≤ a.toNat ∧ a.toNat + l.size ≤ argBase.toNat + 0x10000 ∧
          0 < l.size := argBlocks_at args h
      show l.size < 2 ^ 64
      have h2 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
      omega
  · rcases hsplit ha with h1 | h1 <;> rcases hsplit hb with h2 | h2
    · exact hwf.disjoint a b la lb (hB h1) (hB h2) hab
    · have hx : a.toNat + la.size ≤ argBase.toNat := hbelow _ h1
      have hy : argBase.toNat + 8 ≤ b.toNat ∧ b.toNat + lb.size ≤ argBase.toNat + 0x10000 ∧
          0 < lb.size := argBlocks_at args h2
      exact disjoint_of_before (a := a) (n := la.size) (b := b) (m := lb.size) (by omega) (by omega)
    · have hx : b.toNat + lb.size ≤ argBase.toNat := hbelow _ h2
      have hy : argBase.toNat + 8 ≤ a.toNat ∧ a.toNat + la.size ≤ argBase.toNat + 0x10000 ∧
          0 < la.size := argBlocks_at args h1
      exact (disjoint_of_before (a := b) (n := lb.size) (b := a) (m := la.size) (by omega)
        (by omega)).symm
    · have hL := argBytes_length_le args
      have hL' := argBytes_length args
      have hsz := argvLayout_size args
      have hA8 : (argBase + 8).toNat = 0x7fff0008 := rfl
      have hAL : (argBase + BitVec.ofNat 64 (argBytes args).length).toNat
          = 0x7fff0000 + (argBytes args).length := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase]
        omega
      have hrest : (restLayout args).size = 0x10000 - (argBytes args).length := by
        simp only [restLayout, Layout.size]
        omega
      rcases argBlocks_mem args h1 with e1 | e1 <;> rcases argBlocks_mem args h2 with e2 | e2
      · exact absurd (congrArg Prod.fst e1 |>.trans (congrArg Prod.fst e2).symm) hab
      · cases e1; cases e2
        exact disjoint_of_before (a := argBase + 8) (n := (argvLayout args).size)
          (b := argBase + BitVec.ofNat 64 (argBytes args).length) (m := (restLayout args).size)
          (by omega) (by omega)
      · cases e1; cases e2
        exact (disjoint_of_before (a := argBase + 8) (n := (argvLayout args).size)
          (b := argBase + BitVec.ofNat 64 (argBytes args).length) (m := (restLayout args).size)
          (by omega) (by omega)).symm
      · exact absurd (congrArg Prod.fst e1 |>.trans (congrArg Prod.fst e2).symm) hab
  · rcases hsplit hl with h | h
    · exact hwf.nonempty a l (hB h)
    · exact (argBlocks_at args h).2.2
  · rcases hsplit hl with h | h
    · exact hwf.fits a l (hB h) q hq
    · rcases argBlocks_mem args h with e | e
      · cases e
        obtain ⟨i, hi, rfl⟩ := argvVals_spec 0 _ q hq
        show 0 + 8 * i + 8 ≤ 8 * (argsGiven args).length + 32
        omega
      · cases e
        cases hq
  · rcases hsplit hl with h | h
    · exact hwf.kinds a l (hB h) tag ht
    · rcases argBlocks_mem args h with e | e <;> cases e <;> cases ht
  · rcases hsplit hl with h | h
    · exact hwf.said a l bs (hB h) hs
    · rcases argBlocks_mem args h with e | e <;> cases e <;> cases hs

end

/-- **Whether a program as written is typed and starts as its
entry asks.** As for a program started without: the checker's program is
the assembled table, the entry label is among the labels with the entry
context for arguments, the labels' code is typed, the blocks the program
says are seen in its segments; and the program lies below the stack. -/
def wholeOkWith (code : List (Asm L)) (l : L) (n : Nat) (ks : List (Nat × ShapeS))
    (bs : List (BitVec 64 × LayoutS)) (pg : Prog) (labels : List Label) (fuel : Nat) : Bool :=
  let base := Asm.base code
  let segs := Asm.imageFast base code l
  let blocks := denBlocks bs
  decide (pg.code = progCode (Asm.table base code)) &&
  labels.any (fun x => decide (x.addr = Asm.addr code base l) && decide (x.pat = entryCtx (stackRoom n))) &&
  decide (8 * n ≤ 0x7fff0000) &&
  checkProgram pg labels fuel 0 && tableOk (Asm.table base code) && blocksWf blocks &&
  decide (blocks.Pairwise fun x y => x.1 ≠ y.1) && segsOk segs && segsFull segs &&
  segs.all (offStack (stackStretch n).1.toNat (stackStretch n).2.toNat) &&
  Loaded.holdsAllE (Asm.imageExt base code) (Asm.partsExt base code) && Asm.headOkE base code &&
  (Asm.partsExt base code).all (fun g => decide (g.1 + g.2.2 ≤ stackLow n)) &&
  segs.all (fun g => decide (g.1 + pageBytes g.2.2.length ≤ stackLow n)) &&
  (segStretches segs []).all (stretchIn (blocks.map fun x => (x.1, x.2.size))) &&
  pg.statics.all (staticS bs) && blocksIn segs blocks &&
  valsHold (codeJ pg labels fuel) segs bs &&
  kindsCheck ks bs

/-- The same, each segment taken as one block of plain bytes, and no kinds. -/
abbrev wholeOk (code : List (Asm L)) (l : L) (n : Nat) (pg : Prog) (labels : List Label)
    (fuel : Nat) : Bool :=
  wholeOkWith code l n [] (blocksOf code l) pg labels fuel

/-- The memory typing a program started with these arguments starts
under: the blocks it says, and the stack's two. -/
abbrev psiStart (ks : List (Nat × ShapeS)) (bs : List (BitVec 64 × LayoutS))
    (args : List (List Byte)) : MemTy :=
  MemTy.ofList (denBlocks bs ++ argBlocks args) (kindsDen ks)

/-- What the check establishes, for each list of arguments and each world. -/
structure WholeFacts (code : List (Asm L)) (l : L) (n : Nat) (ks : List (Nat × ShapeS))
    (bs : List (BitVec 64 × LayoutS)) (pg : Prog) (labels : List Label) (fuel : Nat)
    (args : List (List Byte)) (w : World) : Prop where
  hcode : ∀ e ∈ pg.code, Asm.fetch (Asm.base code) code e.1 = some (e.2.1, e.2.2)
  wf : (psiStart ks bs args).WF
  /-- The typing the program starts under has the blocks the program says,
  and the stack's besides. -/
  ext : (MemTy.ofList (denBlocks bs) (kindsDen ks)).Ext (psiStart ks bs args)
  nd : (denBlocks bs).Pairwise fun x y => x.1 ≠ y.1
  kindsOk : KindsOk (MemTy.ofList (denBlocks bs) (kindsDen ks)) (kindsOf ks)
  statics : ∀ (fetch : Fetch) (sys : Syscall),
    StaticsOk fetch sys (MemTy.ofList (denBlocks bs) (kindsDen ks)) pg.statics
  check : checkProgram pg labels fuel 0 = true
  entry : (⟨Asm.addr code (Asm.base code) l, entryCtx (stackRoom n)⟩ : Label) ∈ labels
  loaded : Loaded (Asm.fetch (Asm.base code) code) (startIn code l n args w)
  typed : ∀ (fetch : Fetch) (sys : Syscall) (k : Nat),
    (∀ a E, codeJ pg labels fuel a E = true → ∀ (ρ : Env) (fam : Fam), ρ.fn = pg.fns →
      Ok fetch sys (MemTy.ofList (denBlocks bs) (kindsDen ks)) k a
        (E.den { ρ with bound := fam :: ρ.bound })) →
    WellTyped fetch sys (psiStart ks bs args) k
      ((entryCtx (stackRoom n)).den { ({ fn := pg.fns } : Env) with
        bound := startFam (startIn code l n args w) n args :: [] })
      (startIn code l n args w)

theorem wholeOk_facts {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog} {labels : List Label} {fuel : Nat}
    (h : wholeOkWith code l n ks bs pg labels fuel = true) (args : List (List Byte)) (w : World) :
    WholeFacts code l n ks bs pg labels fuel args w := by
  simp only [wholeOkWith, Asm.imageFast_eq, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpc, x, hx, hxa, hxp⟩, hn⟩, hchk⟩, htab⟩, hwfB⟩, hndB⟩, hsegs⟩, hfull⟩, hoff⟩,
    hholds⟩, hhead⟩, hpbelow⟩, hsbelow⟩, hcovB⟩, hstat⟩, hin⟩, hvals⟩, hkc⟩ := h
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hlow := stackLow_le n
  have hperm : (startIn code l n args w).perm
      = ((State.init.loadSegs (Asm.image (Asm.base code) code l)).setPerm (stackStretch n).1
          (stackStretch n).2 .rw).perm := rfl
  have hmemOn : MemOn (Asm.image (Asm.base code) code l) (startIn code l n args w) := by
    intro g hg j hj
    have hb := of_decide_eq_true (List.all_eq_true.mp hsbelow g hg)
    have hpl := pageData_length g
    have hlt : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 j).toNat < argBase.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have e : (startIn code l n args w).mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 j)
        = (Asm.load State.init (Asm.base code) code l).mem
            (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 j) :=
      State.mem_withArgs_below _ n args hlt
    rw [e]
    exact mem_pageData hsegs hg rfl hj
  have hwfBs : (MemTy.ofList (denBlocks bs) (kindsDen ks)).WF :=
    blocksWf_wf hwfB (tags_of_check hkc)
  have hB : ∀ x ∈ denBlocks bs, (startIn code l n args w).canRead x.1 x.2.size = true ∧
      (x.2.writable = true → (startIn code l n args w).canWrite x.1 x.2.size = true) := by
    intro x hx'
    have := List.all_eq_true.mp (blocksPerm_in hsegs hfull hoff hperm hin) x hx'
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    refine ⟨this.1, fun hw => ?_⟩
    rcases this.2 with hn | hcw
    · rw [hw] at hn; cases hn
    · exact hcw
  have hBlow : ∀ x ∈ denBlocks bs, x.1.toNat + x.2.size ≤ stackLow n := by
    intro x hx'
    obtain ⟨g, hg, hb⟩ := List.any_eq_true.mp (List.all_eq_true.mp hin x hx')
    simp only [blockOf, Bool.and_eq_true, decide_eq_true_eq] at hb
    have h2 := hb.1.1.1.2
    have hb' := of_decide_eq_true (List.all_eq_true.mp hsbelow g hg)
    omega
  have hBbelow : ∀ x ∈ denBlocks bs, x.1.toNat + x.2.size ≤ argBase.toNat := fun x hx' => by
    have := hBlow x hx'
    omega
  have hBpos : ∀ x ∈ denBlocks bs, 0 < x.2.size := fun x hx' =>
    hwfBs.nonempty x.1 x.2 (MemTy.ofList_of_mem _ hndB x hx')
  have hcov : ∀ a : BitVec 64, (startIn code l n args w).perm a ≠ .none →
      (stackLow n ≤ a.toNat ∧ a.toNat < argBase.toNat + 0x10000) ∨
        ∃ x ∈ denBlocks bs, (a - x.1).toNat < x.2.size := by
    intro a ha
    have hpw : PermsWithin (startIn code l n args w)
        (stackStretch n :: segStretches (Asm.image (Asm.base code) code l) []) :=
      ((PermsWithin.init.loadSegs _).setPerm (stackStretch n).1 (stackStretch n).2 .rw).congr hperm
    obtain ⟨r, hr, h1, h2⟩ := hpw a ha
    rcases List.mem_cons.mp hr with rfl | hr
    · have e1 : (stackStretch n).1.toNat = 0x7fff0000 - 8 * n := by
        show (argBase - BitVec.ofNat 64 (8 * n)).toNat = _
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hbase]
        omega
      have e2 : (stackStretch n).2.toNat = 8 * n + 0x10000 := by
        show (BitVec.ofNat 64 (8 * n + 0x10000)).toNat = _
        rw [BitVec.toNat_ofNat]
        omega
      rw [e1, e2] at h1 h2
      simp only [State.pagesOf, show 8 * n + 0x10000 ≠ 0 from by omega, ↓reduceIte] at h1 h2
      refine .inl ?_
      unfold stackLow
      omega
    · have := List.all_eq_true.mp hcovB r hr
      simp only [stretchIn, Bool.or_eq_true, beq_iff_eq] at this
      generalize (State.pagesOf r.1.toNat r.2.toNat).1 = p1 at *
      generalize (State.pagesOf r.1.toNat r.2.toNat).2 = p2 at *
      rcases this with h0 | hsw
      · omega
      · obtain ⟨c, hcm, h3, h4⟩ := sweep_cover _ _ _ hsw a.toNat (by omega) (by omega)
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hcm
        exact .inr ⟨y, hy, by bv_omega⟩
  have hnd := nd_args args hndB hBbelow hBpos
  have hΨv : MemTy.ofList (denBlocks bs ++ argBlocks args) (kindsDen ks) (argBase + 8)
      = some (argvLayout args) :=
    MemTy.ofList_of_mem _ hnd (argBase + 8, argvLayout args)
      (List.mem_append_right _ List.mem_cons_self)
  have hext : (MemTy.ofList (denBlocks bs) (kindsDen ks)).Ext
      (MemTy.ofList (denBlocks bs ++ argBlocks args) (kindsDen ks)) :=
    ⟨fun a l' hl => MemTy.ofList_of_mem _ hnd (a, l')
      (List.mem_append_left _ (MemTy.mem_of_ofList hl)), rfl⟩
  have hst := starts_startState (Asm.load State.init (Asm.base code) code l)
    (Asm.addr code (Asm.base code) l) n args w ({ fn := pg.fns } : Env) (kinds := kindsDen ks) hB
    (said_in hsegs hmemOn hin) (text_in hsegs hmemOn hin) hn hBlow hcov
  refine ⟨by rw [hpc]; exact hcode_of_tableOk htab, wf_args args hwfBs hndB hBbelow, hext,
    hndB,
    kindsOk_of_check hkc _,
    fun fetch sys => staticsOk_of_holds (fetch := fetch) (sys := sys) (kinds := kindsDen ks)
      hndB hstat,
    hchk, ?_, Asm.loaded (start_holds hholds hhead hn hpbelow args w), fun fetch sys k hj => ?_⟩
  · obtain ⟨xa, xp⟩ := x
    simp only at hxa hxp
    subst hxa hxp
    exact hx
  refine hst.matches hnd (fun f hf => ?_) (fun y hy q hq => ?_)
  · have e : f = (BitVec.ofNat 64 (stackLow n) + BitVec.ofNat 64 (stackRoom n) + 8,
        Ty.arr (argCount args) (Ty.str 0)) := List.mem_singleton.mp hf
    have hr : BitVec.ofNat 64 (stackLow n) + BitVec.ofNat 64 (stackRoom n) = argBase := by
      have := stackLow_room n
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hbase]
      omega
    rw [e, hr]
    exact argv_known args k hΨv
  · rcases List.mem_append.mp hy with hy | hy
    · exact (heap_of_check hmemOn hndB hvals k hj y hy q hq).ext hext
    · rcases argBlocks_mem args hy with rfl | rfl
      · exact argv_heap _ _ n args w k hΨv q hq
      · cases hq

/-- **A program that checks is safe, on the machine
that decodes its instructions from memory: whatever its arguments, and
whatever the world outside it holds.** -/
theorem whole_safe {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog} {labels : List Label} {fuel : Nat}
    (h : wholeOkWith code l n ks bs pg labels fuel = true) (hpk : pg.kinds = kindsOf ks)
    (hlaws : LawsHold pg.fns pg.laws) :
    ∀ args w, SafeMem linux (startIn code l n args w) := fun args w =>
  have f := wholeOk_facts h args w
  SafeMem.of_safe linux_frame f.loaded
    (safe_of_checked_ext linux_describes rfl (PreSound.all (fun _ => trivial) _) f.hcode
      (hpk ▸ f.kindsOk) (f.statics _ _) f.ext f.wf hlaws f.check f.entry rfl { fn := pg.fns }
      (startFam (startIn code l n args w) n args) rfl fun k H =>
        f.typed _ _ k fun a E hj ρ fam hfn =>
          justifyF_sound linux_describes rfl (PreSound.all (fun _ => trivial) _) pg.index_mem (fun _ _ => labelIx_find)
            f.hcode (hpk ▸ f.kindsOk) (f.statics _ _) hlaws H fuel 0 a E hj ρ fam hfn)

/-- **And where it checks against the wanted status, ends only with it.** -/
theorem whole_exits {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog} {labels : List Label} {fuel : Nat}
    (h : wholeOkWith code l n ks bs pg labels fuel = true)
    {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool} (hq : ∀ c, q c = true → Q c)
    (hpg : pg.pre = preExits q) (hpk : pg.kinds = kindsOf ks) (hlaws : LawsHold pg.fns pg.laws) :
    ∀ args w, SafeMem linux (startIn code l n args w) ∧
      ∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code l n args w) s' →
        ∀ len c, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → Q c := fun args w =>
  have f := wholeOk_facts h args w
  have r := exits_of_checked_ext hq hpg f.hcode (hpk ▸ f.kindsOk) (f.statics _ _) f.ext f.wf
    f.check f.entry rfl { fn := pg.fns } (startFam (startIn code l n args w) n args)
    rfl hlaws fun k H =>
      f.typed _ _ k fun a E hj ρ fam hfn =>
        justifyF_sound (D := exitsDesc Q) (linux_describes.exitsOnly Q) rfl
          (by rw [hpg]; exact preExits_sound hq) pg.index_mem (fun _ _ => labelIx_find) f.hcode (hpk ▸ f.kindsOk)
          (f.statics _ _) hlaws H fuel 0 a E hj ρ fam hfn
  ⟨SafeMem.of_safe linux_frame f.loaded r.1, r.2⟩

/-- **And against the wanted status and the wanted writes: both.** -/
theorem whole_outputs {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog} {labels : List Label} {fuel : Nat}
    (h : wholeOkWith code l n ks bs pg labels fuel = true)
    {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool} (hq : ∀ c, q c = true → Q c)
    {R : BitVec 64 → List (BitVec 8) → Prop} {r : BitVec 64 → List (BitVec 8) → Bool}
    (hr : ∀ fd bs, r fd bs = true → R fd bs) {said : List (BitVec 64 × List (BitVec 8))}
    (hsaid : saidCheck (denBlocks bs) said = true) (hpg : pg.pre = preOut said q r)
    (hpk : pg.kinds = kindsOf ks) (hlaws : LawsHold pg.fns pg.laws) :
    ∀ args w, SafeMem linux (startIn code l n args w) ∧
      (∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code l n args w) s' →
        ∀ len c, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → Q c) ∧
      (∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code l n args w) s' →
        ∀ len, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        s'.getReg .rax = 1 → R (s'.getReg .rdi) s'.offered) := fun args w =>
  have f := wholeOk_facts h args w
  have hso := saidOk_of_check (kinds := kindsDen ks) f.nd hsaid
  have o := outputs_of_checked hq hr hso hpg f.hcode (hpk ▸ f.kindsOk) (f.statics _ _) f.ext f.wf
    f.check f.entry rfl { fn := pg.fns } (startFam (startIn code l n args w) n args) rfl hlaws
    fun k H =>
      f.typed _ _ k fun a E hj ρ fam hfn =>
        justifyF_sound (D := outDesc Q R) ((linux_describes.exitsOnly Q).writesOnly R) rfl
          (by rw [hpg]; exact preOut_sound hq hr hso) pg.index_mem (fun _ _ => labelIx_find) f.hcode (hpk ▸ f.kindsOk)
          (f.statics _ _) hlaws H fuel 0 a E hj ρ fam hfn
  ⟨SafeMem.of_safe linux_frame f.loaded o.1, o.2.1, o.2.2⟩

end TypedAsm.U
