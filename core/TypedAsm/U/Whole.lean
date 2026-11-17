import TypedAsm.U.Blocks
import TypedAsm.U.LayoutS
import TypedAsm.Linux

/-!
# A whole program, checked

One check for a program as written: that its labels' code is typed, and
that the state it is loaded into starts as its entry label asks. And one
statement of what the check shows. A program is its lines, the label it
starts at, and how many slots of stack it is given; the state it starts in
is the one the kernel makes of it.
-/

namespace TypedAsm.U

open TypedAsm

deriving instance DecidableEq for CtxS

variable {L : Type} [DecidableEq L]

/-- The stretch below the stack pointer given to a stack of so many slots. -/
def stackStretch (n : Nat) : BitVec 64 × BitVec 64 :=
  (0x80000000 - BitVec.ofNat 64 (8 * n), BitVec.ofNat 64 (8 * n))

/-- Where the pages of that stretch start, and how many bytes they are. -/
def stackBase (n : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (4096 * (State.pagesOf (stackStretch n).1.toNat (stackStretch n).2.toNat).1)

def stackSize (n : Nat) : Nat :=
  4096 * (State.pagesOf (stackStretch n).1.toNat (stackStretch n).2.toNat).2

/-- **The state a program starts in**: its segments placed as the kernel
places them, the stack's pages given, the stack pointer at their end, and
the instruction pointer at the label it starts at. -/
def startOf (code : List (Asm L)) (l : L) (n : Nat) : State :=
  { ((Asm.load State.init (Asm.base code) code l).setPerm (stackStretch n).1 (stackStretch n).2
        .rw).setReg .rsp 0x80000000 with
    rip := Asm.addr code (Asm.base code) l }

/-- The same, in any outside world: whatever there is for the program to
read. Nothing the check looks at is of the world. -/
def startIn (code : List (Asm L)) (l : L) (n : Nat) (w : World) : State :=
  { startOf code l n with world := w }

/-- The context a program with so many slots of stack starts in. -/
def entryOf (n : Nat) : CtxS := if n = 0 then entryPat else entryPatStack (stackSize n)

/-- The member of the entry's family the starting state is. -/
def entryFam (code : List (Asm L)) (l : L) (n : Nat) : Fam :=
  if n = 0 then Fam.ofState (startOf code l n) else Fam.ofStack (startOf code l n) (stackBase n)

/-- The blocks of a program's first memory typing: each segment, as the
block of its pages. -/
def blocksOf (code : List (Asm L)) (l : L) : List (BitVec 64 × LayoutS) :=
  (Asm.image (Asm.base code) code l).map fun g =>
    (BitVec.ofNat 64 g.1,
      { shape := .mk (pageBytes g.2.2.length) .nil
        writable := g.2.1.writable
        said := if g.2.1.writable then none else some (pageData g) })

/-- **Whether a program as written is typed and starts as its entry asks.**
The checker's program is the assembled table; the entry label is among the
labels, with the entry context; the labels' code is typed; and the state
the program is loaded into is seen, by where its segments and its stack
are, to start as the entry asks, under the blocks the program says its
segments are; and those blocks, and what the program says of its static
data, are seen in its segments; its kinds mention nothing, and each block
said to be of one has its shape. -/
def wholeOkWith (code : List (Asm L)) (l : L) (n : Nat) (ks : List (Nat × ShapeS))
    (bs : List (BitVec 64 × LayoutS)) (pg : Prog) (labels : List Label) (fuel : Nat) : Bool :=
  let base := Asm.base code
  let segs := Asm.image base code l
  let blocks := denBlocks bs
  let st := stackStretch n
  decide (pg.code = progCode (Asm.table base code)) &&
  labels.any (fun x => decide (x.addr = Asm.addr code base l) && decide (x.pat = entryOf n)) &&
  checkProgram pg labels fuel 0 && tableOk (Asm.table base code) && blocksWf blocks &&
  decide (blocks.Pairwise fun x y => x.1 ≠ y.1) && segsOk segs && segsFull segs &&
  segs.all (offStack st.1.toNat st.2.toNat) &&
  Loaded.holdsAllE (Asm.imageExt base code) (Asm.partsExt base code) && Asm.headOkE base code &&
  (Asm.partsExt base code).all (Loaded.offPagesE st.1.toNat st.2.toNat) &&
  (if n = 0 then
    (st :: segStretches segs []).all (stretchIn (blocks.map fun x => (x.1, x.2.size)))
   else
    decide ((stackBase n).toNat = 4096 * (State.pagesOf st.1.toNat st.2.toNat).1) &&
    decide ((stackBase n).toNat + stackSize n ≤ addrTop) &&
    decide ((0x80000000 : BitVec 64) = stackBase n + BitVec.ofNat 64 (stackSize n)) &&
    (blocks.all fun x => decide (Disjoint (stackBase n) (stackSize n) x.1 x.2.size)) &&
    (st :: segStretches segs []).all
      (stretchIn ((stackBase n, stackSize n) :: blocks.map fun x => (x.1, x.2.size)))) &&
  pg.statics.all (staticOk blocks) && blocksIn segs blocks &&
  (blocks.all fun x => x.2.shape.vals.isEmpty) && kindsCheck ks bs

/-- The same, each segment taken as one block of plain bytes, and no kinds. -/
abbrev wholeOk (code : List (Asm L)) (l : L) (n : Nat) (pg : Prog) (labels : List Label)
    (fuel : Nat) : Bool :=
  wholeOkWith code l n [] (blocksOf code l) pg labels fuel

/-- What the check establishes, of the machine that looks instructions up
in the program and of the state the program starts in. -/
structure WholeFacts (code : List (Asm L)) (l : L) (n : Nat) (ks : List (Nat × ShapeS))
    (bs : List (BitVec 64 × LayoutS)) (pg : Prog) (labels : List Label) (fuel : Nat) : Prop where
  hcode : ∀ e ∈ pg.code, Asm.fetch (Asm.base code) code e.1 = some (e.2.1, e.2.2)
  wf : (MemTy.ofList (denBlocks bs) (kindsDen ks)).WF
  nd : (denBlocks bs).Pairwise fun x y => x.1 ≠ y.1
  plain : ∀ x ∈ denBlocks bs, x.2.shape.vals = []
  kindsOk : KindsOk (MemTy.ofList (denBlocks bs) (kindsDen ks)) (kindsOf ks)
  check : checkProgram pg labels fuel 0 = true
  entry : (⟨Asm.addr code (Asm.base code) l, entryOf n⟩ : Label) ∈ labels
  statics : ∀ (fetch : Fetch) (sys : Syscall),
    StaticsOk fetch sys (MemTy.ofList (denBlocks bs) (kindsDen ks)) pg.statics
  loaded : ∀ w, Loaded (Asm.fetch (Asm.base code) code) (startIn code l n w)
  starts : ∀ (w : World) (ρ : Env), Starts (denBlocks bs) (kindsDen ks)
    ((entryOf n).den { ρ with bound := entryFam code l n :: ρ.bound }) (startIn code l n w)

theorem wholeOk_facts {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog} {labels : List Label}
    {fuel : Nat} (h : wholeOkWith code l n ks bs pg labels fuel = true) :
    WholeFacts code l n ks bs pg labels fuel := by
  simp only [wholeOkWith, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpc, x, hx, hxa, hxp⟩, hchk⟩, htab⟩, hwf⟩, hnd⟩, hsegs⟩, hfull⟩, hoff⟩,
    hholds⟩, hhead⟩, hoffp⟩, hlast⟩, hstat⟩, hin⟩, hplain⟩, hkc⟩ := h
  have hparts : ∀ w, ∀ g ∈ Asm.parts (Asm.base code) code, (startIn code l n w).Holds g :=
    fun w g hg =>
      (Asm.prepared_holds State.init (Asm.base code) code l (stackStretch n).1 (stackStretch n).2
        0x80000000 hholds hhead hoffp g hg).congr rfl rfl
  refine ⟨?_, blocksWf_wf hwf (tags_of_check hkc), hnd,
    fun x hx => List.isEmpty_iff.mp (List.all_eq_true.mp hplain x hx),
    kindsOk_of_check hkc _, hchk, ?_,
    fun _ _ => staticsOk_of_check hnd hstat,
    fun w => Asm.loaded (hparts w), fun w ρ => ?_⟩
  · rw [hpc]
    exact hcode_of_tableOk htab
  · obtain ⟨xa, xp⟩ := x
    simp only at hxa hxp
    subst hxa hxp
    exact hx
  · by_cases hn : n = 0
    · subst hn
      simp only [↓reduceIte] at hlast
      exact loaded_starts (t := startIn code l 0 w) hsegs hfull hoff rfl rfl hin ρ hlast
    · simp only [hn, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hlast
      obtain ⟨⟨⟨⟨hb, htop⟩, hrsp⟩, hapart⟩, hc⟩ := hlast
      have e1 : entryOf n = entryPatStack (stackSize n) := by simp only [entryOf, hn, ↓reduceIte]
      have e2 : entryFam code l n = Fam.ofStack (startOf code l n) (stackBase n) := by
        simp only [entryFam, hn, ↓reduceIte]
      rw [e1, e2]
      have hsp : (startIn code l n w).getReg .rsp = (0x80000000 : BitVec 64) :=
        State.getReg_setReg_same
          ((Asm.load State.init (Asm.base code) code l).setPerm (stackStretch n).1
            (stackStretch n).2 .rw) .rsp 0x80000000
      exact loaded_starts_stack (t := startIn code l n w) hsegs hfull hoff rfl rfl hin ρ hb rfl
        htop (hsp.trans hrsp) hapart hc

/-- A state that starts as the entry asks matches it, at every step count:
the entry knows nothing of any value, and the blocks are of plain bytes. -/
theorem WholeFacts.wellTyped {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog}
    {labels : List Label} {fuel : Nat} (f : WholeFacts code l n ks bs pg labels fuel)
    (fetch : Fetch) (sys : Syscall) (w : World) (k : Nat) :
    WellTyped fetch sys (MemTy.ofList (denBlocks bs) (kindsDen ks)) k
      ((entryOf n).den { ({} : Env) with bound := entryFam code l n :: [] }) (startIn code l n w) :=
  (f.starts w {}).matches f.nd
    (fun g hg => by
      have hk : ((entryOf n).den { ({} : Env) with bound := entryFam code l n :: [] }).known = [] := by
        unfold entryOf
        split <;> rfl
      rw [hk] at hg
      cases hg)
    (fun x hx p hp => by
      rw [f.plain x hx] at hp
      cases hp)

/-- **A program that checks is safe, on the machine that decodes its
instructions from memory.** -/
theorem whole_safe {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog} {labels : List Label}
    {fuel : Nat} (h : wholeOkWith code l n ks bs pg labels fuel = true)
    (hpk : pg.kinds = kindsOf ks) :
    ∀ w, SafeMem linux (startIn code l n w) := fun w =>
  have f := wholeOk_facts h
  SafeMem.of_safe linux_frame (f.loaded w)
    (safe_of_checked linux_describes rfl (PreSound.all (fun _ => trivial) _) f.hcode (hpk ▸ f.kindsOk)
      (f.statics _ _) f.wf f.check f.entry rfl {} (entryFam code l n) (f.wellTyped _ _ w))

/-- **And where it checks against the wanted status, ends only with it.** -/
theorem whole_exits {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog} {labels : List Label}
    {fuel : Nat} (h : wholeOkWith code l n ks bs pg labels fuel = true)
    {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool} (hq : ∀ c, q c = true → Q c)
    (hpg : pg.pre = preExits q) (hpk : pg.kinds = kindsOf ks) :
    ∀ w, SafeMem linux (startIn code l n w) ∧
      ∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code l n w) s' →
        ∀ len c, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → Q c := fun w =>
  have f := wholeOk_facts h
  have r := exits_of_checked hq hpg f.hcode (hpk ▸ f.kindsOk) (f.statics _ _) f.wf f.check f.entry
    rfl {} (entryFam code l n) (f.wellTyped _ _ w)
  ⟨SafeMem.of_safe linux_frame (f.loaded w) r.1, r.2⟩

/-- **And against the wanted status and the wanted writes: both.** -/
theorem whole_outputs {code : List (Asm L)} {l : L} {n : Nat} {ks : List (Nat × ShapeS)}
    {bs : List (BitVec 64 × LayoutS)} {pg : Prog} {labels : List Label}
    {fuel : Nat} (h : wholeOkWith code l n ks bs pg labels fuel = true)
    {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool} (hq : ∀ c, q c = true → Q c)
    {R : BitVec 64 → List (BitVec 8) → Prop} {r : BitVec 64 → List (BitVec 8) → Bool}
    (hr : ∀ fd bs, r fd bs = true → R fd bs) {said : List (BitVec 64 × List (BitVec 8))}
    (hsaid : saidCheck (denBlocks bs) said = true) (hpg : pg.pre = preOut said q r)
    (hpk : pg.kinds = kindsOf ks) :
    ∀ w, SafeMem linux (startIn code l n w) ∧
      (∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code l n w) s' →
        ∀ len c, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → Q c) ∧
      (∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code l n w) s' →
        ∀ len, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        s'.getReg .rax = 1 → R (s'.getReg .rdi) s'.offered) := fun w =>
  have f := wholeOk_facts h
  have o := outputs_of_checked hq hr (saidOk_of_check f.nd hsaid) hpg f.hcode (hpk ▸ f.kindsOk)
    (f.statics _ _) f.wf f.check f.entry rfl {} (entryFam code l n) (f.wellTyped _ _ w)
  ⟨SafeMem.of_safe linux_frame (f.loaded w) o.1, o.2.1, o.2.2⟩

end TypedAsm.U
