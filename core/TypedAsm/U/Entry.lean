import TypedAsm.U.Safe

/-!
# Where a program starts

What is asked of the state a program starts in, to match the context its
entry label wants. It is said in two parts. One is of the state alone: its
registers and flags, the blocks of memory the program's data and code are
in, the regions it holds, and that these are all the memory there is; this
is what the loader is to be shown to give. The other is of types: that
what the context knows is so, and that each block holds what its shape
says; this is settled from the program.

All the memory there is: a byte the machine can touch is in a region held
or in a block. So the pages a program's instructions are in are blocks too,
that may be read and not written.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

/-- The memory typing whose blocks are those of a list, each at its
address, with the given kinds. -/
def MemTy.ofList (blocks : List (BitVec 64 × Layout)) (kinds : Nat → Option Shape) : MemTy :=
  ⟨fun a => (blocks.find? fun x => x.1 = a).map (·.2), kinds⟩

theorem MemTy.mem_of_ofList {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    {a : BitVec 64} {l : Layout} (h : (MemTy.ofList blocks kinds) a = some l) : (a, l) ∈ blocks := by
  have h' : (blocks.find? fun x => x.1 = a).map (·.2) = some l := h
  cases hf : blocks.find? fun x => x.1 = a with
  | none => rw [hf] at h'; cases h'
  | some x =>
    rw [hf] at h'
    cases h'
    have hx := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [decide_eq_true_eq] at hx
    rw [← hx]
    exact hm

/-- Where no two blocks of a list are at one address, each is the block of
the memory typing at its address. -/
theorem MemTy.ofList_of_mem {kinds : Nat → Option Shape} :
    (blocks : List (BitVec 64 × Layout)) → blocks.Pairwise (fun x y => x.1 ≠ y.1) →
    ∀ x ∈ blocks, (MemTy.ofList blocks kinds) x.1 = some x.2
  | [], _, x, hx => nomatch hx
  | y :: ys, hnd, x, hx => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hnd
    show ((y :: ys).find? fun z => z.1 = x.1).map (·.2) = some x.2
    by_cases hxy : y.1 = x.1
    · rw [List.find?_cons_of_pos (by simpa using hxy)]
      rcases List.mem_cons.mp hx with rfl | hx'
      · rfl
      · exact absurd hxy (hy x hx')
    · rw [List.find?_cons_of_neg (by simpa using hxy)]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact absurd rfl hxy
      · exact MemTy.ofList_of_mem (kinds := kinds) ys hys x hx'

/-- **What is asked of the state a program starts in**, for a context: all
of matching it that is of the state alone. -/
structure Starts (blocks : List (BitVec 64 × Layout)) (kinds : Nat → Option Shape) (Γ : Ctx)
    (s : State) : Prop where
  /-- Each register holds the value the context says, and the flags are its. -/
  val : ∀ r, s.getReg r = Γ.val r
  flags : s.flags = Γ.flags
  /-- Each block may be read, and written if it says so. -/
  perms : ∀ x ∈ blocks,
    s.canRead x.1 x.2.size = true ∧ (x.2.writable = true → s.canWrite x.1 x.2.size = true)
  /-- The text of each block that has some ends in a zero byte. -/
  text : ∀ x ∈ blocks, x.2.text ≠ 0 → s.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0
  /-- A block that says its bytes holds them. -/
  said : ∀ x ∈ blocks, ∀ bs : List (BitVec 8), x.2.said = some bs →
    ∀ k (hk : k < bs.length), s.mem (x.1 + BitVec.ofNat 64 k) = bs[k]
  /-- The regions held are there, apart from each other and from the blocks,
  and hold what the context says. -/
  held : HeldOk (MemTy.ofList blocks kinds) Γ s
  /-- And these are all the memory there is. -/
  complete : ∀ a : BitVec 64, s.perm a ≠ .none →
    (∃ b ∈ Γ.held, (a - b.1).toNat < b.2.size) ∨
    (∃ x ∈ blocks, (a - x.1).toNat < x.2.size)

/-- **A state that starts so matches the context**, where no two blocks are
at one address, what the context knows is so, and each block holds what its
shape says. -/
theorem Starts.matches {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape} {Γ : Ctx}
    {s : State} {H : Ty → BitVec 64 → Prop} (h : Starts blocks kinds Γ s)
    (hnd : blocks.Pairwise fun x y => x.1 ≠ y.1)
    (hknown : ∀ f ∈ Γ.known, H f.2 f.1)
    (hheap : ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals, H p.2 (s.load64 (x.1 + BitVec.ofNat 64 p.1)))
    (hrows : Γ.rows = []) :
    Matches H (MemTy.ofList blocks kinds) Γ s where
  val := h.val
  known := hknown
  flags := h.flags
  heapPerm := fun a l hl => h.perms (a, l) (MemTy.mem_of_ofList hl)
  heap := fun a l hl p hp => hheap (a, l) (MemTy.mem_of_ofList hl) p hp
  text := fun a l hl => h.text (a, l) (MemTy.mem_of_ofList hl)
  said := fun a l bs hl => h.said (a, l) (MemTy.mem_of_ofList hl) bs
  held := h.held
  rows := fun r hr => by rw [hrows] at hr; cases hr
  fed := fun r hr => by rw [hrows] at hr; cases hr
  complete := fun a ha =>
    (h.complete a ha).imp id fun ⟨x, hx, hlt⟩ =>
      ⟨x.1, x.2, MemTy.ofList_of_mem blocks hnd x hx, hlt⟩

/-- **A checked program started so is safe**: at one of its labels, in a
state that starts as a member of the label's family asks, under the memory
typing of its blocks. -/
theorem Starts.safe {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {pg : Prog} {labels : List Label} {fuel k : Nat}
    {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (hpre : PreSound fetch sys (MemTy.ofList blocks kinds) D pg.pre)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2))
    (hk : KindsOk (MemTy.ofList blocks kinds) pg.kinds)
    (hst : StaticsOk fetch sys (MemTy.ofList blocks kinds) pg.statics)
    (hwf : (MemTy.ofList blocks kinds).WF)
    (h : checkProgram pg labels fuel k = true)
    {l : Label} (hl : l ∈ labels) {s : State} (hrip : s.rip = l.addr) (ρ : Env) (fam : Fam)
    (hfn : ρ.fn = pg.fns) (hlaws : LawsHold pg.fns pg.laws)
    (hs : Starts blocks kinds (l.pat.den { ρ with bound := fam :: ρ.bound }) s)
    (hnd : blocks.Pairwise fun x y => x.1 ≠ y.1)
    (hknown : ∀ n, ∀ f ∈ (l.pat.den { ρ with bound := fam :: ρ.bound }).known,
      HasTy fetch sys (MemTy.ofList blocks kinds) n f.2 f.1)
    (hheap : ∀ n, ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy fetch sys (MemTy.ofList blocks kinds) n p.2 (s.load64 (x.1 + BitVec.ofNat 64 p.1)))
    (hrows : l.pat.rows = []) :
    Safe fetch sys s :=
  safe_of_checked hD hkind hpre hcode hk hst hwf hlaws h hl hrip ρ fam hfn fun n _ =>
    hs.matches hnd (hknown n) (hheap n) (by show l.pat.rows.map _ = []; rw [hrows]; rfl)

end TypedAsm.U
