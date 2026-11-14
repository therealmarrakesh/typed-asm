import TypedAsm.Types

/-!
# Memory typings from a list of blocks

A memory typing given as a list of blocks, with the checks that can be
decided by computation packaged so that a concrete starting state needs a
proof only for the parts that cannot: what the registers, stack slots and
fields hold.
-/

namespace TypedAsm

instance (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Decidable (Disjoint a n b m) := by
  unfold Disjoint
  infer_instance

/-- The memory typing with a block at each listed address, and the listed
kinds of block. A kind is a number and the fields its blocks have. -/
def MemTy.ofList (bs : List (BitVec 64 × Layout)) (kinds : List (Nat × List Ty)) : MemTy :=
  ⟨fun a => (bs.find? (·.1 = a)).map (·.2), fun tag => kinds.lookup tag⟩

variable {kinds : List (Nat × List Ty)}

theorem MemTy.mem_of_ofList {bs : List (BitVec 64 × Layout)} {a : BitVec 64} {l : Layout}
    (h : MemTy.ofList bs kinds a = some l) : (a, l) ∈ bs := by
  simp only [MemTy.ofList, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hx
  have ha := List.find?_some hx
  simp only [decide_eq_true_eq] at ha
  subst ha
  exact hmem

/-- Whether the blocks fit in the address space, none is empty, and no two
with different addresses overlap. -/
def MemTy.check (bs : List (BitVec 64 × Layout)) : Bool :=
  bs.all (fun x => decide (x.2.size < 2 ^ 64) && !x.2.fields.isEmpty) &&
  bs.all (fun x => bs.all (fun y =>
    decide (x.1 = y.1) || decide (Disjoint x.1 x.2.size y.1 y.2.size)))

/-- What the listed kinds say the fields of each block of a kind are. -/
def MemTy.declared (kinds : List (Nat × List Ty)) (bs : List (BitVec 64 × Layout)) :
    List (Option (List Ty)) :=
  bs.filterMap (fun x => x.2.tag.map (fun tag => kinds.lookup tag))

/-- The fields each block of a kind actually has. -/
def MemTy.actual (bs : List (BitVec 64 × Layout)) : List (Option (List Ty)) :=
  bs.filterMap (fun x => x.2.tag.map (fun _ => some x.2.fields))

theorem MemTy.kinds_of_eq : ∀ {bs : List (BitVec 64 × Layout)},
    MemTy.declared kinds bs = MemTy.actual bs →
    ∀ x ∈ bs, ∀ tag, x.2.tag = some tag → kinds.lookup tag = some x.2.fields := by
  intro bs
  induction bs with
  | nil => intro _ x hx; cases hx
  | cons y ys ih =>
    intro h x hx tag ht
    simp only [MemTy.declared, MemTy.actual, List.filterMap_cons] at h
    cases hy : y.2.tag with
    | none =>
      rw [hy] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hy] at ht; cases ht
      · exact ih h x hx' tag ht
    | some u =>
      rw [hy] at h
      simp only [Option.map_some, List.cons.injEq] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hy] at ht; cases ht; exact h.1
      · exact ih h.2 x hx' tag ht

/-- A list of blocks that passes the check is a well-formed memory typing,
provided each block of a kind has the fields listed for that kind. For
concrete lists that is true by computation, and is proved without being asked. -/
theorem MemTy.wf_of_check {bs : List (BitVec 64 × Layout)} (h : MemTy.check bs = true)
    (hk : MemTy.declared kinds bs = MemTy.actual bs := by rfl) :
    (MemTy.ofList bs kinds).WF := by
  simp only [MemTy.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  constructor
  · intro a l hl
    exact (h.1 _ (MemTy.mem_of_ofList hl)).1
  · intro a b la lb ha hb hne
    exact (h.2 _ (MemTy.mem_of_ofList ha) _ (MemTy.mem_of_ofList hb)).resolve_left hne
  · intro a l hl
    exact (h.1 _ (MemTy.mem_of_ofList hl)).2
  · intro a l hl tag ht
    exact MemTy.kinds_of_eq hk _ (MemTy.mem_of_ofList hl) tag ht

/-- The parts of "the state matches the context" that are decided by
computation: permissions, sizes, and that no block overlaps the stack. -/
def stateCheck (bs : List (BitVec 64 × Layout)) (Γ : Ctx) (s : State) : Bool :=
  s.canWrite (stackBase Γ s) (stackSize Γ) && decide (stackSize Γ < 2 ^ 64) &&
  bs.all (fun x =>
    s.canRead x.1 x.2.size && (!x.2.writable || s.canWrite x.1 x.2.size) &&
    decide (Disjoint (stackBase Γ s) (stackSize Γ) x.1 x.2.size))

/-- A state matches a context if the computed checks pass and the registers,
flags, stack slots and block fields hold what the context says. -/
theorem Matches.ofCheck {H : Ty → BitVec 64 → Prop} {bs : List (BitVec 64 × Layout)} {Γ : Ctx}
    {s : State} (hc : stateCheck bs Γ s = true)
    (hregs : ∀ r, r ≠ .rsp → H (Γ.regs r) (s.getReg r)) (hflags : Γ.flags s.flags)
    (hstack : ∀ i τ, Γ.stack[i]? = some τ →
      H τ (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i))))
    (hheap : ∀ x ∈ bs, ∀ i τ, x.2.fields[i]? = some τ →
      H τ (s.load64 (x.1 + BitVec.ofNat 64 (8 * i))))
    (hrsp : H (Γ.regs .rsp) (s.getReg .rsp)) :
    Matches H (MemTy.ofList bs kinds) Γ s := by
  simp only [stateCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨hsp, hsz⟩, hb⟩ := hc
  exact {
    regs := hregs
    flags := hflags
    stackPerm := hsp
    stackSize_lt := hsz
    stack := hstack
    heapPerm := fun a l hl => by
      obtain ⟨⟨hr, hw⟩, -⟩ := hb _ (MemTy.mem_of_ofList hl)
      refine ⟨hr, fun hwr => ?_⟩
      rcases hw with hw | hw
      · rw [hw] at hwr; cases hwr
      · exact hw
    heap := fun a l hl => hheap _ (MemTy.mem_of_ofList hl)
    stackHeap := fun a l hl => (hb _ (MemTy.mem_of_ofList hl)).2
    sp := hrsp }

end TypedAsm
