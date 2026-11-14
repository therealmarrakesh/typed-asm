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

/-- The memory typing with a block at each listed address. -/
def MemTy.ofList (bs : List (BitVec 64 × Layout)) : MemTy :=
  fun a => (bs.find? (·.1 = a)).map (·.2)

theorem MemTy.mem_of_ofList {bs : List (BitVec 64 × Layout)} {a : BitVec 64} {l : Layout}
    (h : MemTy.ofList bs a = some l) : (a, l) ∈ bs := by
  simp only [MemTy.ofList, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hx
  have ha := List.find?_some hx
  simp only [decide_eq_true_eq] at ha
  subst ha
  exact hmem

/-- Whether the blocks fit in the address space and no two with different
addresses overlap. -/
def MemTy.check (bs : List (BitVec 64 × Layout)) : Bool :=
  bs.all (fun x => decide (x.2.size < 2 ^ 64)) &&
  bs.all (fun x => bs.all (fun y =>
    decide (x.1 = y.1) || decide (Disjoint x.1 x.2.size y.1 y.2.size)))

theorem MemTy.wf_of_check {bs : List (BitVec 64 × Layout)} (h : MemTy.check bs = true) :
    (MemTy.ofList bs).WF := by
  simp only [MemTy.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at h
  constructor
  · intro a l hl
    exact h.1 _ (MemTy.mem_of_ofList hl)
  · intro a b la lb ha hb hne
    exact (h.2 _ (MemTy.mem_of_ofList ha) _ (MemTy.mem_of_ofList hb)).resolve_left hne

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
    Matches H (MemTy.ofList bs) Γ s := by
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
