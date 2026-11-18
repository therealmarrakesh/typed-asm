import TypedAsm.U.FromAsm

/-!
# A first state, checked

What is asked of the state a program starts in is decided, for a state
given: that its blocks may be read and written as they say, and that the blocks
make sense together.
-/

namespace TypedAsm.U

open TypedAsm

instance (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Decidable (Disjoint a n b m) := by
  unfold Disjoint
  infer_instance

/-- Whether a list of blocks makes sense as a memory typing with no kinds:
each of a size a machine word holds and not nought, its typed values within
it, saying its bytes only if it may not be written and saying
all of them; and no two overlapping or at one address. -/
def blocksWf (blocks : List (BitVec 64 × Layout)) : Bool :=
  (blocks.all fun x =>
    decide (x.2.size < 18446744073709551616) && decide (0 < x.2.size) &&
      (x.2.shape.vals.all fun p => decide (p.1 + 8 ≤ x.2.shape.size)) &&
      (match x.2.said with
       | some bs => !x.2.writable && decide (bs.length = x.2.size)
       | none => true)) &&
  (blocks.all fun x => blocks.all fun y =>
    decide (x.1 = y.1) || decide (Disjoint x.1 x.2.size y.1 y.2.size))

theorem blocksWf_wf {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (h : blocksWf blocks = true)
    (hk : ∀ x ∈ blocks, ∀ t, x.2.tag = some t → kinds t = some x.2.shape) :
    (MemTy.ofList blocks kinds).WF := by
  simp only [blocksWf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a l hl => ?_, fun a b la lb ha hb hab => ?_, fun a l hl => ?_, fun a l hl p hp => ?_,
    fun a l hl tag ht => ?_, fun a l bs hl hs => ?_⟩
  · exact (h1 _ (MemTy.mem_of_ofList hl)).1.1.1
  · rcases h2 _ (MemTy.mem_of_ofList ha) _ (MemTy.mem_of_ofList hb) with he | hd
    · exact absurd he hab
    · exact hd
  · exact (h1 _ (MemTy.mem_of_ofList hl)).1.1.2
  · exact (h1 _ (MemTy.mem_of_ofList hl)).1.2 p hp
  · exact hk _ (MemTy.mem_of_ofList hl) tag ht
  · have := (h1 _ (MemTy.mem_of_ofList hl)).2
    rw [hs] at this
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    exact this

/-- Whether each block may be read, and written if it says so. -/
def blocksPerm (s : State) (blocks : List (BitVec 64 × Layout)) : Bool :=
  blocks.all fun x => s.canRead x.1 x.2.size && (!x.2.writable || s.canWrite x.1 x.2.size)

/-- The values of a family that are a state's registers. -/
def Fam.ofState (s : State) : Fam where
  vals := fun i =>
    match i with
    | 0 => s.getReg .rax | 1 => s.getReg .rcx | 2 => s.getReg .rdx | 3 => s.getReg .rbx
    | 4 => s.getReg .rsp | 5 => s.getReg .rbp | 6 => s.getReg .rsi | 7 => s.getReg .rdi
    | 8 => s.getReg .r8 | 9 => s.getReg .r9 | 10 => s.getReg .r10 | 11 => s.getReg .r11
    | 12 => s.getReg .r12 | 13 => s.getReg .r13 | 14 => s.getReg .r14 | 15 => s.getReg .r15
    | _ => 0
  flags := s.flags
  rest := []

end TypedAsm.U
