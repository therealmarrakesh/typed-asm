import TypedAsm.U.FromAsm

/-!
# A first state, checked

What is asked of the state a program starts in is decided, for a state
given: that its blocks may be read and written as they say, and that the blocks
make sense together. And
the context a program with no stack starts in: every register and the
flags as they are, nothing held.
-/

namespace TypedAsm.U

open TypedAsm

instance (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Decidable (Disjoint a n b m) := by
  unfold Disjoint
  infer_instance

/-- Whether a list of blocks makes sense as a memory typing with no kinds:
each of a size a machine word holds and not nought, its typed values within
it, of no kind, saying its bytes only if it may not be written and saying
all of them; and no two overlapping or at one address. -/
def blocksWf (blocks : List (BitVec 64 × Layout)) : Bool :=
  (blocks.all fun x =>
    decide (x.2.size < 18446744073709551616) && decide (0 < x.2.size) &&
      (x.2.shape.vals.all fun p => decide (p.1 + 8 ≤ x.2.shape.size)) && x.2.tag.isNone &&
      (match x.2.said with
       | some bs => !x.2.writable && decide (bs.length = x.2.size)
       | none => true)) &&
  (blocks.all fun x => blocks.all fun y =>
    decide (x.1 = y.1) || decide (Disjoint x.1 x.2.size y.1 y.2.size))

theorem blocksWf_wf {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (h : blocksWf blocks = true) : (MemTy.ofList blocks kinds).WF := by
  simp only [blocksWf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a l hl => ?_, fun a b la lb ha hb hab => ?_, fun a l hl => ?_, fun a l hl p hp => ?_,
    fun a l hl tag ht => ?_, fun a l bs hl hs => ?_⟩
  · exact (h1 _ (MemTy.mem_of_ofList hl)).1.1.1.1
  · rcases h2 _ (MemTy.mem_of_ofList ha) _ (MemTy.mem_of_ofList hb) with he | hd
    · exact absurd he hab
    · exact hd
  · exact (h1 _ (MemTy.mem_of_ofList hl)).1.1.1.2
  · exact (h1 _ (MemTy.mem_of_ofList hl)).1.1.2 p hp
  · have := (h1 _ (MemTy.mem_of_ofList hl)).1.2
    rw [ht] at this
    cases this
  · have := (h1 _ (MemTy.mem_of_ofList hl)).2
    rw [hs] at this
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    exact this

/-- A context that holds nothing asks nothing of what is held. -/
theorem HeldOk.nil {Ψ : MemTy} {Γ : Ctx} {s : State} (h : Γ.held = []) : HeldOk Ψ Γ s := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, ?_⟩
  all_goals first
    | (rw [h] at hb; cases hb)
    | (rw [h]; exact List.Pairwise.nil)

/-- Whether each block may be read, and written if it says so. -/
def blocksPerm (s : State) (blocks : List (BitVec 64 × Layout)) : Bool :=
  blocks.all fun x => s.canRead x.1 x.2.size && (!x.2.writable || s.canWrite x.1 x.2.size)

/-- The context a program with no stack starts in, as a family: every
register and the flags whatever they are, nothing held. -/
def entryPat : CtxS where
  regs := ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3, .bvar 0 4, .bvar 0 5, .bvar 0 6, .bvar 0 7,
    .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13, .bvar 0 14, .bvar 0 15⟩
  flags := .bvar 0
  held := []
  known := []
  rest := .none

/-- The member of that family a state is. -/
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

/-- **A state checked so starts as the entry context asks**, where each block
that says its bytes holds them, every
byte it can touch is on a page of a stretch that lies within a block, and
no block has a text of its own. -/
theorem starts_entry {s : State} {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (ρ : Env) (hb : blocksPerm s blocks = true)
    (hsaid : ∀ x ∈ blocks, ∀ bs : List (BitVec 8), x.2.said = some bs →
      ∀ k (hk : k < bs.length), s.mem (x.1 + BitVec.ofNat 64 k) = bs[k])
    (htext : ∀ x ∈ blocks, x.2.text = 0)
    {rs : List (BitVec 64 × BitVec 64)} (hp : PermsWithin s rs)
    (hc : rs.all (stretchIn (blocks.map fun x => (x.1, x.2.size))) = true) :
    Starts blocks kinds (entryPat.den { ρ with bound := Fam.ofState s :: ρ.bound }) s where
  val := fun r => by cases r <;> rfl
  flags := rfl
  perms := fun x hx => by
    have := List.all_eq_true.mp hb x hx
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    refine ⟨this.1, fun hw => ?_⟩
    rcases this.2 with hn | hcw
    · rw [hw] at hn; cases hn
    · exact hcw
  text := fun x hx ht => absurd (htext x hx) ht
  said := hsaid
  held := HeldOk.nil rfl
  complete := fun a ha => by
    have := hp.complete (Γ := entryPat.den { ρ with bound := Fam.ofState s :: ρ.bound })
      (blocks := blocks) (by exact hc) a ha
    exact this

end TypedAsm.U
