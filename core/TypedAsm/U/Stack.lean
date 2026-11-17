import TypedAsm.U.Pages

/-!
# A first state with a stack

The context a program with a stack starts in: every register but the stack
pointer and the flags whatever they are; the stack's pages held as one
region, the stack pointer at its end; nothing else held.
-/

namespace TypedAsm.U

open TypedAsm

/-- The context a program with a stack of so many bytes starts in, as a
family: the stack's region at an address the family ranges over, the stack
pointer at its end. -/
def entryPatStack (size : Nat) : CtxS where
  regs := ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3,
    .add (.bvar 0 16) (.lit (BitVec.ofNat 64 size)), .bvar 0 5, .bvar 0 6, .bvar 0 7,
    .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13, .bvar 0 14, .bvar 0 15⟩
  flags := .bvar 0
  held := [(.bvar 0 16, ⟨size, []⟩)]
  known := []
  rest := .none

/-- The member of that family a state is, its stack's region at `base`. -/
def Fam.ofStack (s : State) (base : BitVec 64) : Fam where
  vals := fun i => if i = 16 then base else (Fam.ofState s).vals i
  flags := s.flags
  rest := []

/-- **A state checked so starts as the entry context with a stack asks**:
the stack's region may be written, the stack pointer is at its end, it is
apart from every block, and every byte the state can touch is on a page of
a stretch within the region or a block. -/
theorem starts_stack {s : State} {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (ρ : Env) {base : BitVec 64} {size : Nat}
    (hb : blocksPerm s blocks = true)
    (hsaid : ∀ x ∈ blocks, ∀ bs : List (BitVec 8), x.2.said = some bs →
      ∀ k (hk : k < bs.length), s.mem (x.1 + BitVec.ofNat 64 k) = bs[k])
    (htext : ∀ x ∈ blocks, x.2.text ≠ 0 → s.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0)
    (hw : s.canWrite base size = true) (hsz : size < 18446744073709551616)
    (hrsp : s.getReg .rsp = base + BitVec.ofNat 64 size)
    (hapart : (blocks.all fun x => decide (Disjoint base size x.1 x.2.size)) = true)
    {rs : List (BitVec 64 × BitVec 64)} (hp : PermsWithin s rs)
    (hc : rs.all (stretchIn ((base, size) :: blocks.map fun x => (x.1, x.2.size))) = true) :
    Starts blocks kinds
      ((entryPatStack size).den { ρ with bound := Fam.ofStack s base :: ρ.bound }) s where
  val := fun r => by
    cases r <;> first | rfl | exact hrsp
  flags := rfl
  perms := fun x hx => by
    have := List.all_eq_true.mp hb x hx
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    refine ⟨this.1, fun hw => ?_⟩
    rcases this.2 with hn | hcw
    · rw [hw] at hn; cases hn
    · exact hcw
  text := htext
  said := hsaid
  held := by
    have hheld : ((entryPatStack size).den { ρ with bound := Fam.ofStack s base :: ρ.bound }).held
        = [(base, ⟨size, []⟩)] := rfl
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb p hp => ?_, fun b hb p hp => ?_,
      fun b hb a l hl => ?_, ?_⟩
    · rw [hheld] at hb; cases List.mem_singleton.mp hb; exact hw
    · rw [hheld] at hb; cases List.mem_singleton.mp hb; exact hsz
    · rw [hheld] at hb; cases List.mem_singleton.mp hb; cases hp
    · rw [hheld] at hb; cases List.mem_singleton.mp hb; cases hp
    · rw [hheld] at hb
      cases List.mem_singleton.mp hb
      have := List.all_eq_true.mp hapart (a, l) (MemTy.mem_of_ofList hl)
      exact of_decide_eq_true this
    · rw [hheld]; exact List.pairwise_singleton _ _
  complete := fun a ha =>
    hp.complete (Γ := (entryPatStack size).den { ρ with bound := Fam.ofStack s base :: ρ.bound })
      (blocks := blocks) hc a ha

end TypedAsm.U
