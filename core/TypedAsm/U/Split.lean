import TypedAsm.U.Regard
import TypedAsm.Ranges

/-!
# The regions held, seen another way

What a context asks of the regions it holds is asked of each; so it is
still met of fewer of them, and of more where the further one is there and
overlaps nothing. Those are steps on the way: a context must say all that
is held, so the regions may be changed only for others that take in every
byte that was held (`WellTyped.reheld`).

Two regions that lie end to end may be regarded as one: nothing happens to
the machine, it is only how the same bytes are regarded. Taking one region
as several is a case of the one statement of what regard comes to, in
`Entail`.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat} {Γ : Ctx} {s : State}

namespace HeldOk

/-- What is asked of the regions held is met of any of them. -/
theorem sublist {L : List Region} (h : HeldOk Ψ Γ s) (hsub : L.Sublist Γ.held) :
    HeldOk Ψ { Γ with held := L } s :=
  { perm := fun c hc => h.perm c (hsub.subset hc)
    size_lt := fun c hc => h.size_lt c (hsub.subset hc)
    fits := fun c hc => h.fits c (hsub.subset hc)
    vals := fun c hc => h.vals c (hsub.subset hc)
    heap := fun c hc => h.heap c (hsub.subset hc)
    apart := h.apart.sublist hsub }

/-- And of one more, that is writable, holds the values said, and overlaps
nothing held or described by the memory typing. -/
theorem cons {b : Region} (h : HeldOk Ψ Γ s)
    (hperm : s.canWrite b.1 b.2.size = true) (hlt : b.2.size < 2 ^ 64)
    (hfits : ∀ p ∈ b.2.vals, p.1 + 8 ≤ b.2.size)
    (hvals : ∀ p ∈ b.2.vals, s.load64 (b.1 + BitVec.ofNat 64 p.1) = p.2)
    (hheap : ∀ a l, Ψ a = some l → Disjoint b.1 b.2.size a l.size)
    (hapart : ∀ c ∈ Γ.held, Disjoint b.1 b.2.size c.1 c.2.size) :
    HeldOk Ψ { Γ with held := b :: Γ.held } s :=
  { perm := fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hperm
      · exact h.perm c hc
    size_lt := fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hlt
      · exact h.size_lt c hc
    fits := fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hfits
      · exact h.fits c hc
    vals := fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hvals
      · exact h.vals c hc
    heap := fun c hc a l hl => by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hheap a l hl
      · exact h.heap c hc a l hl
    apart := List.pairwise_cons.mpr ⟨hapart, h.apart⟩ }

end HeldOk

/-- **A state that matches a context matches it with other regions held**,
where what is asked of those is met and every byte that was held is in one
of them. Bytes may not be let go: the context says all that is held. -/
theorem WellTyped.reheld (h : WellTyped fetch sys Ψ n Γ s) (L : List Region)
    (hheld : HeldOk Ψ { Γ with held := L } s)
    (hcov : ∀ b ∈ Γ.held, ∀ a : BitVec 64, (a - b.1).toNat < b.2.size →
      ∃ c ∈ L, (a - c.1).toNat < c.2.size) :
    WellTyped fetch sys Ψ n { Γ with held := L } s :=
  { val := h.val
    known := h.known
    flags := h.flags
    heapPerm := h.heapPerm
    heap := h.heap
    text := h.text
    said := h.said
    held := hheld
    complete := fun a ha => by
      rcases h.complete a ha with ⟨b, hb, hlt⟩ | hr
      · exact .inl (hcov b hb a hlt)
      · exact .inr hr }

/-- **Two held regions that lie end to end may be regarded as one**, the
bytes of the first followed by those of the second. They are taken as the
first two the context lists; any two may be put there, the order of what is
held being of no account. -/
theorem Regards.join {Γ : Ctx} {b : BitVec 64} {S₁ S₂ : Held} {rest : List Region}
    (hheld : Γ.held = (b, S₁) :: (b + BitVec.ofNat 64 S₁.size, S₂) :: rest)
    (hsz : S₁.size + S₂.size < 2 ^ 64) :
    Regards fetch sys Ψ Γ { Γ with held := (b, S₁.append S₂) :: rest } := by
  intro j Ψ' he hwf s h
  have hin₁ : (b, S₁) ∈ Γ.held := by rw [hheld]; exact List.mem_cons_self
  have hin₂ : (b + BitVec.ofNat 64 S₁.size, S₂) ∈ Γ.held := by
    rw [hheld]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hap := h.held.apart
  rw [hheld] at hap
  obtain ⟨hap₁, hap'⟩ := List.pairwise_cons.mp hap
  obtain ⟨hap₂, hap₃⟩ := List.pairwise_cons.mp hap'
  have hsub : rest.Sublist Γ.held := by
    rw [hheld]; exact (List.sublist_cons_self _ _).trans (List.sublist_cons_self _ _)
  refine h.reheld _ ((h.held.sublist hsub).cons (b := (b, S₁.append S₂)) ?_ hsz ?_ ?_ ?_ ?_) ?_
  · have p₁ := State.canWrite_iff.mp (h.held.perm _ hin₁)
    have p₂ := State.canWrite_iff.mp (h.held.perm _ hin₂)
    simp only at p₁ p₂
    rw [State.canWrite_iff]
    show ∀ i, i < S₁.size + S₂.size → _
    intro i hi
    by_cases hi₁ : i < S₁.size
    · exact p₁ i hi₁
    · have := p₂ (i - S₁.size) (by omega)
      rwa [show b + BitVec.ofNat 64 S₁.size + BitVec.ofNat 64 (i - S₁.size)
          = b + BitVec.ofNat 64 i by bv_omega] at this
  · intro p hp
    simp only [ShapeOf.append, List.mem_append, List.mem_map] at hp
    show p.1 + 8 ≤ S₁.size + S₂.size
    rcases hp with hp | ⟨q, hq, rfl⟩
    · have := h.held.fits _ hin₁ p hp; simp only at this; omega
    · have := h.held.fits _ hin₂ q hq; simp only at this ⊢; omega
  · intro p hp
    simp only [ShapeOf.append, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact h.held.vals _ hin₁ p hp
    · have := h.held.vals _ hin₂ q hq
      simp only at this ⊢
      rwa [show b + BitVec.ofNat 64 S₁.size + BitVec.ofNat 64 q.1
          = b + BitVec.ofNat 64 (S₁.size + q.1) by bv_omega] at this
  · intro a l hl
    exact (Disjoint.union_right (m₁ := S₁.size) (m₂ := S₂.size) (h.held.heap _ hin₁ a l hl).symm
      (h.held.heap _ hin₂ a l hl).symm hsz).symm
  · intro c hc
    exact (Disjoint.union_right (m₁ := S₁.size) (m₂ := S₂.size)
      (hap₁ c (List.mem_cons_of_mem _ hc)).symm (hap₂ c hc).symm hsz).symm
  · -- every byte of the two, and of the rest, is in the one or the rest
    intro c hc a ha
    rw [hheld] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, by
        show (a - b).toNat < S₁.size + S₂.size
        simp only at ha; omega⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨_, List.mem_cons_self, by
          show (a - b).toNat < S₁.size + S₂.size
          simp only at ha
          bv_omega⟩
      · exact ⟨c, List.mem_cons_of_mem _ hc, ha⟩

end TypedAsm.U
