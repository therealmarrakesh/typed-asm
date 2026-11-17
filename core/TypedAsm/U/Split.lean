import TypedAsm.U.Regard
import TypedAsm.Owned

/-!
# Regions held, dropped, added, and taken as one

A region the context holds may be dropped from what it holds, and a region
that is writable and overlaps nothing may be added: which is how a system
call that maps or unmaps memory is typed. And two regions that lie end to
end may be regarded as one: nothing happens to the machine, it is only how
the same bytes are regarded. Taking one region as several, or as part of
itself, is a case of the one statement of what regard comes to, in
`Entail`.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat} {Γ : Ctx} {s : State}

namespace WellTyped

/-- A region the context holds may be dropped from what it holds: less is
then asked of the state. -/
theorem eraseHeld (h : WellTyped fetch sys Ψ n Γ s) (k : Nat) :
    WellTyped fetch sys Ψ n { Γ with held := Γ.held.eraseIdx k } s :=
  have hsub : ∀ c ∈ Γ.held.eraseIdx k, c ∈ Γ.held :=
    fun c hc => (List.eraseIdx_sublist _ _).subset hc
  { val := h.val
    known := h.known
    flags := h.flags
    heapPerm := h.heapPerm
    heap := h.heap
    text := h.text
    said := h.said
    held :=
      { perm := fun c hc => h.held.perm c (hsub c hc)
        size_lt := fun c hc => h.held.size_lt c (hsub c hc)
        fits := fun c hc => h.held.fits c (hsub c hc)
        vals := fun c hc => h.held.vals c (hsub c hc)
        heap := fun c hc => h.held.heap c (hsub c hc)
        apart := h.held.apart.sublist (List.eraseIdx_sublist _ _) } }

/-- A region that is writable, holds the values said, and overlaps nothing
the context holds or the memory typing describes may be added to what the
context holds. -/
theorem addHeld {b : Region} (h : WellTyped fetch sys Ψ n Γ s)
    (hperm : s.canWrite b.1 b.2.size = true) (hlt : b.2.size < 2 ^ 64)
    (hfits : ∀ p ∈ b.2.vals, p.1 + 8 ≤ b.2.size)
    (hvals : ∀ p ∈ b.2.vals, s.load64 (b.1 + BitVec.ofNat 64 p.1) = p.2)
    (hheap : ∀ a l, Ψ a = some l → Disjoint b.1 b.2.size a l.size)
    (hapart : ∀ c ∈ Γ.held, Disjoint b.1 b.2.size c.1 c.2.size) :
    WellTyped fetch sys Ψ n { Γ with held := b :: Γ.held } s :=
  { val := h.val
    known := h.known
    flags := h.flags
    heapPerm := h.heapPerm
    heap := h.heap
    text := h.text
    said := h.said
    held :=
      { perm := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hperm
          · exact h.held.perm c hc
        size_lt := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hlt
          · exact h.held.size_lt c hc
        fits := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hfits
          · exact h.held.fits c hc
        vals := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hvals
          · exact h.held.vals c hc
        heap := fun c hc a l hl => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hheap a l hl
          · exact h.held.heap c hc a l hl
        apart := List.pairwise_cons.mpr ⟨hapart, h.held.apart⟩ } }

end WellTyped

/-- **Two held regions that lie end to end may be regarded as one**, the
bytes of the first followed by those of the second. They are taken as the
first two the context lists; any two may be put there, the order of what is
held being of no account. -/
theorem Regards.join {Γ : Ctx} {b : BitVec 64} {S₁ S₂ : Held} {rest : List Region}
    (hheld : Γ.held = (b, S₁) :: (b + BitVec.ofNat 64 S₁.size, S₂) :: rest)
    (hsz : S₁.size + S₂.size < 2 ^ 64) :
    Regards fetch sys Ψ Γ { Γ with held := (b, S₁.append S₂) :: rest } := by
  intro j Ψ' he hwf s h
  refine ⟨Ψ', MemTy.Ext.refl _, hwf, ?_⟩
  have hin₁ : (b, S₁) ∈ Γ.held := by rw [hheld]; exact List.mem_cons_self
  have hin₂ : (b + BitVec.ofNat 64 S₁.size, S₂) ∈ Γ.held := by
    rw [hheld]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hrest : ∀ c ∈ rest, c ∈ Γ.held := fun c hc => by
    rw [hheld]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)
  have hap := h.held.apart
  rw [hheld] at hap
  obtain ⟨hap₁, hap'⟩ := List.pairwise_cons.mp hap
  obtain ⟨hap₂, hap₃⟩ := List.pairwise_cons.mp hap'
  -- what is held besides the two
  have h₀ : WellTyped fetch sys Ψ' j { Γ with held := rest } s :=
    { val := h.val
      known := h.known
      flags := h.flags
      heapPerm := h.heapPerm
      heap := h.heap
      text := h.text
      said := h.said
      held :=
        { perm := fun c hc => h.held.perm c (hrest c hc)
          size_lt := fun c hc => h.held.size_lt c (hrest c hc)
          fits := fun c hc => h.held.fits c (hrest c hc)
          vals := fun c hc => h.held.vals c (hrest c hc)
          heap := fun c hc => h.held.heap c (hrest c hc)
          apart := hap₃ } }
  refine h₀.addHeld (b := (b, S₁.append S₂)) ?_ hsz ?_ ?_ ?_ ?_
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

end TypedAsm.U
