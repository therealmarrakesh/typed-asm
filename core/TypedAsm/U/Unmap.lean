import TypedAsm.U.Map

/-!
# Memory given back to the system

A region the context holds may cease to be accessible: the context without
it still describes the state. So a call that takes back exactly a region the
context holds is typed, the region no longer held, whether or not the system
did as asked. To give back part of a region, it is regarded as two first.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat} {Γ : Ctx} {s : State}

/-- **A held region may be given up**, even if its memory has meanwhile
become inaccessible: nothing else the context describes lay in it. -/
theorem WellTyped.dropHeld {s' : State} {k : Nat} {a : BitVec 64} {S : Held}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hk : Γ.held[k]? = some (a, S))
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hmem : s'.mem = s.mem)
    (hperm : ∀ x, s'.perm x = s.perm x ∨ (x - a).toNat < S.size) :
    WellTyped fetch sys Ψ n { Γ with held := Γ.held.eraseIdx k } s' := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (a, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hsz := h.held.size_lt _ hin
  have hhp := h.held.heap _ hin
  simp only at hsz hhp
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hsub : ∀ c ∈ Γ.held.eraseIdx k, c ∈ Γ.held :=
    fun c hc => (List.eraseIdx_sublist _ _).subset hc
  exact {
    val := fun r => by rw [hg]; exact h.val r
    known := h.known
    flags := by rw [hflags]; exact h.flags
    heapPerm := fun b l hl =>
      ⟨State.canRead_apart (hhp b l hl) hsz (hΨ.size_lt b l hl) hperm (h.heapPerm b l hl).1,
        fun hw => State.canWrite_apart (hhp b l hl) hsz (hΨ.size_lt b l hl) hperm
          ((h.heapPerm b l hl).2 hw)⟩
    heap := fun b l hl p hp => by rw [State.load64_congr hmem]; exact h.heap b l hl p hp
    text := fun b l hl ht => by rw [hmem]; exact h.text b l hl ht
    said := fun b l bs hl hs k hk => by rw [hmem]; exact h.said b l bs hl hs k hk
    held := {
      perm := fun c hc => by
        obtain ⟨m, hm, hmk, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hc
        have hd := h.held_apart hm hklt hmk
        rw [hkeq] at hd
        simp only at hd
        exact State.canWrite_apart hd hsz (h.held.size_lt _ (List.getElem_mem hm)) hperm
          (h.held.perm _ (List.getElem_mem hm))
      size_lt := fun c hc => h.held.size_lt c (hsub c hc)
      fits := fun c hc => h.held.fits c (hsub c hc)
      vals := fun c hc p hp => by
        rw [State.load64_congr hmem]; exact h.held.vals c (hsub c hc) p hp
      heap := fun c hc => h.held.heap c (hsub c hc)
      apart := h.held.apart.sublist (List.eraseIdx_sublist _ _) } }

/-- **A call that takes memory back**, of exactly a region the context
holds, returns with the region no longer held. -/
theorem Steps.unmap {D : SysDesc} (hD : Describes sys D) {Γ : Ctx} {next : BitVec 64} {k : Nat}
    {S : Held} (hk : D.kind (Γ.val .rax) = some .unmap)
    (hheld : Γ.held[k]? = some (Γ.val .rdi, S)) (hsz : S.size = pages (Γ.val .rsi))
    (hpre : ∀ n, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = next →
      WellTyped fetch sys Ψ' n Γ s → D.pre s) :
    Steps fetch sys Ψ .syscall next Γ fun t Γ' => t = next ∧
      ∃ v, Γ' = CtxOf.afterSys { Γ with held := Γ.held.eraseIdx k } v next := by
  intro n Ψ' he hwf s hrip hw
  obtain ⟨t, hst, hun⟩ := hD s .unmap (by rw [hw.val]; exact hk) (hpre n Ψ' he hwf s hrip hw)
  rw [hw.val .rdi, hw.val .rsi, ← hsz] at hun
  rcases hun with ⟨v, rfl⟩ | ⟨hal, hfit, v, rfl⟩
  · refine ⟨_, hst, Ψ', MemTy.Ext.refl _, hwf, _, ⟨hrip, v, rfl⟩, ?_⟩
    rw [← hrip]
    exact (hw.eraseHeld k).ret v s.world
  · refine ⟨_, hst, Ψ', MemTy.Ext.refl _, hwf, _, ⟨hrip, v, rfl⟩, ?_⟩
    have hsz4 : S.size % 4096 = 0 := by rw [hsz]; exact Nat.mul_mod_left _ _
    have hD' := hw.dropHeld hwf hheld (s' := s.unmap (Γ.val .rdi) S.size) rfl rfl rfl (fun x => by
      rw [State.perm_unmap s hal hsz4 hfit]
      split
      · next hin => exact .inr hin
      · exact .inl rfl)
    rw [← hrip]
    exact hD'.ret v (s.unmap (Γ.val .rdi) S.size).world

end TypedAsm.U
