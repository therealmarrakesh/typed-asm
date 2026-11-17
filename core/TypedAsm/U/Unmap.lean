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

/-- **A held region whose memory has become inaccessible is no longer
held**: nothing else the context describes lay in it, and every byte still
accessible is still accounted for. -/
theorem WellTyped.dropHeld {s' : State} {k : Nat} {a : BitVec 64} {S : Held}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hk : Γ.held[k]? = some (a, S))
    (hregs : s'.regs = s.regs) (hflags : s'.flags = s.flags) (hmem : s'.mem = s.mem)
    (hgone : ∀ x, (x - a).toNat < S.size → s'.perm x = .none)
    (hkept : ∀ x, ¬ (x - a).toNat < S.size → s'.perm x = s.perm x) :
    WellTyped fetch sys Ψ n { Γ with held := Γ.held.eraseIdx k } s' := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (a, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hsz := h.held.size_lt _ hin
  have hhp := h.held.heap _ hin
  simp only at hsz hhp
  have hg : ∀ r, s'.getReg r = s.getReg r := fun r => by simp only [State.getReg, hregs]
  have hperm : ∀ x, s'.perm x = s.perm x ∨ (x - a).toNat < S.size := fun x => by
    by_cases hx : (x - a).toNat < S.size
    · exact .inr hx
    · exact .inl (hkept x hx)
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
    complete := fun x hx => by
      have hout : ¬ (x - a).toNat < S.size := fun hin => hx (hgone x hin)
      rw [hkept x hout] at hx
      rcases h.complete x hx with ⟨c, hc, hlt⟩ | hr
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
        by_cases hik : i = k
        · subst hik
          rw [hkeq] at hlt
          exact absurd hlt hout
        · exact .inl ⟨_, List.mem_eraseIdx_iff_getElem.mpr ⟨i, hi, hik, rfl⟩, hlt⟩
      · exact .inr hr
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
holds, returns with zero and the region no longer held, its memory no longer
accessible; or with an error number and the region held as it was. What it
hands back says which. -/
theorem Steps.unmap {D : SysDesc} (hD : Describes sys D) {Γ : Ctx} {next : BitVec 64} {k : Nat}
    {S : Held} (hk : D.kind (Γ.val .rax) = some .unmap)
    (hheld : Γ.held[k]? = some (Γ.val .rdi, S)) (hsz : S.size = pages (Γ.val .rsi))
    (hpre : ∀ n, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = next →
      WellTyped fetch sys Ψ' n Γ s → D.pre s) :
    Steps fetch sys Ψ .syscall next Γ fun t Γ' => t = next ∧
      ((∃ v, SysErr v ∧ Γ' = Γ.afterSys v next) ∨
        Γ' = CtxOf.afterSys { Γ with held := Γ.held.eraseIdx k } 0 next) := by
  intro n Ψ' he hwf s hrip hw
  obtain ⟨t, hst, hun⟩ := hD s .unmap (by rw [hw.val]; exact hk) (hpre n Ψ' he hwf s hrip hw)
  rw [hw.val .rdi, hw.val .rsi, ← hsz] at hun
  rcases hun with ⟨v, hv, rfl⟩ | ⟨hal, hfit, rfl⟩
  · refine ⟨_, hst, _, ⟨hrip, .inl ⟨v, hv, rfl⟩⟩, ?_⟩
    rw [← hrip]
    exact hw.ret v s.world
  · refine ⟨_, hst, _, ⟨hrip, .inr rfl⟩, ?_⟩
    have hsz4 : S.size % 4096 = 0 := by rw [hsz]; exact Nat.mul_mod_left _ _
    have hD' := hw.dropHeld hwf hheld (s' := s.unmap (Γ.val .rdi) S.size) rfl rfl rfl
      (fun x hx => by rw [State.perm_unmap s hal hsz4 hfit]; simp only [hx, ↓reduceIte])
      (fun x hx => by rw [State.perm_unmap s hal hsz4 hfit]; simp only [hx, ↓reduceIte])
    rw [← hrip]
    exact hD'.ret 0 (s.unmap (Γ.val .rdi) S.size).world

end TypedAsm.U
