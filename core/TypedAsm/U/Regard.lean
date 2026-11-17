import TypedAsm.U.Shared

/-!
# One context regarded as another

`Regards Γ Δ`: every state that matches `Γ` matches `Δ`, the memory typing
having perhaps grown. It is the one question asked wherever control passes
to code that wants a context, and wherever what is held is to be seen
differently: fewer facts, or facts that follow from those known; the
regions held in another order, one as two, two as one, or one made a block
others may point into.

Code typed in `Δ` is typed in any context regarded as `Δ`.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- Every state that matches `Γ` matches `Δ`, the memory typing having
perhaps grown. -/
def Regards (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ Δ : Ctx) : Prop :=
  ∀ k, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' k Γ s →
    ∃ Ψ'' : MemTy, Ψ'.Ext Ψ'' ∧ Ψ''.WF ∧ WellTyped fetch sys Ψ'' k Δ s

theorem Regards.refl (Γ : Ctx) : Regards fetch sys Ψ Γ Γ :=
  fun _ Ψ' _ hwf _ hw => ⟨Ψ', MemTy.Ext.refl _, hwf, hw⟩

theorem Regards.trans {Γ Δ Θ : Ctx} (h₁ : Regards fetch sys Ψ Γ Δ) (h₂ : Regards fetch sys Ψ Δ Θ) :
    Regards fetch sys Ψ Γ Θ := by
  intro k Ψ' he hwf s hw
  obtain ⟨Ψ₁, he₁, hwf₁, hw₁⟩ := h₁ k Ψ' he hwf s hw
  obtain ⟨Ψ₂, he₂, hwf₂, hw₂⟩ := h₂ k Ψ₁ (he.trans he₁) hwf₁ s hw₁
  exact ⟨Ψ₂, he₁.trans he₂, hwf₂, hw₂⟩

/-- **Code typed in a context is typed in any context regarded as it.** -/
theorem Ok.regard {n : Nat} {a : BitVec 64} {Γ Δ : Ctx} (h : Regards fetch sys Ψ Γ Δ)
    (hΔ : Ok fetch sys Ψ n a Δ) : Ok fetch sys Ψ n a Γ := by
  intro k hk Ψ' he hwf s hrip hw
  obtain ⟨Ψ'', he', hwf', hw'⟩ := h k Ψ' he hwf s hw
  exact SafeN.mono (hΔ k hk Ψ'' (he.trans he') hwf' s hrip hw') (Nat.le_refl _)

/-- What is known of a value one way is known of it another: at every step
count, under every memory typing. `Sub` is the part of this that is read off
the two forms; the rest is what follows of the value itself. -/
def Follows (fetch : Fetch) (sys : Syscall) (v : BitVec 64) (τ υ : Ty) : Prop :=
  ∀ (Ψ : MemTy) (n : Nat), HasTy fetch sys Ψ n τ v → HasTy fetch sys Ψ n υ v

theorem Follows.refl (v : BitVec 64) (τ : Ty) : Follows fetch sys v τ τ := fun _ _ h => h

theorem Follows.trans {v : BitVec 64} {τ υ φ : Ty} (h₁ : Follows fetch sys v τ υ)
    (h₂ : Follows fetch sys v υ φ) : Follows fetch sys v τ φ :=
  fun Ψ n h => h₂ Ψ n (h₁ Ψ n h)

theorem Sub.follows {v : BitVec 64} {τ υ : Ty} (h : Sub v τ υ) : Follows fetch sys v τ υ :=
  fun _ _ hv => hv.sub h

/-- A context with the same registers, flags and held regions, of which
each thing known follows from something known before of the same value.
Facts may be dropped. -/
theorem Regards.follows {Γ : Ctx} (fs : List Fact)
    (h : ∀ f ∈ fs, ∃ τ, (f.1, τ) ∈ Γ.known ∧ Follows fetch sys f.1 τ f.2) :
    Regards fetch sys Ψ Γ { Γ with known := fs } := by
  intro k Ψ' he hwf s hw
  refine ⟨Ψ', MemTy.Ext.refl _, hwf, ?_⟩
  exact
    { val := hw.val
      known := fun f hf => by
        obtain ⟨τ, hτ, hfol⟩ := h f hf
        exact hfol _ _ (hw.known _ hτ)
      flags := hw.flags
      heapPerm := hw.heapPerm
      heap := hw.heap
      text := hw.text
      said := hw.said
      held :=
        { perm := hw.held.perm
          size_lt := hw.held.size_lt
          fits := hw.held.fits
          vals := hw.held.vals
          heap := hw.held.heap
          apart := hw.held.apart } }

/-- And so where each follows by `Sub`. -/
theorem Regards.known {Γ : Ctx} (fs : List Fact)
    (h : ∀ f ∈ fs, ∃ τ, (f.1, τ) ∈ Γ.known ∧ Sub f.1 τ f.2) :
    Regards fetch sys Ψ Γ { Γ with known := fs } :=
  Regards.follows fs fun f hf =>
    let ⟨τ, hτ, hsub⟩ := h f hf
    ⟨τ, hτ, hsub.follows⟩

/-- The regions held, in any order. -/
theorem Regards.perm {Γ : Ctx} {L : List Region} (h : L.Perm Γ.held) :
    Regards fetch sys Ψ Γ { Γ with held := L } := by
  intro k Ψ' he hwf s hw
  refine ⟨Ψ', MemTy.Ext.refl _, hwf, ?_⟩
  have hsub : ∀ b, b ∈ L → b ∈ Γ.held := fun b hb => h.subset hb
  exact
    { val := hw.val
      known := hw.known
      flags := hw.flags
      heapPerm := hw.heapPerm
      heap := hw.heap
      text := hw.text
      said := hw.said
      held :=
        { perm := fun b hb => hw.held.perm b (hsub b hb)
          size_lt := fun b hb => hw.held.size_lt b (hsub b hb)
          fits := fun b hb => hw.held.fits b (hsub b hb)
          vals := fun b hb => hw.held.vals b (hsub b hb)
          heap := fun b hb => hw.held.heap b (hsub b hb)
          apart := (h.pairwise_iff (fun {x y}
            (hxy : Disjoint x.1 x.2.size y.1 y.2.size) => Disjoint.symm hxy)).mpr hw.held.apart } }

end TypedAsm.U
