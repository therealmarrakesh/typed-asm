import TypedAsm.U.Shared

/-!
# One context regarded as another

`Regards Γ Δ`: every state that matches `Γ` matches `Δ`. Nothing happens
to the machine, and nothing to the memory typing: it is the same state,
described another way. It is the one question asked wherever control passes
to code that wants a context.

What a context says of the regions held is all of what is held, so a
description of the same state holds the same bytes: in another order, one
region as two, two as one, saying less or more of what is in them, but
never fewer bytes. Coming to hold memory, and ceasing to, are not ways of
regarding: they are things that happen, each with its own statement.

Code typed in `Δ` is typed in any context regarded as `Δ`.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- A byte the machine can write is one it can touch. -/
theorem perm_of_writable {p : Perm} (h : p.writable = true) : p ≠ .none := by
  cases p <;> first | (cases h; done) | exact fun e => nomatch e

/-- **Two contexts that match one state hold the same bytes.** A byte in a
region one holds is in a region the other holds. -/
theorem WellTyped.held_agree {n m : Nat} {Γ Δ : Ctx} {s : State} (hΨ : Ψ.WF)
    (hΓ : WellTyped fetch sys Ψ n Γ s) (hΔ : WellTyped fetch sys Ψ m Δ s) {b : Region}
    (hb : b ∈ Γ.held) {a : BitVec 64} (ha : (a - b.1).toNat < b.2.size) :
    ∃ c ∈ Δ.held, (a - c.1).toNat < c.2.size := by
  have hw := State.canWrite_iff.mp (hΓ.held.perm b hb) _ ha
  rw [show b.1 + BitVec.ofNat 64 (a - b.1).toNat = a by bv_omega] at hw
  rcases hΔ.complete a (perm_of_writable hw) with h | ⟨base, l, hl, hin⟩
  · exact h
  · exfalso
    have hd := (hΓ.held.heap b hb base l hl).of_pos (by omega) (by omega)
    have h1 := hΓ.held.size_lt b hb
    have h2 := hΨ.size_lt base l hl
    obtain ⟨hd1, hd2⟩ := hd
    bv_omega

/-- Every state that matches `Γ` matches `Δ`. -/
def Regards (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ Δ : Ctx) : Prop :=
  ∀ k, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' k Γ s →
    WellTyped fetch sys Ψ' k Δ s

theorem Regards.refl (Γ : Ctx) : Regards fetch sys Ψ Γ Γ :=
  fun _ _ _ _ _ hw => hw

theorem Regards.trans {Γ Δ Θ : Ctx} (h₁ : Regards fetch sys Ψ Γ Δ) (h₂ : Regards fetch sys Ψ Δ Θ) :
    Regards fetch sys Ψ Γ Θ :=
  fun k Ψ' he hwf s hw => h₂ k Ψ' he hwf s (h₁ k Ψ' he hwf s hw)

/-- **Code typed in a context is typed in any context regarded as it.** -/
theorem Ok.regard {n : Nat} {a : BitVec 64} {Γ Δ : Ctx} (h : Regards fetch sys Ψ Γ Δ)
    (hΔ : Ok fetch sys Ψ n a Δ) : Ok fetch sys Ψ n a Γ :=
  fun k hk Ψ' he hwf s hrip hw => hΔ k hk Ψ' he hwf s hrip (h k Ψ' he hwf s hw)

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

end TypedAsm.U
