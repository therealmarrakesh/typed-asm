import TypedAsm.U.Regard

/-!
# Where control goes, and whole programs

Control arrives at a value. What makes that safe is one thing, whatever
instruction sent it there: the value is known to be code wanting a context,
and the context the machine is in may be regarded as one it wants. A label
is such a value, because the program's code is typed there; so is a return
address a caller pushed, and a pointer loaded from a table.

A program is typed if the code at each of its labels is, in each context
the label allows, given that every label's is for fewer steps.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- **The machine arrives at a value known to be code**, in a context that
may be regarded as one the code wants. -/
theorem Arrives.code {n : Nat} {t : BitVec 64} {Γ : Ctx} {pre : Fam → Ctx} (x : Fam)
    (hf : (t, Ty.code pre) ∈ Γ.known) (hreg : Regards fetch sys Ψ Γ (pre x)) :
    Arrives fetch sys Ψ n t Γ := by
  intro k _ Ψ' he hwf s hs hw
  have hw' := hreg (k + 1) Ψ' he hwf s hw
  exact hasTy_code.mp (hw.known _ hf) x k (Nat.lt_succ_self k) Ψ' (MemTy.Ext.refl _) hwf s hs
    (hw'.mono (Nat.le_succ k))

/-- A fact that is so, for as many steps as matter and however the memory
typing grows, may be taken as known. -/
theorem Ok.learn {n : Nat} {a : BitVec 64} {Γ : Ctx} (fs : List Fact)
    (hfs : ∀ f ∈ fs, ∀ k, k ≤ n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → HasTy fetch sys Ψ' k f.2 f.1)
    (h : Ok fetch sys Ψ n a { Γ with known := fs ++ Γ.known }) : Ok fetch sys Ψ n a Γ :=
  fun k hk Ψ' he hwf s hs hw =>
    h k hk Ψ' he hwf s hs (hw.addKnown fs fun f hf => hfs f hf k hk Ψ' he hwf)

/-- The same of arriving: the state that arrives has what was known one
step before, so the facts are to be so for one step more. -/
theorem Arrives.learn {n : Nat} {t : BitVec 64} {Γ : Ctx} (fs : List Fact)
    (hfs : ∀ f ∈ fs, ∀ k, k ≤ n + 1 → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
      HasTy fetch sys Ψ' k f.2 f.1)
    (h : Arrives fetch sys Ψ n t { Γ with known := fs ++ Γ.known }) : Arrives fetch sys Ψ n t Γ :=
  fun k hk Ψ' he hwf s hs hw =>
    h k hk Ψ' he hwf s hs (hw.addKnown fs fun f hf => hfs f hf (k + 1) (by omega) Ψ' he hwf)

/-- A fact that is so wherever what the context knows is so may be taken as
known: it need not be so of itself. -/
theorem Ok.learnRel {n : Nat} {a : BitVec 64} {Γ : Ctx} (fs : List Fact)
    (hfs : ∀ f ∈ fs, ∀ k, k ≤ n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
      (∀ g ∈ Γ.known, HasTy fetch sys Ψ' k g.2 g.1) → HasTy fetch sys Ψ' k f.2 f.1)
    (h : Ok fetch sys Ψ n a { Γ with known := fs ++ Γ.known }) : Ok fetch sys Ψ n a Γ :=
  fun k hk Ψ' he hwf s hs hw =>
    h k hk Ψ' he hwf s hs (hw.addKnown fs fun f hf => hfs f hf k hk Ψ' he hwf hw.known)

theorem Arrives.learnRel {n : Nat} {t : BitVec 64} {Γ : Ctx} (fs : List Fact)
    (hfs : ∀ f ∈ fs, ∀ k, k ≤ n + 1 → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
      (∀ g ∈ Γ.known, HasTy fetch sys Ψ' k g.2 g.1) → HasTy fetch sys Ψ' k f.2 f.1)
    (h : Arrives fetch sys Ψ n t { Γ with known := fs ++ Γ.known }) : Arrives fetch sys Ψ n t Γ :=
  fun k hk Ψ' he hwf s hs hw =>
    h k hk Ψ' he hwf s hs
      (hw.addKnown fs fun f hf => hfs f hf (k + 1) (by omega) Ψ' he hwf hw.known)

/-- Code typed in each of a family of contexts, at an address, makes the
address a value known to be code wanting them. -/
theorem hasTy_code_of_ok {n : Nat} {v : BitVec 64} {pre : Fam → Ctx}
    (h : ∀ x, Ok fetch sys Ψ n v (pre x)) :
    ∀ k, k ≤ n + 1 → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → HasTy fetch sys Ψ' k (.code pre) v := by
  intro k hk Ψ' he _
  rw [hasTy_code]
  intro x j hj Ψ'' he' hwf' s hs hw
  exact h x j (by omega) Ψ'' (he.trans he') hwf' s hs hw

/-- **A program whose labels are typed is typed.** If the code at each
address is typed in each context the code typing allows there, for one step
more than every such code is assumed typed, then all of it is typed, for
any number of steps. -/
theorem ok_of_labels (Φ : CodeTy)
    (h : ∀ n, (∀ a Δ, Φ a Δ → Ok fetch sys Ψ n a Δ) → ∀ a Δ, Φ a Δ → Ok fetch sys Ψ (n + 1) a Δ) :
    ∀ n a Δ, Φ a Δ → Ok fetch sys Ψ n a Δ := by
  intro n
  induction n with
  | zero =>
    intro a Δ _ k hk Ψ' _ _ s _ _
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    trivial
  | succ n ih => exact h n ih

/-- **And safe**: from every state at an address, matching a context the
code typing allows there, with a memory typing that makes sense. -/
theorem safe_of_labels (Φ : CodeTy) (hΨ : Ψ.WF)
    (h : ∀ n, (∀ a Δ, Φ a Δ → Ok fetch sys Ψ n a Δ) → ∀ a Δ, Φ a Δ → Ok fetch sys Ψ (n + 1) a Δ)
    {a : BitVec 64} {Δ : Ctx} (hΦ : Φ a Δ) {s : State} (hs : s.rip = a)
    (hw : ∀ n, WellTyped fetch sys Ψ n Δ s) : Safe fetch sys s :=
  safe_of_safeN fun n =>
    ok_of_labels Φ h n a Δ hΦ n (Nat.le_refl n) Ψ (MemTy.Ext.refl Ψ) hΨ s hs (hw n)

end TypedAsm.U
