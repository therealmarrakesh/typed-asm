import TypedAsm.U.Step
import TypedAsm.U.Program

/-!
# A block walked

The checker's step, taken instruction after instruction for as long as the
address control goes to is one written out. What comes of it is a tree of
what is left to be shown: at each instruction, that it does not fault for a
reason of its own; and where the walk stops, that the code there is typed
in the context reached, or that control arrives at a value.

A walk whose leaves hold types the block it started at.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- What a walk through a block leaves to be shown. -/
inductive Walk
  /-- The walk stopped at an address, in a context: the code there is to be
  typed in it. -/
  | stop (a : BitVec 64) (Γ : CtxS)
  /-- Control goes to a value, in a context: it is to arrive there. -/
  | arrive (t : Val) (Γ : CtxS)
  /-- An instruction was stepped over, from a context, the name `k` standing
  for whatever it read that the context did not say: it does not fault of
  itself, and the rest holds whatever `k` stands for. -/
  | step (i : Instr) (Γ : CtxS) (next : BitVec 64) (k : Nat) (rest : Walk)

/-- That an instruction does not fault for a reason of its own, in a
context, whatever it reads. -/
def GuardOk (ρ : Env) (Γ : CtxS) (next : BitVec 64) (i : Instr) : Prop :=
  ∀ d, i.desc = some d → ∀ x : BitVec 64,
    d.guard (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
      ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x = true

/-- What a walk leaves to be shown, of what its terms stand for: `P` of
where it stopped, `A` of where control goes to a value. -/
def Walk.holds (P A : BitVec 64 → Ctx → Prop) : Walk → Env → Prop
  | .stop a Γ, ρ => P a (Γ.den ρ)
  | .arrive t Γ, ρ => A (t.den ρ) (Γ.den ρ)
  | .step i Γ next k rest, ρ => GuardOk ρ Γ next i ∧ ∀ x, rest.holds P A (ρ.setVal k x)

/-- **The checker walked from an address**, for at most so many
instructions, `k` being a name no term yet mentions. -/
def walk (code : List (BitVec 64 × Instr × BitVec 64)) : Nat → Nat → BitVec 64 → CtxS → Walk
  | 0, _, a, Γ => .stop a Γ
  | fuel + 1, k, a, Γ =>
    match code.find? fun e => e.1 = a with
    | none => .stop a Γ
    | some (_, i, len) =>
      match stepHeld Γ k (a + len) i with
      | none => .stop a Γ
      | some (Γ', t) =>
        if Γ'.under (k + 1) then
          match t.lit? with
          | some t' => .step i Γ (a + len) k (walk code fuel (k + 1) t' Γ')
          | none => .step i Γ (a + len) k (.arrive t Γ')
        else .stop a Γ

theorem Ok.zero (a : BitVec 64) (Γ : Ctx) : Ok fetch sys Ψ 0 a Γ := by
  intro k hk Ψ' _ _ s _ _
  have hk0 : k = 0 := Nat.le_zero.mp hk
  subst hk0
  trivial

theorem Arrives.mono {n m : Nat} {t : BitVec 64} {Γ : Ctx} (h : Arrives fetch sys Ψ n t Γ)
    (hle : m ≤ n) : Arrives fetch sys Ψ m t Γ :=
  fun k hk => h k (Nat.le_trans hk hle)

/-- **A walk whose leaves hold types the block it started at**, for as many
steps as the code where it stopped is typed for. -/
theorem walk_sound {n : Nat} (code : List (BitVec 64 × Instr × BitVec 64))
    (hcode : ∀ e ∈ code, fetch e.1 = some (e.2.1, e.2.2)) :
    (fuel k : Nat) → (a : BitVec 64) → (Γ : CtxS) → (ρ : Env) → Γ.under k = true →
    (walk code fuel k a Γ).holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ →
    Ok fetch sys Ψ n a (Γ.den ρ)
  | 0, _, _, _, _, _, h => h
  | fuel + 1, k, a, Γ, ρ, hu, h => by
    unfold walk at h
    split at h
    · exact h
    · next e i len hfind =>
      have hmem := List.mem_of_find?_eq_some hfind
      have ha : e = a := by simpa using List.find?_some hfind
      subst ha
      have hf : fetch e = some (i, len) := hcode _ hmem
      split at h
      · exact h
      · next Γ' t hstep =>
        split at h
        · next hu' =>
          -- the instruction is typed, and the machine arrives wherever it leaves it
          have key : ∀ (rest : Walk),
              (GuardOk ρ Γ (e + len) i ∧ ∀ x, rest.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n)
                (ρ.setVal k x)) →
              (∀ x, rest.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) (ρ.setVal k x) →
                Arrives fetch sys Ψ n (t.den (ρ.setVal k x)) (Γ'.den (ρ.setVal k x))) →
              Ok fetch sys Ψ n e (Γ.den ρ) := by
            intro rest ⟨hg, hrest⟩ harr
            cases n with
            | zero => exact Ok.zero _ _
            | succ m =>
              refine Ok.step hf (stepHeld_sound hstep hu hg) ?_
              rintro t' Δ ⟨x, rfl, rfl⟩
              exact (harr x (hrest x)).mono (Nat.le_succ m)
          split at h
          · next t' ht =>
            refine key _ h (fun x hx => ?_)
            rw [Val.lit?_den ht]
            exact (walk_sound code hcode fuel (k + 1) t' Γ' (ρ.setVal k x) hu' hx).arrives
          · exact key _ h (fun x hx => hx)
        · exact h

/-- **And for one step more**, where the walk stepped over at least one
instruction: which is what a program's labels are typed by, each for one
step more than all are assumed typed for. -/
theorem walk_sound_succ {n : Nat} (code : List (BitVec 64 × Instr × BitVec 64))
    (hcode : ∀ e ∈ code, fetch e.1 = some (e.2.1, e.2.2)) (fuel k : Nat) (a : BitVec 64)
    (Γ : CtxS) (ρ : Env) (hu : Γ.under k = true) {i : Instr} {Γ₀ : CtxS} {nx : BitVec 64}
    {k' : Nat} {rest : Walk} (hw : walk code (fuel + 1) k a Γ = .step i Γ₀ nx k' rest)
    (h : (walk code (fuel + 1) k a Γ).holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ) :
    Ok fetch sys Ψ (n + 1) a (Γ.den ρ) := by
  unfold walk at h hw
  split at h
  · rw [‹List.find? _ code = none›] at hw; cases hw
  · next e i' len hfind =>
    rw [hfind] at hw
    simp only at hw
    have hmem := List.mem_of_find?_eq_some hfind
    have ha : e = a := by simpa using List.find?_some hfind
    subst ha
    have hf : fetch e = some (i', len) := hcode _ hmem
    split at h
    · next hnone => rw [hnone] at hw; cases hw
    · next Γ' t hstep =>
      rw [hstep] at hw
      simp only at hw
      split at h
      · next hu' =>
        have key : ∀ (rest : Walk),
            (GuardOk ρ Γ (e + len) i' ∧ ∀ x, rest.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n)
              (ρ.setVal k x)) →
            (∀ x, rest.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) (ρ.setVal k x) →
              Arrives fetch sys Ψ n (t.den (ρ.setVal k x)) (Γ'.den (ρ.setVal k x))) →
            Ok fetch sys Ψ (n + 1) e (Γ.den ρ) := by
          intro rest ⟨hg, hrest⟩ harr
          refine Ok.step hf (stepHeld_sound hstep hu hg) ?_
          rintro t' Δ ⟨x, rfl, rfl⟩
          exact harr x (hrest x)
        split at h
        · next t' ht =>
          refine key _ h (fun x hx => ?_)
          rw [Val.lit?_den ht]
          exact (walk_sound code hcode fuel (k + 1) t' Γ' (ρ.setVal k x) hu' hx).arrives
        · exact key _ h (fun x hx => hx)
      · next hnu => simp only [hnu] at hw; cases hw

end TypedAsm.U
