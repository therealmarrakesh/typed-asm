import TypedAsm.U.Step
import TypedAsm.U.SysStep
import TypedAsm.U.Guard

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
  /-- A system call that returns was stepped over, the name `k` standing for
  what it hands back: the rest holds whatever that is. -/
  | sys (k : Nat) (rest : Walk)
  /-- A system call ends the program: nothing is left. -/
  | ends

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
  | .sys k rest, ρ => ∀ x, rest.holds P A (ρ.setVal k x)
  | .ends, _ => True

/-- Whether the walk got anywhere: it stepped over an instruction or a call,
or the program ended. -/
def Walk.moved : Walk → Bool
  | .step .. | .sys .. | .ends => true
  | _ => false

/-- **The checker walked from an address**, for at most so many
instructions, `k` being a name no term yet mentions. -/
def walk (code : List (BitVec 64 × Instr × BitVec 64)) : Nat → Nat → BitVec 64 → CtxS → Walk
  | 0, _, a, Γ => .stop a Γ
  | fuel + 1, k, a, Γ =>
    match code.find? fun e => e.1 = a with
    | none => .stop a Γ
    | some (_, i, len) =>
      if i = .syscall then
        if sysEnds Γ then .ends
        else
          match sysWorld Γ k (a + len) with
          | some Γ' =>
            if Γ'.under (k + 1) then .sys k (walk code fuel (k + 1) (a + len) Γ') else .stop a Γ
          | none => .stop a Γ
      else
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
steps as the code where it stopped is typed for; and for one step more
where the walk got anywhere, which is what a program's labels are typed by,
each for one step more than all are assumed typed for. -/
theorem walk_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {n : Nat} (code : List (BitVec 64 × Instr × BitVec 64))
    (hcode : ∀ e ∈ code, fetch e.1 = some (e.2.1, e.2.2)) :
    (fuel k : Nat) → (a : BitVec 64) → (Γ : CtxS) → (ρ : Env) → Γ.under k = true →
    (walk code fuel k a Γ).holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ →
    Ok fetch sys Ψ n a (Γ.den ρ) ∧
      ((walk code fuel k a Γ).moved = true → Ok fetch sys Ψ (n + 1) a (Γ.den ρ))
  | 0, _, _, _, _, _, h => ⟨h, fun hm => nomatch hm⟩
  | fuel + 1, k, a, Γ, ρ, hu, h => by
    generalize hW : walk code (fuel + 1) k a Γ = W at h ⊢
    unfold walk at hW
    split at hW
    · subst hW; exact ⟨h, fun hm => nomatch hm⟩
    · next e i len hfind =>
      have hmem := List.mem_of_find?_eq_some hfind
      have ha : e = a := by simpa using List.find?_some hfind
      subst ha
      have hf : fetch e = some (i, len) := hcode _ hmem
      -- an instruction or a call typed, with the machine arriving where it is left
      have both : (∀ m, m ≤ n → Ok fetch sys Ψ (m + 1) e (Γ.den ρ)) →
          Ok fetch sys Ψ n e (Γ.den ρ) ∧ Ok fetch sys Ψ (n + 1) e (Γ.den ρ) := fun hall =>
        ⟨by
          cases n with
          | zero => exact Ok.zero _ _
          | succ m => exact hall m (Nat.le_succ m), hall n (Nat.le_refl n)⟩
      split at hW
      · next hsys =>
        subst hsys
        split at hW
        · next hends =>
          exact ⟨sysEnds_sound hD hkind hpre hends hf n, fun _ =>
            sysEnds_sound hD hkind hpre hends hf (n + 1)⟩
        · split at hW
          · next Γ' hw =>
            split at hW
            · next hu' =>
              subst hW
              have ih := fun x => (walk_sound hD hkind hpre code hcode fuel (k + 1) (e + len) Γ'
                (ρ.setVal k x) hu' (h x)).1
              have hb := both fun m hm => by
                refine Ok.step hf (sysWorld_sound hD hkind hpre hw hu) ?_
                rintro t Δ ⟨x, rfl, rfl⟩
                exact ((ih x).mono hm).arrives
              exact ⟨hb.1, fun _ => hb.2⟩
            · subst hW; exact ⟨h, fun hm => nomatch hm⟩
          · subst hW; exact ⟨h, fun hm => nomatch hm⟩
      · split at hW
        · subst hW; exact ⟨h, fun hm => nomatch hm⟩
        · next Γ' t hstep =>
          split at hW
          · next hu' =>
            have key : ∀ (rest : Walk),
                (GuardOk ρ Γ (e + len) i ∧ ∀ x, rest.holds (Ok fetch sys Ψ n)
                  (Arrives fetch sys Ψ n) (ρ.setVal k x)) →
                (∀ x, rest.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) (ρ.setVal k x) →
                  Arrives fetch sys Ψ n (t.den (ρ.setVal k x)) (Γ'.den (ρ.setVal k x))) →
                Ok fetch sys Ψ n e (Γ.den ρ) ∧ Ok fetch sys Ψ (n + 1) e (Γ.den ρ) := by
              intro rest ⟨hg, hrest⟩ harr
              refine both fun m hm => ?_
              refine Ok.step hf (stepHeld_sound hstep hu hg) ?_
              rintro t' Δ ⟨x, rfl, rfl⟩
              exact (harr x (hrest x)).mono hm
            split at hW
            · next t' ht =>
              subst hW
              have hb := key _ h (fun x hx => by
                rw [Val.lit?_den ht]
                exact (walk_sound hD hkind hpre code hcode fuel (k + 1) t' Γ' (ρ.setVal k x) hu'
                  hx).1.arrives)
              exact ⟨hb.1, fun _ => hb.2⟩
            · subst hW
              have hb := key _ h (fun x hx => hx)
              exact ⟨hb.1, fun _ => hb.2⟩
          · subst hW; exact ⟨h, fun hm => nomatch hm⟩

/-- Whether a walk leaves nothing to be shown: every instruction it stepped
over cannot fault of itself, and every way through it ends the program. -/
def Walk.auto : Walk → Bool
  | .step i _ _ _ rest => i.noGuard && rest.auto
  | .sys _ rest => rest.auto
  | .ends => true
  | _ => false

/-- Such a walk holds. -/
theorem Walk.holds_of_auto (P A : BitVec 64 → Ctx → Prop) :
    (W : Walk) → (ρ : Env) → W.auto = true → W.holds P A ρ
  | .step i Γ next k rest, ρ, h => by
    simp only [Walk.auto, Bool.and_eq_true] at h
    exact ⟨fun d hd x => desc_noGuard h.1 hd _ _ _ _ _,
      fun x => Walk.holds_of_auto P A rest _ h.2⟩
  | .sys k rest, ρ, h => fun x => Walk.holds_of_auto P A rest _ h
  | .ends, _, _ => trivial
  | .stop _ _, _, h => nomatch h
  | .arrive _ _, _, h => nomatch h

end TypedAsm.U
