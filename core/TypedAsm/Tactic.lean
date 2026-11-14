import TypedAsm.Program
import TypedAsm.Fn

/-!
# Tactics for typing programs

These build typing derivations; the kernel checks the result, so nothing here
is trusted. They handle the mechanical parts and leave as goals whatever
needs an argument, typically a fact about values at a branch.

* `ty_steps` types the straight-line instructions at the start of a block.
* `ty_accept h` shows the current context is accepted at an address, given
  the fact `h` that the code typing allows some context there.
* `ctx_sub` and `sub_regs` compare contexts.
-/

namespace TypedAsm

/-! ## Lemmas the tactics apply -/

/-- The slot a displacement addresses, computed from the displacement. -/
theorem slotDisp_of (disp : BitVec 32) (h8 : disp.toNat % 8 = 0) (hlt : disp.toNat < 2 ^ 31) :
    slotDisp (disp.toNat / 8) disp := by
  refine ⟨?_, by omega⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem getElem?_replicate_of_lt {n i : Nat} {τ : Ty} (h : i < n) :
    (List.replicate n τ)[i]? = some τ := by
  simp [h]

/-- Exact-value types are compared by comparing the values. -/
theorem Sub.of_eq {a b : BitVec 64} (h : a = b) : Sub (.eq a) (.eq b) :=
  h ▸ .refl _

theorem Flags.cf_isSome_of_known {f : Flags} (h : Flags.Known f) : f.cf.isSome = true := by
  simp only [Flags.Known, Flags.defined, Bool.and_eq_true] at h
  exact h.1.1.1

/-- When the flags are known, every condition is decided. -/
theorem Cond.decided_of_known {P : Flags → Prop} (hP : ∀ f, P f → Flags.Known f) (c : Cond) :
    ∀ f, P f → ∃ b, c.eval f = some b :=
  fun f hf => Cond.eval_some (hP f hf) c

/-! ## Comparing contexts -/

/-- Proves `Sub τ υ` when it holds for a structural reason. -/
macro "ty_sub" : tactic =>
  `(tactic| first
    | exact Sub.refl _
    | exact Sub.int _
    | exact Sub.readOnly _ _ _
    | exact Sub.of_eq (by first | assumption | rfl))

/-- Compares register types one register at a time. Registers it cannot
settle are left as goals. -/
macro "sub_regs" : tactic =>
  `(tactic| (intro r _; cases r <;> try ty_sub))

/-- Compares two stacks slot by slot. -/
macro "ty_stack" : tactic =>
  `(tactic| first
    | exact SubList.refl _
    | repeat (first | exact SubList.nil | refine SubList.cons (by ty_sub) ?_))

/-- Shows one flags predicate implies another, in the common cases. -/
macro "ty_flags" : tactic =>
  `(tactic| first
    | exact fun _ h => h
    | exact fun _ _ => trivial
    | (rintro f rfl; exact Flags.ofResult_defined _ _ _))

/-- Proves `CtxSub Γ Δ`. The stack, room and flags must be settled
automatically; register comparisons it cannot settle are left as goals. -/
macro "ctx_sub" : tactic =>
  `(tactic| (refine CtxSub.mk ?_ (by ty_stack) (by first | rfl | omega) (by ty_flags); sub_regs))

/-- `ty_accept h`, where `h : Φ a Δ`, proves `Accepts Φ a Γ` by comparing
`Γ` with `Δ`. Holes in `h` become goals. -/
macro "ty_accept " h:term : tactic =>
  `(tactic| (refine ⟨_, $h, ?sub⟩; case' sub => ctx_sub))

/-! ## Typing instructions -/

/-- Proves a field lookup `fields[i]? = some τ`. -/
macro "ty_field" : tactic =>
  `(tactic| first
    | rfl
    | exact getElem?_replicate_of_lt (by first | assumption | omega)
    | (simp [*]; done))

/-- Proves that an operation's need for the carry flag is met. -/
macro "ty_carry" : tactic =>
  `(tactic| first
    | exact fun h => absurd h (by decide)
    | exact fun _ _ hf => Flags.cf_isSome_of_known hf
    | (rintro - f rfl; rfl))

/-- Proves `Straight Γ i ?Γ'` for a known instruction `i`, choosing the most
informative rule that applies. -/
macro "ty_straight" : tactic =>
  `(tactic| first
    | exact Straight.nop
    | exact Straight.movRR64 (by decide) (by decide)
    | exact Straight.movRR32 (by decide)
    | exact Straight.movRI (by decide)
    | exact Straight.movAbs (by decide)
    | exact Straight.lea (by decide)
    | exact Straight.loadStack (by decide) (by rfl) (slotDisp_of _ (by decide) (by decide))
    | exact Straight.loadField (by decide) (by decide) rfl (by ty_field)
        (slotDisp_of _ (by decide) (by decide))
    | exact Straight.storeStack (by decide) (by first | decide | (simp; omega) | simp)
        (slotDisp_of _ (by decide) (by decide))
    | exact Straight.storeField (by decide) (by decide) rfl (by ty_field) (by ty_sub)
        (slotDisp_of _ (by decide) (by decide))
    | exact Straight.push (by decide) rfl
    | exact Straight.pop (by decide) rfl
    | exact Straight.aluExact (by decide) rfl rfl
    | exact Straight.addPtr (by decide) rfl (slotDisp_of _ (by decide) (by decide))
    | exact Straight.aluMem (by decide) (by decide) rfl (by ty_field)
        (slotDisp_of _ (by decide) (by decide)) (by ty_carry)
    | exact Straight.aluRR (by decide) (by ty_carry)
    | exact Straight.aluRI (by decide) (by ty_carry)
    | exact Straight.testExact (by decide) (by decide) rfl rfl
    | exact Straight.test)

/-- Types as many straight-line instructions as it can from the start of a
block, leaving the rest of the block as the goal. -/
macro "ty_steps" : tactic =>
  `(tactic| repeat (refine BlockOk.step rfl (by ty_straight) ?_))

end TypedAsm
