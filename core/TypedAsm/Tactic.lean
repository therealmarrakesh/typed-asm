import TypedAsm.Program
import TypedAsm.Fn

/-!
# Tactics for typing programs

These build typing derivations; the kernel checks the result, so nothing here
is trusted. They handle the mechanical parts and leave as goals whatever
needs an argument, typically a fact about values at a branch.

* `ty_steps` types the straight-line instructions at the start of a block.
* `ty_step` types one, and shows the instruction and context if it cannot.
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

/-- The slot and byte a displacement addresses, computed from the displacement. -/
theorem innerDisp_of (disp : BitVec 32) (hlt : disp.toNat < 2 ^ 31) :
    innerDisp (disp.toNat / 8) (disp.toNat % 8) disp := by
  refine ⟨?_, by omega⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- Releasing the top `k` stack slots, with the remaining stack computed. -/
theorem Straight.freeFrame' {Γ : Ctx} {k : Nat} {imm : BitVec 32} (hk : slotDisp k imm)
    (hlen : (Γ.stack.take k).length = k) :
    Straight Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm))
      { Γ with stack := Γ.stack.drop k, room := Γ.room + k, flags := Flags.Known } :=
  .freeFrame hk (List.take_append_drop k _).symm hlen

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

/-! ## Comparing contexts

A note on how these are written. A side condition is never proved by a
nested `by` inside a term: when such a block fails, Lean logs the error and
carries on, so a `first` would not move on to its next alternative. Instead
each side condition becomes a goal and is proved by a following tactic. -/

/-- Proves `Sub τ υ` when it holds for a structural reason. -/
macro "ty_sub" : tactic =>
  `(tactic| first
    | exact Sub.refl _
    | exact Sub.int _
    | exact Sub.readOnly _ _ _
    | (refine Sub.of_eq ?_; first | assumption | rfl))

/-- Compares register types one register at a time. Registers it cannot
settle are left as goals. -/
macro "sub_regs" : tactic =>
  `(tactic| (intro r _; cases r <;> try ty_sub))

/-- Compares two stacks slot by slot. -/
macro "ty_stack" : tactic =>
  `(tactic| first
    | exact SubList.refl _
    | (repeat (first | exact SubList.nil | (refine SubList.cons ?_ ?_; ty_sub)); done))

/-- Shows one flags predicate implies another, in the common cases. -/
macro "ty_flags" : tactic =>
  `(tactic| first
    | exact fun _ h => h
    | exact fun _ _ => trivial
    | (rintro f rfl; exact Flags.ofResult_defined _ _ _))

/-- Proves `CtxSub Γ Δ`. The stack, room and flags must be settled
automatically; register comparisons it cannot settle are left as goals. -/
macro "ctx_sub" : tactic =>
  `(tactic| (
    refine CtxSub.mk ?regs ?stack ?room ?flags
    case stack => ty_stack
    case room => first | rfl | omega
    case flags => ty_flags
    sub_regs))

/-- `ty_accept h`, where `h : Φ a Δ`, proves `Accepts Φ a Γ` by comparing
`Γ` with `Δ`. Holes in `h` become goals. -/
macro "ty_accept " h:term : tactic =>
  `(tactic| (refine ⟨_, $h, ?sub⟩; case' sub => ctx_sub))

/-! ## Typing instructions -/

/-- Proves a field lookup `fields[i]? = some τ`. -/
macro "ty_field" : tactic =>
  `(tactic| first
    | rfl
    | (refine getElem?_replicate_of_lt ?_
       first | assumption | omega | (simp; first | assumption | omega))
    | (simp [*]; done))

/-- Proves that an operation's need for the carry flag is met. -/
macro "ty_carry" : tactic =>
  `(tactic| first
    | (intro h; exact absurd h (by decide))
    | exact fun _ _ hf => Flags.cf_isSome_of_known hf
    | (rintro - f rfl; rfl))

/-- Proves a side condition of a typing rule, or fails. -/
macro "ty_side" : tactic =>
  `(tactic| first
    | rfl
    | decide
    | (refine slotDisp_of _ ?_ ?_ <;> decide)
    | (refine innerDisp_of _ ?_ <;> decide)
    | ty_field
    | ty_sub
    | ty_carry)

/-- Applies one typing rule and proves all its premises, or fails. The
premises are attempted in order and then again, because proving one can
determine what an earlier one refers to. -/
macro "ty_rule " r:term : tactic =>
  `(tactic| (((refine' $r .. <;> try ty_side) <;> try ty_side); done))

/-- Proves `Straight Γ i ?Γ'` for a known instruction `i`, choosing the most
informative rule that applies. -/
macro "ty_straight" : tactic =>
  `(tactic| first
    | exact Straight.nop
    | ty_rule Straight.movRR64
    | ty_rule Straight.movRR32
    | ty_rule Straight.movRI
    | ty_rule Straight.movAbs
    | ty_rule Straight.lea
    | ty_rule Straight.loadStack
    | ty_rule Straight.loadField
    | ty_rule Straight.storeStack
    | ty_rule Straight.storeField
    | ty_rule Straight.push
    | ty_rule Straight.pop
    | ty_rule Straight.allocFrame
    | ty_rule Straight.freeFrame'
    | ty_rule Straight.aluExact
    | ty_rule Straight.aluExactRR
    | ty_rule Straight.loadField32
    | ty_rule Straight.movzxField
    | ty_rule Straight.movsxField
    | ty_rule Straight.addPtr
    | ty_rule Straight.aluMem
    | ty_rule Straight.aluRR
    | ty_rule Straight.aluRI
    | ty_rule Straight.testExact
    | exact Straight.test)

/-- Simplifies the context in a block goal. Each rule wraps the previous
context in a record update that mentions it once per field, so without this
the context would multiply in size with every instruction. -/
macro "ty_normalize" : tactic =>
  `(tactic| try dsimp only [CtxOf.setReg, CtxOf.afterAlu, CtxOf.afterSyscall, AluOp.writesDst,
      ↓reduceIte])

/-- Types one straight-line instruction. If no rule applies, the goal that is
left shows the instruction and the context, which is the place to look when
`ty_steps` stops earlier than expected. -/
macro "ty_step" : tactic =>
  `(tactic| (refine BlockOk.step (Γ' := ?_) rfl ?instruction ?_
             case' instruction => try ty_straight
             all_goals ty_normalize))

/-- Types as many straight-line instructions as it can from the start of a
block, leaving the rest of the block as the goal. -/
macro "ty_steps" : tactic =>
  `(tactic| repeat (refine BlockOk.step (Γ' := ?_) rfl ?instruction ?_
                    case instruction => ty_straight
                    ty_normalize))

end TypedAsm
