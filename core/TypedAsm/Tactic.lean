import Lean
import TypedAsm.Program
import TypedAsm.Fn
import TypedAsm.Print
import TypedAsm.Blocks
import TypedAsm.Linux

/-!
# Tactics for typing programs

These build typing derivations; the kernel checks the result, so nothing here
is trusted. They handle the mechanical parts and leave as goals whatever
needs an argument, typically a fact about values at a branch.

* `ty_block` types a whole block of a labelled program, finding jump targets
  by label. `ty_call sig` types a call. These are the usual entry points.
* `ty_steps` types the straight-line instructions at the start of a block.
* `ty_step` types one. `ty_step_with r` types one with a rule you name.
* `ty_branch` types a conditional jump and leaves the side that carries on.
* `ty_straight` types a single instruction; the two above are built on it.
* `ty_name r as v` gives the value in a register a name; `ty_name_slot i as v`
  does the same for a stack slot.
* `ty_open r` and `ty_null r` open a pointer to a kind of block and
  split a value that may be null.
* `ty_mmap fields` and `ty_mmap_kind tag` type an `mmap` for fresh memory;
  `ty_err r as e` then splits what it handed back into an error number and
  a pointer.
* `ty_fn_ptr r to sig` turns a register holding a function's address into a
  pointer to that function.
* `ty_code_ptr r to Δ` turns a register holding a label's address into a
  code pointer, for indirect jumps and calls.
* `ty_accept h` shows the current context is accepted at an address, given
  the fact `h` that the code typing allows some context there.
* `ty_into h` types one instruction and ends the block there, handing over
  to the label that follows.
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
theorem Straight.freeFrame' {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {k : Nat} {imm : BitVec 32}
    (hk : slotDisp k imm) (hlen : (Γ.stack.take k).length = k) :
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm))
      { Γ.moveSp (BitVec.ofNat 64 (8 * k)) with
        stack := Γ.stack.drop k, room := Γ.room + k, flags := Flags.Known } :=
  .freeFrame hk (List.take_append_drop k _).symm hlen

/-! Operands at a fixed address. Which block the address falls in, and where,
is found by computation: the first premise of each lemma below is there only
to be solved by `rfl`, which determines the block, the field and the byte. -/

/-- The block among `bs` that contains address `a`, with the field and the
byte within the field that `a` is at. -/
def MemTy.locate (bs : List (BitVec 64 × Layout)) (a : BitVec 64) :
    Option (BitVec 64 × Nat × Nat) :=
  bs.findSome? fun x =>
    if (a - x.1).toNat < x.2.size then some (x.1, (a - x.1).toNat / 8, (a - x.1).toNat % 8)
    else none

section Globals

variable {bs : List (BitVec 64 × Layout)} {kinds : List (Nat × List Ty)} {next base : BitVec 64}
  {Γ : Ctx} {l : Layout} {i k n : Nat} {disp : BitVec 32} {τ : Ty}

theorem ReadOk.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, i, k))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i + k))
    (hi : l.fields[i]? = some τ) (hk : k + n ≤ 8) :
    ReadOk (MemTy.ofList bs kinds) next Γ n (.mem (.rip disp)) :=
  .global hl haddr hi hk

theorem WriteIntOk.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, i, k))
    (hl : MemTy.ofList bs kinds base = some l) (hw : l.writable = true)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i + k))
    (hi : l.fields[i]? = some .int) (hk : k + n ≤ 8) :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n (.mem (.rip disp)) Γ :=
  .global hl hw haddr hi hk

theorem Holds.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, i, 0))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i))
    (hi : l.fields[i]? = some τ) :
    Holds (MemTy.ofList bs kinds) next Γ (.mem (.rip disp)) τ :=
  .global hl haddr hi

theorem Straight.loadGlobal_of {d : Reg} (hd : d ≠ .rsp)
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, i, 0))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i))
    (hi : l.fields[i]? = some τ) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.r_m d (.rip disp))) (Γ.setReg d τ) :=
  .loadGlobal hd hl haddr hi

theorem Straight.storeGlobal_of {s : Reg} (hs : s ≠ .rsp)
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, i, 0))
    (hl : MemTy.ofList bs kinds base = some l) (hw : l.writable = true)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 (8 * i))
    (hi : l.fields[i]? = some τ) (hsub : Sub (Γ.regs s) τ) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.rm_r (.mem (.rip disp)) s)) Γ :=
  .storeGlobal hs hl hw haddr hi hsub

end Globals

/-! Indexed operands: which field and byte a scaled index lands on. These
hold for any index, since addresses wrap; what needs a bound on the index is
the field being inside the block. -/

theorem sext_toNat {disp : BitVec 32} (hd : disp.toNat < 2 ^ 31) :
    disp.signExtend 64 = BitVec.ofNat 64 disp.toNat := by
  have h := sext_small hd
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

/-- An index scaled by 8 with a displacement that is a multiple of 8
addresses a whole field. -/
theorem index8_slot (c : BitVec 64) (disp : BitVec 32)
    (h8 : disp.toNat % 8 = 0) (hd : disp.toNat < 2 ^ 31) :
    (c <<< Scale.s8.shift) + disp.signExtend 64
      = BitVec.ofNat 64 (8 * (c.toNat + disp.toNat / 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Scale.shift]
  omega

/-- An index scaled by 8, with any displacement. -/
theorem index8 (c : BitVec 64) (disp : BitVec 32) (hd : disp.toNat < 2 ^ 31) :
    (c <<< Scale.s8.shift) + disp.signExtend 64
      = BitVec.ofNat 64 (8 * (c.toNat + disp.toNat / 8) + disp.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Scale.shift]
  omega

/-- An index with any scale: the field and byte are those of the byte offset. -/
theorem index_any (c : BitVec 64) (sc : Scale) (disp : BitVec 32) (hd : disp.toNat < 2 ^ 31) :
    (c <<< sc.shift) + disp.signExtend 64
      = BitVec.ofNat 64 (8 * ((c.toNat * 2 ^ sc.shift + disp.toNat) / 8)
          + (c.toNat * 2 ^ sc.shift + disp.toNat) % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize c.toNat * 2 ^ sc.shift = m
  omega

/-- After `cmp a, b`, "below" holds exactly when `a` is less than `b` as
unsigned numbers. This is the fact a bounds check establishes. -/
theorem cmp_below_iff (a b : BitVec 64) :
    Cond.eval (AluOp.apply .cmp a b).2 .b = some (decide (a.toNat < b.toNat)) := by
  have h := subBorrow_cf .w64 a b
  simp only [AluOp.apply, Cond.eval]
  rw [h]
  rfl

theorem cmp_below {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .b = some true) :
    a.toNat < b.toNat := by
  rw [cmp_below_iff] at h
  simpa using h

theorem cmp_not_below {a b : BitVec 64}
    (h : Cond.eval (AluOp.apply .cmp a b).2 .b = some false) : b.toNat ≤ a.toNat := by
  rw [cmp_below_iff] at h
  simpa using h

/-- After `cmp a, b`, "less" holds exactly when `a` is less than `b` as
signed numbers. -/
theorem cmp_less_iff (a b : BitVec 64) :
    Cond.eval (AluOp.apply .cmp a b).2 .l = some (a.slt b) := by
  simp only [AluOp.apply, Cond.eval, subBorrow, Flags.ofResult, bind, Option.bind, pure,
    Option.some.injEq]
  bv_decide

theorem cmp_less {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .l = some true) :
    a.slt b = true := by
  rw [cmp_less_iff] at h
  simpa using h

theorem cmp_not_less {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .l = some false) :
    a.slt b = false := by
  rw [cmp_less_iff] at h
  simpa using h

theorem getElem?_replicate_of_lt {n i : Nat} {τ : Ty} (h : i < n) :
    (List.replicate n τ)[i]? = some τ := by
  simp [h]

/-- Exact-value types are compared by comparing the values. -/
theorem Sub.of_eq {a b : BitVec 64} (h : a = b) : Sub (.eq a) (.eq b) :=
  h ▸ .refl _

/-- An unsigned divide whose dividend has a zero upper half and whose divisor
is known not to be zero cannot raise a divide error. -/
theorem Straight.divSafe {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {w : Width} {r : Reg}
    {a d b : BitVec 64} (hr : r ≠ .rsp) (hΓa : Γ.regs .rax = .eq a) (hΓd : Γ.regs .rdx = .eq d)
    (hΓr : Γ.regs r = .eq b) (hd : d.setWidth w.bits = 0) (hb : b.setWidth w.bits ≠ 0) :
    Straight Ψ next Γ (.mulDiv .div w (.reg r))
      { (Γ.setReg .rax (.eq ((a.setWidth w.bits / b.setWidth w.bits).setWidth 64))).setReg .rdx
          (.eq ((a.setWidth w.bits % b.setWidth w.bits).setWidth 64)) with
        flags := (· = Flags.unknown) } :=
  .mulDivExact hr hΓa hΓd hΓr (by rw [hd]; exact MulDivOp.eval_div _ _ hb)

/-- A signed divide whose dividend has been sign-extended into `rdx` (as
`cqo` and `cdq` do) and whose divisor is known not to be zero cannot raise a
divide error, unless it is the most negative number divided by minus one. -/
theorem Straight.idivSafe {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {w : Width} {r : Reg}
    {a d b : BitVec 64} (hr : r ≠ .rsp) (hΓa : Γ.regs .rax = .eq a) (hΓd : Γ.regs .rdx = .eq d)
    (hΓr : Γ.regs r = .eq b) (hd : d.setWidth w.bits = signFill (a.setWidth w.bits))
    (hb : b.setWidth w.bits ≠ 0)
    (hov : a.setWidth w.bits ≠ BitVec.intMin w.bits ∨ b.setWidth w.bits ≠ -1#w.bits) :
    Straight Ψ next Γ (.mulDiv .idiv w (.reg r))
      { (Γ.setReg .rax (.eq (((a.setWidth w.bits).sdiv (b.setWidth w.bits)).setWidth 64))).setReg
          .rdx (.eq (((a.setWidth w.bits).srem (b.setWidth w.bits)).setWidth 64)) with
        flags := (· = Flags.unknown) } :=
  .mulDivExact hr hΓa hΓd hΓr (by rw [hd]; exact MulDivOp.eval_idiv _ _ hb hov)

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
syntax "ty_sub" : tactic

/-- A `Sub` goal restated with both types reduced to their outermost form,
and whether both are exactly known values. Comparing the reduced types
keeps the comparison from wandering into whatever the unreduced ones
mention along the way. -/
private def headForm? (g : Lean.MVarId) : Lean.Meta.MetaM (Option (Lean.MVarId × Bool)) :=
  g.withContext do
    let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
    unless t.isAppOfArity ``Sub 2 do return none
    let a ← Lean.Meta.whnf t.appFn!.appArg!
    let b ← Lean.Meta.whnf t.appArg!
    let g' ← g.change (Lean.mkApp2 (Lean.mkConst ``Sub) a b)
    return some (g', a.isAppOfArity ``Ty.eq 1 && b.isAppOfArity ``Ty.eq 1)

open Lean Meta Elab Tactic in
/-- Compares two exactly known values. They are never compared by unfolding
arithmetic, which runs away when a variable has a large constant added to
it: values with no variables in them are compared by computing, and others
as written, then from the hypotheses, then by bit-vector arithmetic. -/
elab "ty_sub_exact" : tactic => do
  let some (g, true) ← headForm? (← getMainGoal) | throwError "not two exactly known values"
  let t ← g.getType
  let closed := !(t.hasFVar || t.hasExprMVar)
  replaceMainGoal [g]
  if closed then
    evalTactic (← `(tactic| (refine Sub.of_eq ?_; first | rfl | decide)))
  else
    -- Constants added one after another are first added up, so that a value
    -- moved down and back up is seen to be the value it was.
    evalTactic (← `(tactic|
      try simp only [BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero]))
    evalTactic (← `(tactic| first
      | (with_reducible exact Sub.refl _)
      | (refine Sub.of_eq ?_; first | assumption | bv_omega)))

open Lean Meta Elab Tactic in
/-- Restates the goal with both types in their outermost form. Fails when
both are exactly known values, which `ty_sub_exact` owns. -/
elab "ty_sub_other" : tactic => do
  match ← headForm? (← getMainGoal) with
  | some (_, true) => throwError "two exactly known values"
  | some (g, false) => replaceMainGoal [g]
  | none => pure ()

macro_rules
  | `(tactic| ty_sub) =>
    `(tactic| first
      | ty_sub_exact
      | (ty_sub_other
         first
         | exact Sub.refl _
         | exact Sub.int _
         | exact Sub.readOnly _ _ _
         | exact Sub.refReadOnly _ _ _
         | exact Sub.null _
         | (refine Sub.nullableMono ?_; ty_sub)
         | (refine Sub.nullable ?_; ty_sub)
         | (refine Sub.orErrMono ?_; ty_sub)
         | (refine Sub.orErr ?_; ty_sub)
         -- the stack pointer's type after moves that cancel or add up
         | (simp only [Ty.shift_shift]
            first | exact Sub.refl _ | (refine Sub.shift_congr ?_; decide))))

/-- Compares register types one register at a time. Registers it cannot
settle are left as goals. -/
macro "sub_regs" : tactic =>
  `(tactic| (intro r hr; cases r <;> first | exact absurd rfl hr | (try ty_sub)))

/-- Compares two stacks slot by slot. -/
macro "ty_stack" : tactic =>
  `(tactic| first
    | exact SubList.refl _
    | ((repeat (first | exact SubList.nil | (refine SubList.cons ?_ ?_; ty_sub))); done))

/-- Shows one flags predicate implies another, in the common cases. -/
macro "ty_flags" : tactic => do
  -- `rfl` must be written without macro hygiene, or `rintro` takes it for a name.
  let subst := Lean.mkIdent `rfl
  `(tactic| first
    | exact fun _ h => h
    | exact fun _ _ => trivial
    | (rintro f $subst:ident; exact Flags.ofResult_defined _ _ _))

/-- Proves `CtxSub Γ Δ`. The stack, room and flags must be settled
automatically; register comparisons it cannot settle are left as goals. -/
macro "ctx_sub" : tactic =>
  `(tactic| (
    refine CtxSub.mk ?regs ?stack ?room ?flags ?sp
    case stack => ty_stack
    case room => first | rfl | omega
    case flags => ty_flags
    case sp => ty_sub
    sub_regs))

/-- `ty_accept h` proves `Accepts Φ a Γ` by comparing `Γ` with a context `Δ`
that is allowed at `a`. The fact `h` is either `Φ a Δ` itself or, for a
labelled program, a statement that `Δ` is allowed at the label whose address
is `a`. Holes in `h` become goals. -/
macro "ty_accept " h:term : tactic =>
  `(tactic| ((first | refine ⟨_, $h, ?sub⟩ | refine ⟨_, CodeTy.ofLabels.intro $h, ?sub⟩);
             case' sub => ctx_sub))

/-! ## Typing instructions -/

/-- Proves a field lookup `fields[i]? = some τ`. -/
macro "ty_field" : tactic =>
  `(tactic| first
    | rfl
    | (refine getElem?_replicate_of_lt ?_
       first | assumption | omega | (simp; first | assumption | omega))
    | (simp [*]; done))

/-- Proves that an operation's need for the carry flag is met. -/
macro "ty_carry" : tactic => do
  let subst := Lean.mkIdent `rfl
  `(tactic| first
    | (intro h; exact absurd h (by decide))
    | exact fun _ _ hf => Flags.cf_isSome_of_known hf
    | (rintro - f $subst:ident; rfl))

/-- Proves that the flags decide a condition. -/
macro "ty_decided" : tactic => do
  let subst := Lean.mkIdent `rfl
  `(tactic| first
    | exact Cond.decided_of_known (fun _ h => h) _
    | (rintro f $subst:ident; exact ⟨_, rfl⟩)
    | (refine Cond.decided_of_defined _ ?_; decide))

/-- Proves that exactly known flags give a condition a particular answer. -/
macro "ty_cond_value" : tactic => do
  let subst := Lean.mkIdent `rfl
  `(tactic| (rintro f $subst:ident; rfl))

/-- Proves which field and byte a scaled index lands on. -/
macro "ty_index" : tactic =>
  `(tactic| first
    | (refine index8_slot _ _ ?_ ?_ <;> decide)
    | (refine index8 _ _ ?_; decide)
    | (refine index_any _ _ _ ?_; decide))

/-- Proves a fact with no unknowns in it from the hypotheses: the fact
itself, or one side of an "or". A goal with unknowns is refused, since a
hypothesis of the right shape would settle them whether or not it was the
one meant. -/
syntax "ty_known" : tactic

/-- Proves a side condition of a typing rule, or fails. -/
syntax "ty_side" : tactic

/-- Applies one typing rule and proves all its premises, or fails. The
premises are attempted in order and then again, because proving one can
determine what an earlier one refers to. -/
syntax "ty_rule " term : tactic

/-- Like `ty_rule`, but proves the premises strictly in order and gives up
at the first that fails. For rules whose first premise computes what the
others refer to, where carrying on after a failure would be slow. -/
syntax "ty_rule_ordered " term : tactic

/-- Proves that an operand can be read, can be written, or holds a value of
a given type: it is a register, a stack slot, a field of a pointer, or a field
of a block at a fixed address. -/
macro "ty_operand" : tactic =>
  `(tactic| first
    | ty_rule_ordered ReadOk.reg | ty_rule_ordered ReadOk.slot | ty_rule_ordered ReadOk.field
    | ty_rule_ordered ReadOk.indexed | ty_rule_ordered ReadOk.global_of
    | ty_rule_ordered WriteIntOk.reg | ty_rule_ordered WriteIntOk.slot
    | ty_rule_ordered WriteIntOk.field | ty_rule_ordered WriteIntOk.indexed
    | ty_rule_ordered WriteIntOk.global_of
    | ty_rule_ordered Holds.reg | ty_rule_ordered Holds.slot | ty_rule_ordered Holds.field
    | ty_rule_ordered Holds.indexed | ty_rule_ordered Holds.global_of)

macro_rules
  | `(tactic| ty_side) =>
    `(tactic| first
      | rfl
      | decide
      | (refine slotDisp_of _ ?_ ?_ <;> decide)
      | (refine innerDisp_of _ ?_ <;> decide)
      | ty_field
      | ty_sub
      | ty_carry
      | ty_decided
      | ty_cond_value
      | ty_index
      | ty_known
      | ty_operand)

macro_rules
  | `(tactic| ty_rule $r) =>
    `(tactic| (((refine' $r .. <;> try ty_side) <;> try ty_side); done))

/-- Simplifies the context in a block goal. Each rule wraps the previous
context in a record update that mentions it once per field, so without this
the context would multiply in size with every instruction. -/
macro "ty_normalize" : tactic =>
  `(tactic| try dsimp only [CtxOf.setReg, CtxOf.moveSp, Ty.shift, CtxOf.afterAlu, CtxOf.afterSyscall,
      CtxOf.afterMulDiv,
      ShiftOp.apply, Scale.shift,
      ShiftOp.flagsAfter, Width.bits, Nat.reduceEqDiff, Nat.reduceBEq, ↓reduceIte,
      AluOp.writesDst, List.set_cons_zero, List.set_cons_succ,
      Bool.cond_true, Bool.cond_false, Nat.add_zero, Nat.zero_add, BitVec.reduceToNat, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul])

/-- `ty_name r as v`: from here on, the value in register `r` is called `v`
and the register is typed as exactly `v`. Use it on a register typed as an
integer, for example one just loaded from memory, before testing it or
computing with it, so that what is learnt about the value can be used. -/
syntax "ty_name " term " as " ident : tactic

syntax "ty_name_slot " term " as " ident : tactic
syntax "ty_open " term : tactic
syntax "ty_null " term : tactic
syntax "ty_err " term " as " ident : tactic
syntax "ty_mmap " term : tactic
syntax "ty_mmap_kind " term : tactic
syntax "ty_into " term : tactic

/-! ## Choosing the rule from the instruction

The tactics below are metaprograms. They look at the instruction, try only
the rules written for its shape, and when none applies they say which
premise of each stood in the way. -/

open Lean Meta Elab Tactic

elab_rules : tactic
  | `(tactic| ty_known) => withMainContext do
    let ty ← instantiateMVars (← (← getMainGoal).getType)
    if ty.hasExprMVar then throwError "ty_known: the goal has unknowns"
    -- A goal that asks for a value, not a fact, is never settled this way.
    unless ← isProp ty do throwError "ty_known: the goal is not a proposition"
    evalTactic (← `(tactic| first
      | assumption
      | (refine Or.inl ?_; first | assumption | decide)
      | (refine Or.inr ?_; first | assumption | decide)))

elab_rules : tactic
  | `(tactic| ty_rule_ordered $r) => Tactic.withoutRecover do
    evalTactic (← `(tactic| refine' $r ..))
    for g in ← getGoals do
      if ← g.isAssigned then continue
      unless ← isProp (← g.getType) do continue
      setGoals [g]
      evalTactic (← `(tactic| ty_side))
      unless (← getUnsolvedGoals).isEmpty do throwError "premise not proved"
    setGoals []

/-- Gives the value in a register a name, on the main goal, which must be a block. -/
def nameRegister (r : Term) (v : Ident) : TacticM Unit := do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  setGoals [goal]
  -- the stack pointer has a rule of its own
  let saved ← saveState
  let rest? ← try
      evalTactic (← `(tactic| refine BlockOk.name (r := $r) ?_ ?_))
      let mut rest? : Option MVarId := none
      for g in ← getGoals do
        let t ← instantiateMVars (← g.getType)
        if t.isAppOf ``Ne then
          setGoals [g]
          evalTactic (← `(tactic| decide))
        else rest? := some g
      pure rest?
    catch _ =>
      saved.restore
      setGoals [goal]
      evalTactic (← `(tactic| refine BlockOk.nameSp (Γ := ?_) ?_))
      pure (← getGoals).head?
  let some rest := rest? | throwError "ty_name: unexpected goals"
  setGoals [rest]
  evalTactic (← `(tactic| (intro $v:ident; ty_normalize)))
  setGoals ((← getGoals) ++ others)

elab_rules : tactic
  | `(tactic| ty_name $r as $v) => nameRegister r v

/-- Applies a rule that turns the main block goal into one or more block
goals, proving its side condition that a register is not `rsp`. The new
block goals come back simplified and in order. -/
def refineBlocks (tac : TSyntax `tactic) : TacticM Unit := do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  setGoals [goal]
  evalTactic tac
  let mut blocks : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then
      setGoals [g]
      evalTactic (← `(tactic| ty_normalize))
      blocks := blocks ++ (← getGoals)
    else
      setGoals [g]
      evalTactic (← `(tactic| decide))
  setGoals (blocks ++ others)

/-- `ty_name_slot i as v`: from here on, the value in stack slot `i` is
called `v` and the slot is typed as exactly `v`. -/
elab_rules : tactic
  | `(tactic| ty_name_slot $i as $v) => do
    let goal ← getMainGoal
    let others := (← getGoals).drop 1
    setGoals [goal]
    evalTactic (← `(tactic| refine BlockOk.nameSlot (i := $i) ?_ ?_))
    let mut rest? : Option MVarId := none
    for g in ← getGoals do
      let t ← instantiateMVars (← g.getType)
      if t.isForall then rest? := some g
      else
        setGoals [g]
        try
          evalTactic (← `(tactic| first | decide | (simp; done) | omega))
        catch _ => throwError "ty_name_slot: there is no such stack slot here"
    let some rest := rest? | throwError "ty_name_slot: unexpected goals"
    setGoals [rest]
    evalTactic (← `(tactic| (intro $v:ident; ty_normalize)))
    setGoals ((← getGoals) ++ others)

/-- `ty_open r`: register `r` holds a pointer to a block of some kind. From
here on `r` is an ordinary pointer to the fields the memory typing lists for
that kind, which can be loaded from and stored to. -/
elab_rules : tactic
  | `(tactic| ty_open $r) => do
    refineBlocks (← `(tactic| refine BlockOk.openRef (r := $r) ?_ rfl rfl ?_))

/-- `ty_null r`: register `r` holds a value that may be null. Two goals
follow: the rest of the block with `r` exactly zero, then with `r` a value
of the type itself. A test of `r` then decides in each which way it goes. -/
elab_rules : tactic
  | `(tactic| ty_null $r) => do
    refineBlocks (← `(tactic| refine BlockOk.splitNull (r := $r) ?_ rfl ?_ ?_))

/-- `ty_err r as e`: register `r` holds what a system call handed back, an
error number or a value. Two goals follow: the rest of the block with `r`
exactly an error number `e`, then with `r` a value of the type itself. A
test of `r` then decides in the first which way it goes. -/
elab_rules : tactic
  | `(tactic| ty_err $r as $e) => do
    let goal ← getMainGoal
    let others := (← getGoals).drop 1
    setGoals [goal]
    evalTactic (← `(tactic| refine BlockOk.splitErr (r := $r) ?_ rfl ?_ ?_))
    let mut blocks : List MVarId := []
    for g in ← getGoals do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      setGoals [g]
      if t.isAppOf ``BlockOk then
        evalTactic (← `(tactic| ty_normalize))
        blocks := blocks ++ (← getGoals)
      else if t.isForall then
        evalTactic (← `(tactic| (intro $e:ident herr; ty_normalize)))
        blocks := blocks ++ (← getGoals)
      else
        evalTactic (← `(tactic| decide))
    setGoals (blocks ++ others)

/-- The rules whose premises are proved in order, stopping at the first that
fails: those for operands, whose premises each depend on the ones before. -/
def orderedRules : List Name := [``Straight.loadGlobal_of, ``Straight.storeGlobal_of,
  ``ReadOk.reg, ``ReadOk.slot, ``ReadOk.field, ``ReadOk.indexed, ``ReadOk.global_of,
  ``WriteIntOk.reg, ``WriteIntOk.slot, ``WriteIntOk.field, ``WriteIntOk.indexed,
  ``WriteIntOk.global_of, ``Holds.reg, ``Holds.slot, ``Holds.field, ``Holds.indexed,
  ``Holds.global_of]

/-- The straight-line rules that can type an instruction of this shape, most
informative first. An empty list means the type system has no rule for it. -/
def Instr.rules : Instr → List Name
  | .nop => [``Straight.nop]
  -- moves between registers and constants
  | .mov .w64 (.rm_r (.reg _) _) => [``Straight.movRR64]
  | .mov .w32 (.rm_r (.reg _) _) => [``Straight.mov32Exact, ``Straight.movRR32]
  | .mov _ (.rm_i (.reg _) _) => [``Straight.movRI]
  | .movAbs _ _ => [``Straight.movAbs]
  | .lea .w64 _ (.rip _) => [``Straight.leaRip, ``Straight.lea]
  | .lea .w64 _ (.sib (some .rsp) none _) => [``Straight.leaSp, ``Straight.lea]
  | .lea .w64 _ (.sib (some _) none _) => [``Straight.leaExactB, ``Straight.lea]
  | .lea .w64 _ (.sib (some _) (some _) _) => [``Straight.leaExactBI, ``Straight.lea]
  | .lea _ _ _ => [``Straight.lea]
  -- loads: a whole slot or field keeps its type, anything else is an integer
  | .mov .w64 (.r_m _ (.sib (some .rsp) none _)) => [``Straight.loadStack]
  | .mov .w64 (.r_m _ (.sib (some _) none _)) => [``Straight.loadField]
  | .mov .w64 (.r_m _ (.rip _)) => [``Straight.loadGlobal_of]
  | .mov .w64 (.r_m _ (.sib (some _) (some _) _)) => [``Straight.loadIndexed, ``Straight.loadInt]
  | .mov _ (.r_m _ _) => [``Straight.loadInt]
  | .movzx _ _ _ (.reg _) => [``Straight.movzxExact, ``Straight.movzxRM]
  | .movzx _ _ _ _ => [``Straight.movzxRM]
  | .movsx _ _ _ (.reg _) => [``Straight.movsxExact, ``Straight.movsxRM]
  | .movsx _ _ _ _ => [``Straight.movsxRM]
  | .movsxd _ (.reg _) => [``Straight.movsxdExact, ``Straight.movsxdRM]
  | .movsxd _ _ => [``Straight.movsxdRM]
  -- stores
  | .mov .w64 (.rm_r (.mem (.sib (some .rsp) none _)) _) => [``Straight.storeStack]
  | .mov .w64 (.rm_r (.mem (.sib (some _) none _)) _) =>
    [``Straight.storeField, ``Straight.storeInt]
  | .mov .w64 (.rm_r (.mem (.rip _)) _) => [``Straight.storeGlobal_of, ``Straight.storeInt]
  | .mov .w64 (.rm_r (.mem (.sib (some _) (some _) _)) _) =>
    [``Straight.storeIndexed, ``Straight.storeInt]
  | .mov _ (.rm_r (.mem _) _) => [``Straight.storeInt]
  | .mov _ (.rm_i (.mem _) _) => [``Straight.storeImm]
  | .store8 _ _ => [``Straight.store8RM]
  | .store16 _ _ => [``Straight.store16RM]
  | .push _ => [``Straight.push]
  | .pop _ => [``Straight.pop]
  -- arithmetic
  | .alu .sub .w64 (.rm_i (.reg .rsp) _) => [``Straight.allocFrame]
  | .alu .add .w64 (.rm_i (.reg .rsp) _) => [``Straight.freeFrame']
  | .alu _ .w64 (.rm_i (.reg _) _) => [``Straight.aluExact, ``Straight.addPtr, ``Straight.aluRI]
  | .alu _ _ (.rm_i (.reg _) _) => [``Straight.aluExact32, ``Straight.aluRI]
  | .alu .xor w (.rm_r (.reg d) s) =>
    -- `xor r, r` clears `r` whatever it held
    if d = s then [``Straight.xorSelf]
    else match w with
      | .w64 => [``Straight.aluExactRR, ``Straight.aluRR]
      | .w32 => [``Straight.aluExactRR32, ``Straight.aluRR]
  | .alu _ .w64 (.rm_r (.reg _) _) => [``Straight.aluExactRR, ``Straight.aluRR]
  | .alu _ _ (.rm_r (.reg _) _) => [``Straight.aluExactRR32, ``Straight.aluRR]
  | .alu _ _ (.r_m _ _) => [``Straight.aluLoad]
  | .alu op _ (.rm_r (.mem _) _) =>
    if op.writesDst then [``Straight.aluStoreR] else [``Straight.cmpR]
  | .alu op _ (.rm_i (.mem _) _) =>
    if op.writesDst then [``Straight.aluStoreI] else [``Straight.cmpI]
  | .test .w64 (.reg _) (.reg _) => [``Straight.testExact, ``Straight.testRM]
  | .test _ _ _ => [``Straight.testRM]
  | .unary .neg _ (.reg _) => [``Straight.negExact, ``Straight.negRM]
  | .unary .neg _ _ => [``Straight.negRM]
  | .unary .not _ (.reg _) => [``Straight.notExact, ``Straight.notRM]
  | .unary .not _ _ => [``Straight.notRM]
  | .shift _ _ (.reg _) (.imm _) => [``Straight.shiftExact, ``Straight.shiftImm]
  | .shift _ _ _ (.imm _) => [``Straight.shiftImm]
  | .shift _ _ _ .cl => [``Straight.shiftCl]
  | .mulDiv .mul _ (.reg _) => [``Straight.mulDivExact, ``Straight.mulRM]
  | .mulDiv .mul _ _ => [``Straight.mulRM]
  | .mulDiv .imul _ (.reg _) => [``Straight.mulDivExact, ``Straight.imulRM]
  | .mulDiv .imul _ _ => [``Straight.imulRM]
  -- a divide is typed only when shown not to raise a divide error
  | .mulDiv .div _ (.reg _) => [``Straight.mulDivExact, ``Straight.divSafe]
  | .mulDiv .idiv _ (.reg _) => [``Straight.mulDivExact, ``Straight.idivSafe]
  | .imul2 _ _ (.reg _) => [``Straight.imul2Exact, ``Straight.imul2RM]
  | .imul2 _ _ _ => [``Straight.imul2RM]
  | .imul3 _ _ (.reg _) _ => [``Straight.imul3Exact, ``Straight.imul3RM]
  | .imul3 _ _ _ _ => [``Straight.imul3RM]
  | .popcnt _ _ (.reg _) => [``Straight.popcntExact, ``Straight.popcntRM]
  | .popcnt _ _ _ => [``Straight.popcntRM]
  | .bswap _ _ => [``Straight.bswapExact, ``Straight.bswap]
  | .cdq => [``Straight.cdqExact, ``Straight.cdq]
  | .cqo => [``Straight.cqoExact, ``Straight.cqo]
  | .cmov _ _ _ (.reg _) => [``Straight.cmovExact, ``Straight.cmovRM]
  | .cmov _ _ _ _ => [``Straight.cmovRM]
  | .setcc _ (.reg _) => [``Straight.setccExact, ``Straight.setccRM]
  | .setcc _ _ => [``Straight.setccRM]
  -- control transfers end a block and are not typed by a straight-line rule
  | _ => []

/-- Rules that only sharpen what a more general rule for the same
instruction already gives: they apply when values are exactly known. When an
instruction cannot be typed, why one of these did not apply is not reported,
since the general rule's reason is the one that matters. -/
def sharpeningRules : List Name := [``Straight.leaSp, ``Straight.mov32Exact, ``Straight.aluExact32,
  ``Straight.aluExactRR32, ``Straight.shiftExact, ``Straight.leaExactB, ``Straight.leaExactBI,
  ``Straight.negExact, ``Straight.notExact, ``Straight.imul2Exact, ``Straight.imul3Exact,
  ``Straight.mulDivExact, ``Straight.cdqExact, ``Straight.cqoExact,
  ``Straight.movsxdExact, ``Straight.movzxExact, ``Straight.movsxExact, ``Straight.popcntExact,
  ``Straight.bswapExact, ``Straight.cmovExact, ``Straight.setccExact]

/-- Why an instruction form has no rule, where there is something more
useful to say than that. -/
def Instr.noRuleReason : Instr → Option String
  | .mulDiv .div _ (.mem _) | .mulDiv .idiv _ (.mem _) =>
    some "a divide is typed only when its divisor is shown not to be zero, and values in \
      memory are not tracked: load the divisor into a register first"
  | _ => none

/-- The registers whose values an instruction's rules need to speak of. If
one of them is typed as an integer, the tactic gives its value a name first,
so that the rules for exactly known values apply. -/
def Instr.wantsNamed : Instr → List Reg
  | .mulDiv .div _ (.reg r) | .mulDiv .idiv _ (.reg r) => [.rax, .rdx, r]
  | .cqo | .cdq => [.rax]
  | _ => []

/-- Whether the instruction can send control somewhere other than the next
instruction, which is where a block ends. -/
def Instr.endsBlock : Instr → Bool
  | .jmp _ | .jcc _ _ | .call _ | .ret | .syscall | .ud2 => true
  | _ => false

/-- Every straight-line rule, for instructions whose shape is not known. -/
def allStraightRules : List Name := sharpeningRules ++ [``Straight.movRR64, ``Straight.movRR32, ``Straight.movRI, ``Straight.movAbs, ``Straight.leaRip, ``Straight.lea, ``Straight.loadStack, ``Straight.loadField, ``Straight.storeStack, ``Straight.storeField, ``Straight.push, ``Straight.pop, ``Straight.allocFrame, ``Straight.freeFrame', ``Straight.aluExact, ``Straight.aluExactRR, ``Straight.addPtr, ``Straight.aluRR, ``Straight.aluRI, ``Straight.testExact, ``Straight.nop, ``Straight.aluStoreR, ``Straight.aluStoreI, ``Straight.cmpR, ``Straight.cmpI, ``Straight.aluLoad, ``Straight.testRM, ``Straight.negRM, ``Straight.notRM, ``Straight.shiftImm, ``Straight.shiftCl, ``Straight.mulRM, ``Straight.imulRM, ``Straight.divSafe, ``Straight.idivSafe, ``Straight.imul2RM, ``Straight.imul3RM, ``Straight.popcntRM, ``Straight.bswap, ``Straight.cdq, ``Straight.cqo, ``Straight.movsxdRM, ``Straight.cmovRM, ``Straight.setccRM, ``Straight.movzxRM, ``Straight.movsxRM, ``Straight.loadInt, ``Straight.storeInt, ``Straight.storeImm, ``Straight.store8RM, ``Straight.store16RM, ``Straight.loadGlobal_of, ``Straight.storeGlobal_of, ``Straight.xorSelf,
  ``Straight.loadIndexed, ``Straight.storeIndexed]

private unsafe def evalInstrUnsafe (e : Expr) : MetaM Instr :=
  evalExpr Instr (mkConst ``Instr) e

private unsafe def evalAddrUnsafe (e : Expr) : MetaM Nat := do
  let v ← evalExpr (BitVec 64) (mkApp (mkConst ``BitVec) (mkNatLit 64)) e
  return v.toNat

/-- The number a closed address term denotes. -/
@[implemented_by evalAddrUnsafe]
private opaque evalAddr (e : Expr) : MetaM Nat

/-- The instruction a closed term denotes. -/
@[implemented_by evalInstrUnsafe]
private opaque evalInstr (e : Expr) : MetaM Instr

/-- The instruction in a goal, if it is fully known. -/
private def knownInstr (e : Expr) : MetaM (Option Instr) := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasFVar then return none
  try return some (← evalInstr e) catch _ => return none

/-- Tries one rule on the main goal, undoing everything if it does not finish. -/
private def tryRule (rule : Name) : TacticM Bool := do
  let saved ← saveState
  try
    if orderedRules.contains rule then
      evalTactic (← `(tactic| ty_rule_ordered $(mkIdent rule)))
    else
      evalTactic (← `(tactic| ty_rule $(mkIdent rule)))
    return true
  catch _ =>
    saved.restore
    return false

/-- Shows a term without the internal names of unknowns. -/
private def ppClean (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.mvars false) (ppExpr (← instantiateMVars e))
  -- One line, however long: these appear inside sentences.
  return fmt.pretty (width := 100000)

/-- The elements of a list written out in full, if the term is one. -/
private partial def listElems? (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    (listElems? e.appArg!).map (e.appFn!.appArg! :: ·)
  else none

/-- A type in the notation used in messages: `int`, `exactly 5`,
`pointer to [int, int]`. Falls back to the Lean term for anything else. -/
private partial def ppTy (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  if e.isConstOf ``Ty.int then return "int"
  if e.isAppOfArity ``Ty.eq 1 then return s!"exactly {← ppClean e.appArg!}"
  if e.isAppOfArity ``Ty.code 1 then return "code pointer"
  if e.isAppOf ``Ty.fn || e.isAppOf ``FnSig.ty then return "function pointer"
  if e.isAppOfArity ``Ty.nullable 1 then return s!"{← ppTy e.appArg!} or null"
  if e.isAppOfArity ``Ty.orErr 1 then return s!"{← ppTy e.appArg!} or an error number"
  if e.isAppOfArity ``Ty.ref 3 then
    let args := e.getAppArgs
    let kind := if args[1]!.isConstOf ``Bool.true then "pointer" else "read-only pointer"
    let index ← ppClean args[2]!
    return s!"{kind} to a block of kind {← ppClean args[0]!}" ++
      (if index == "0" then "" else s!", at field {index}")
  if e.isAppOfArity ``Ty.ptr 3 then
    let args := e.getAppArgs
    let kind := if args[1]!.isConstOf ``Bool.true then "pointer" else "read-only pointer"
    let fields ← match listElems? args[0]! with
      | some elems => do
        let parts ← elems.mapM ppTy
        pure s!"[{", ".intercalate parts}]"
      | none =>
        if args[0]!.isAppOfArity ``List.replicate 3 then
          let n ← ppClean args[0]!.appFn!.appArg!
          pure s!"{n} × {← ppTy args[0]!.appArg!}"
        else ppClean args[0]!
    let index ← ppClean args[2]!
    return s!"{kind} to {fields}" ++ (if index == "0" then "" else s!", at field {index}")
  ppClean e

/-- The name of a register, if the term is one. -/
private def regName? (e : Expr) : Option String :=
  match e.constName? with
  | some (.str ``Reg n) => some n
  | _ => none

/-- Describes, in terms of the program, a rule premise that could not be proved. -/
private def describePremise (ty : Expr) : MetaM MessageData := do
  let ty ← instantiateMVars ty
  if let some (_, lhs, rhs) := ty.eq? then
    -- what a divide needs of the upper half of its dividend
    if lhs.isAppOf ``BitVec.setWidth && rhs.isAppOf ``signFill then
      return m!"`rdx` is not known to hold the sign extension of `rax`: use `cqo` or `cdq` \
        before the divide"
    if lhs.isAppOf ``BitVec.setWidth && !rhs.isAppOf ``BitVec.setWidth then
      return m!"`rdx`, the upper half of the dividend, is not known to be zero: clear it \
        before the divide"
    -- what a register must hold
    if lhs.isAppOfArity ``CtxOf.regs 3 then
      let reg := (regName? (← whnf lhs.appArg!)).getD "the register"
      let actual ← ppTy (← reduce lhs)
      if lhs.appArg!.isAppOf ``IndexReg.toReg then
        return m!"the index register `{reg}` must hold an exactly known value, but its type \
          is `{actual}`; `ty_name` gives an integer a name"
      let wanted :=
        if rhs.isAppOf ``Ty.ptr then
          if rhs.getAppArgs[1]!.isConstOf ``Bool.true then "a writable pointer" else "a pointer"
        else if rhs.isAppOf ``Ty.eq then "an exactly known value"
        else if rhs.isAppOf ``Ty.code then "a code pointer"
        else if rhs.isAppOf ``Ty.fn || rhs.isAppOf ``FnSig.ty then "a function pointer"
        else "a value of another type"
      let held ← reduce lhs
      let hint :=
        if held.isAppOf ``Ty.nullable then
          ": it must be tested for null first, and `ty_null` then gives the two cases"
        else if held.isAppOf ``Ty.orErr then
          ": it must be tested for an error first, and `ty_err` then gives the two cases"
        else if held.isAppOf ``Ty.ref && rhs.isAppOf ``Ty.ptr then
          ": `ty_open` turns it into a pointer to that kind's fields"
        else ""
      return m!"`{reg}` must hold {wanted}, but its type is `{actual}`{hint}"
    if lhs.isAppOf ``MemTy.locate then
      return m!"the address is not inside any memory block"
    if lhs.isAppOf ``AluOp.readsCarry then
      return m!"this rule does not cover operations that read the carry flag"
    if lhs.isAppOfArity ``CtxOf.room 2 then
      return m!"there is not enough free stack: the context has room for {← ppClean (← reduce lhs)}"
    -- a field or stack slot lookup
    let actual ← reduce lhs
    if actual.isAppOf ``Option.none then
      return m!"there is no field or stack slot at that offset"
    if rhs.isAppOf ``Option.some && actual.isAppOf ``Option.some then
      return m!"the field must have type `{← ppTy rhs.appArg!}`, but has type \
        `{← ppTy actual.appArg!}`"
    if rhs.isAppOf ``Option.some then
      return m!"the field is not known to be inside the block: a bound on the index is needed \
        among the hypotheses"
    return m!"needs `{← ppClean ty}`, but the left side is `{← ppClean actual}`"
  if ty.isAppOf ``slotDisp then
    return m!"the displacement must be a non-negative multiple of 8"
  if ty.isAppOf ``innerDisp then
    return m!"the displacement must be non-negative"
  if ty.isAppOfArity ``Sub 2 then
    return m!"a value of type `{← ppTy (← reduce ty.appFn!.appArg!)}` cannot be stored \
      where `{← ppTy ty.appArg!}` is required"
  if ty.isAppOfArity ``Ne 3 && (regName? ty.appArg!) == some "rsp" then
    return m!"`rsp` cannot be this operand"
  if ty.isAppOfArity ``Ne 3 && ty.appFn!.appArg!.isAppOf ``BitVec.setWidth then
    return m!"the divisor, `{← ppClean ty.appFn!.appArg!.appArg!}`, is not known to be \
      non-zero: a check is needed before the divide"
  if ty.isAppOfArity ``Ne 3 then
    return m!"`{← ppClean ty}` is not known: it is needed among the hypotheses"
  if ty.isAppOfArity ``Or 2 then
    return m!"neither `{← ppClean ty.appFn!.appArg!}` nor `{← ppClean ty.appArg!}` is known: \
      one is needed among the hypotheses"
  if ty.isAppOf ``LE.le then
    return m!"the access would cross the end of an 8-byte field"
  if ty.isForall && ty.getForallBody.isAppOf ``Exists then
    return m!"the flags are not known here, so they do not decide the condition"
  if ty.isForall then
    return m!"the operation reads the carry flag, which is not known to be defined here"
  return m!"needs `{← ppClean ty}`"

/-- The rules for an operand judgment, in the order to try them. -/
private def operandRules (ty : Expr) : List Name :=
  if ty.isAppOf ``ReadOk then [``ReadOk.reg, ``ReadOk.slot, ``ReadOk.field, ``ReadOk.indexed, ``ReadOk.global_of]
  else if ty.isAppOf ``WriteIntOk then [``WriteIntOk.reg, ``WriteIntOk.slot, ``WriteIntOk.field, ``WriteIntOk.indexed,
    ``WriteIntOk.global_of]
  else if ty.isAppOf ``Holds then [``Holds.reg, ``Holds.slot, ``Holds.field, ``Holds.indexed, ``Holds.global_of]
  else []

/-- Applies a rule to the main goal and describes the first premise that
cannot be proved. `none` if the rule is for a goal of a different form. A
premise about an operand is explained by the rule for that kind of operand. -/
private partial def explainPremises (rule : Name) : TacticM (Option MessageData) := do
  try
    evalTactic (← `(tactic| refine' $(mkIdent rule) ..))
  catch _ =>
    return none
  let goals ← getGoals
  -- Premises are attempted in order and then again, as in `ty_rule`, so that
  -- what is reported is a premise that fails once everything else is known.
  let mut failed : Array (MVarId × Expr) := #[]
  let mut stop := false
  for pass in [0, 1] do
    for g in goals do
      if ← g.isAssigned then continue
      unless ← isProp (← g.getType) do continue
      setGoals [g]
      let attempt ← saveState
      let ok ← try
          evalTactic (← `(tactic| ty_side))
          pure true
        catch _ =>
          attempt.restore
          pure false
      if !ok then
        let ty ← instantiateMVars (← g.getType)
        -- Where premises build on one another, nothing after the first
        -- failure can be judged.
        if orderedRules.contains rule then
          failed := #[(g, ty)]
          stop := true
          break
        if pass == 1 then failed := failed.push (g, ty)
    if stop then break
  -- A premise about the displacement is reported first: the others cannot
  -- be judged until it holds. After that, prefer a premise with no unknowns.
  let isDisp (e : MVarId × Expr) : Bool := e.2.isAppOf ``slotDisp || e.2.isAppOf ``innerDisp
  let chosen := (failed.find? isDisp <|> failed.find? (!·.2.hasExprMVar) <|> failed[0]?)
  match chosen with
  | some (g, ty) =>
    let inner := operandRules ty
    if inner.isEmpty then return some (← describePremise ty)
    for r in inner do
      setGoals [g]
      if let some msg ← explainPremises r then return some msg
    return some m!"this form of operand has no rule: a memory operand needs a base register \
      or `rip`"
  | none => return some m!"every premise holds separately, but not together"

/-- Says why a rule did not apply: the first premise that could not be proved. -/
private def explainRule (rule : Name) : TacticM MessageData := do
  let saved ← saveState
  let name := rule.components.getLast!
  try
    match ← explainPremises rule with
    | some msg => return m!"{name}: {msg}"
    | none => return m!"{name}: is for a different form of this instruction"
  finally
    saved.restore

/-- Types the instruction in a `Straight Ψ next Γ i ?Γ'` goal, or explains why not. -/
def typeStraight : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``Straight 5 do
    throwError "ty_straight: the goal is not of the form `Straight Ψ next Γ i Γ'`"
  let instrExpr := ty.getAppArgs[3]!
  let instr? ← knownInstr instrExpr
  let rules := match instr? with
    | some i => i.rules
    | none => allStraightRules
  for rule in rules do
    if ← tryRule rule then return
  let shown : MessageData := match instr? with
    | some i => m!"`{i.toAsm}`"
    | none => m!"{instrExpr}"
  if rules.isEmpty then
    match instr?.bind Instr.noRuleReason with
    | some why => throwError "cannot type {shown}: {why}"
    | none => throwError "the type system has no rule for {shown}"
  let mut msg := m!"cannot type {shown} in the current context"
  let general := rules.filter (!sharpeningRules.contains ·)
  for rule in (if general.isEmpty then rules else general) do
    msg := msg ++ m!"\n• {← explainRule rule}"
  throwError msg

/-- Types the instruction in a `Straight` goal, choosing the rule from the
instruction's shape. When no rule applies, the error names the instruction
and, for each rule that could have applied, the premise that failed. -/
elab "ty_straight" : tactic => typeStraight

/-- The outcome of trying to take one step in a block. -/
private inductive StepResult
  | stepped
  | endOfBlock (instr : Instr)
  | notABlock

/-- Runs a tactic on one goal and returns the goals it leaves. -/
private def runOn (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  setGoals [g]
  -- Without this a failing step is logged and its goal admitted, and the
  -- caller would carry on as if it had succeeded.
  Tactic.withoutRecover tac
  getUnsolvedGoals

/-- The system call number a context puts in `rax`, if it is exactly known. -/
private def syscallNumber (ctx : Expr) : MetaM (Option Nat) := do
  let regTy ← whnf (← mkAppM ``CtxOf.regs #[ctx, mkConst ``Reg.rax])
  unless regTy.isAppOfArity ``Ty.eq 1 do return none
  let v ← instantiateMVars regTy.appArg!
  if v.hasExprMVar || v.hasFVar then return none
  try return some (← evalAddr v) catch _ => return none

/-- Types a `read` whose buffer is on the stack, at the head of a block
goal. Returns the rest of the block. -/
private def typeReadStack (goal : MVarId) : TacticM MVarId := do
  let gs ← runOn goal (do evalTactic (← `(tactic|
    refine BlockOk.sys rfl
      (linux_read_stack (v := ?_) (d := ?_) (len := ?_) rfl ?_ ?_ ?_ ?_ ?_) ?_)))
  -- what the registers hold first: that settles where the buffer is
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        discard <| runOn g (do evalTactic (← `(tactic| rfl)))
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if t.isForall then
      discard <| runOn g (do evalTactic (← `(tactic| (refine ints_of_check ?_; first | ((try dsimp only); decide) | rfl))))
    else if (← isProp t) then
      discard <| runOn g (do evalTactic (← `(tactic| decide)))
  let some rest := rest? | throwError "unexpected goals"
  return rest

/-- Types a `write` or `read` at the head of a block goal, leaving the rest
of the block as the main goal. -/
private def typeSyscallStep (goal : MVarId) (nr : Nat) : TacticM Unit := do
  let ctx := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs[5]!
  if nr == 0 then
    let saved ← saveState
    try
      let rest ← typeReadStack goal
      setGoals [rest]
      evalTactic (← `(tactic| ty_normalize))
      return
    catch _ => saved.restore
  let gs ← try
      if nr == 1 then
        runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.sys rfl (linux_write rfl) ?_)))
      else
        runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.sys rfl
            (linux_read (fields := ?_) (off := ?_) (len := ?_) rfl ?_ ?_ ?_) ?_)))
    catch _ => throwError "`syscall`: the operating system here is not the Linux model"
  let mut rest? : Option MVarId := none
  let mut left : List MVarId := []
  -- what the registers must hold first: that settles the buffer and the count
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if let some (_, lhs, rhs) := t.eq? then
      try
        discard <| runOn g (do evalTactic (← `(tactic| rfl)))
      catch _ =>
        let reg := (regName? lhs.appArg!).getD "the register"
        let actual ← g.withContext do ppTy (← reduce (← mkAppM ``CtxOf.regs #[ctx, lhs.appArg!]))
        if rhs.isAppOf ``Ty.ptr then
          throwError "`read` needs `{reg}` to hold a writable pointer to the buffer, or the \
            address of stack slots taken with `lea` once `rsp` has a name, but its type is \
            `{actual}`"
        else
          throwError "`read` needs the count in `{reg}` to be exactly known, but its type is \
            `{actual}`"
  -- then that every field the buffer covers is an integer
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isForall then
      let after ← try
          runOn g (do evalTactic (← `(tactic| first
            | (refine ints_of_check ?_; first | ((try dsimp only); decide) | rfl)
            | (intro j hj; refine getElem?_replicate_of_lt ?_; omega))))
        catch _ =>
          throwError "`read` could overwrite something that is not an integer: the buffer in \
            `rsi` does not have room for the count in `rdx` in integer fields"
      left := left ++ after
  let some rest := rest? | throwError "ty_block: unexpected goals at `syscall`"
  setGoals [rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left)

/-- Types the first instruction of a block goal if it is a straight-line
instruction, leaving the rest of the block as the main goal. -/
private partial def typeStep (named : Bool := false) : TacticM StepResult := withMainContext do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOf ``BlockOk do return .notABlock
  let saved ← saveState
  let others := (← getGoals).drop 1
  setGoals [goal]
  try
    evalTactic (← `(tactic| refine BlockOk.step (Γ' := ?_) rfl ?_ ?_))
  catch _ =>
    saved.restore
    throwError "there is no instruction at this address"
  let mut instrGoal? : Option MVarId := none
  let mut restGoal? : Option MVarId := none
  for g in ← getGoals do
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``Straight then instrGoal? := some g
    else if t.isAppOf ``BlockOk then restGoal? := some g
  let (some instrGoal, some restGoal) := (instrGoal?, restGoal?)
    | saved.restore; throwError "ty_step: unexpected goals after taking a step"
  let instrTy ← instantiateMVars (← instrGoal.getType)
  if let some instr ← knownInstr instrTy.getAppArgs[3]! then
    if instr.endsBlock then
      saved.restore
      -- A system call that returns is a step like any other.
      if let .syscall := instr then
        if let some nr ← syscallNumber ty.getAppArgs[5]! then
          if nr == 0 || nr == 1 then
            setGoals [goal]
            typeSyscallStep goal nr
            setGoals ((← getGoals) ++ others)
            return .stepped
      return .endOfBlock instr
    -- Registers the rules need to speak of, but which are only known to be
    -- integers, are given names first.
    unless named do
      let ctx := ty.getAppArgs[5]!
      let mut toName : List Reg := []
      for r in instr.wantsNamed.eraseDups do
        let regE := mkConst (Name.str ``Reg r.name64)
        let regTy ← whnf (← mkAppM ``CtxOf.regs #[ctx, regE])
        if regTy.isConstOf ``Ty.int then toName := toName ++ [r]
      unless toName.isEmpty do
        saved.restore
        setGoals [goal]
        for r in toName do
          nameRegister (mkIdent (Name.str ``Reg r.name64))
            (mkIdent (Name.mkSimple s!"{r.name64}₀"))
        setGoals ((← getGoals) ++ others)
        return ← typeStep (named := true)
  setGoals [instrGoal]
  let addr ← instantiateMVars ty.getAppArgs[4]!
  let at? ← if addr.hasExprMVar || addr.hasFVar then pure none
    else try pure (some (← evalAddr addr)) catch _ => pure none
  try
    typeStraight
  catch e =>
    match at? with
    | some n => throwError "at address {n}: {e.toMessageData}"
    | none => throw e
  setGoals [restGoal]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ others)
  return .stepped

/-- Types one straight-line instruction at the start of a block. -/
elab "ty_step" : tactic => do
  match ← typeStep with
  | .stepped => pure ()
  | .endOfBlock instr =>
    throwError "`{instr.toAsm}` can transfer control, so it ends the block and is not typed by `ty_step`"
  | .notABlock => throwError "ty_step: the goal is not a block"

/-- Types the straight-line instructions at the start of a block, stopping
at the first instruction that can transfer control and leaving it as the
goal. A straight-line instruction that cannot be typed is an error. -/
elab "ty_steps" : tactic => do
  repeat
    match ← typeStep with
    | .stepped => continue
    | _ => break

/-! ## Control transfers

For a labelled program the tactic can find where control goes: it looks for
the label at the target address, then for a context allowed at that label
which the current context is at least as strong as. Whatever it cannot
settle is left as a goal: typically a fact about values that the target's
context demands, such as a loop bound. -/

/-- The constructors of the inductive type a term's type belongs to. -/
private def ctorsOfType (ty : Expr) : MetaM (List Name) := do
  let ty ← whnf (← instantiateMVars ty)
  let some n := ty.getAppFn.constName? | return []
  match (← getEnv).find? n with
  | some (.inductInfo info) => return info.ctors
  | _ => return []

/-- Whether a proposition compares two values. -/
private def isComparison (t : Expr) : Bool :=
  t.isAppOf ``LT.lt || t.isAppOf ``LE.le || t.isAppOf ``GT.gt || t.isAppOf ``GE.ge ||
  t.isAppOf ``Eq || t.isAppOf ``Ne || t.isAppOf ``Not

/-- Proves `Φ a Δ` for a labelled program: finds the label whose address is
`a` and a context allowed there. `check` runs once the context is chosen and
should fail if it is the wrong one; another is then tried. Returns the goals
`check` left, then the premises of the chosen context that remain unproved. -/
private def proveAtLabel (g : MVarId) (check : TacticM (List MVarId)) :
    TacticM (List MVarId) := do
  let parts ← try
      runOn g (do evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩)))
    catch _ =>
      throwError "the code typing here is not given by labels; name the target context with \
        `ty_accept`"
  let mut label? : Option MVarId := none
  let mut addr? : Option MVarId := none
  let mut fact? : Option MVarId := none
  for p in parts do
    let t ← instantiateMVars (← p.getType)
    if !(← isProp t) then label? := some p
    else if t.isEq then addr? := some p
    else fact? := some p
  let (some label, some addr, some fact) := (label?, addr?, fact?)
    | throwError "the code typing here is not given by labels; name the target context with \
        `ty_accept`"
  for c in ← ctorsOfType (← label.getType) do
    let atLabel ← saveState
    let found ← try
        label.assign (mkConst c)
        discard <| runOn addr (do evalTactic (← `(tactic| rfl)))
        pure true
      catch _ =>
        atLabel.restore
        pure false
    unless found do continue
    let mut reasons : MessageData := m!""
    for k in ← ctorsOfType (← fact.getType) do
      let atCtx ← saveState
      -- A context for some other label is passed over without comment.
      let premises? ← try
          pure (some (← runOn fact (do evalTactic (← `(tactic| refine' $(mkIdent k) ..)))))
        catch _ =>
          atCtx.restore
          pure none
      let some premises := premises? | continue
      try
        -- Premises that are not comparisons, such as a caller's requirement,
        -- are looked for among the hypotheses first. That fixes the parameters
        -- they mention to the ones in scope, where comparing contexts could
        -- settle on something equal in effect but different in form.
        for p in premises do
          if ← p.isAssigned then continue
          let t ← instantiateMVars (← p.getType)
          unless ← isProp t do continue
          if isComparison t then continue
          try
            discard <| runOn p (do evalTactic (← `(tactic| assumption)))
          catch _ => pure ()
        let left ← check
        let mut rest := left
        for p in premises do
          if ← p.isAssigned then continue
          unless ← isProp (← p.getType) do continue
          let after ← try
              runOn p (do evalTactic (← `(tactic| first | assumption | omega | decide)))
            catch _ => pure [p]
          rest := rest ++ after
        -- Parameters nothing determined are left for the user to supply.
        for p in premises do
          if ← p.isAssigned then continue
          unless ← isProp (← p.getType) do rest := rest ++ [p]
        return rest
      catch e =>
        atCtx.restore
        reasons := reasons ++ m!"\n• {k.components.getLast!}: {e.toMessageData}"
    throwError "no context allowed at label `{c.components.getLast!}` accepts the current one{reasons}"
  throwError "there is no label at the target address"

/-- Fails if a register comparison left as a goal can never hold: the two
types are fully known and of different kinds. -/
private def rejectImpossible (gs : List MVarId) : TacticM Unit := do
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    unless t.isAppOfArity ``Sub 2 do continue
    let have_ ← g.withContext (reduce t.appFn!.appArg!)
    let want ← g.withContext (reduce t.appArg!)
    if have_.hasExprMVar || want.hasExprMVar then continue
    if have_.getAppFn.constName? != want.getAppFn.constName? then
      let reg := (← g.getTag).eraseMacroScopes.components.getLast!
      throwError "`{reg}` has type `{← ppTy have_}`, but `{← ppTy want}` is required"

/-- Proves `Accepts Φ a Γ` by finding the label at `a`. Returns what is left. -/
private def proveAccepts (g : MVarId) : TacticM (List MVarId) := do
  let parts ← runOn g (do evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩)))
  let mut here? : Option MVarId := none
  let mut sub? : Option MVarId := none
  for p in parts do
    let t ← instantiateMVars (← p.getType)
    if t.isAppOf ``CtxSub then sub? := some p
    else if ← isProp t then here? := some p
  let (some here, some sub) := (here?, sub?)
    | throwError "ty_label: the goal is not of the form `Accepts Φ a Γ`"
  proveAtLabel here (do
    let left ← try
        runOn sub (do evalTactic (← `(tactic| ctx_sub)))
      catch _ =>
        throwError "the stack, the free room or the flags do not match"
    rejectImpossible left
    pure left)

/-- Proves `Accepts Φ a Γ` in a labelled program by finding the label at
address `a` and a context allowed there that `Γ` is at least as strong as.
Facts the target's context demands, and register types that do not
obviously match, are left as goals. -/
elab "ty_label" : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  let left ← proveAccepts goal
  setGoals (left ++ others)

/-- Introduces the flags hypotheses of one side of a conditional jump. When
the flags are known exactly they are substituted. The fact about which way
the condition went is named `hcond`. -/
private def introBranch : TacticM Unit := do
  let hcond := mkIdent `hcond
  -- `rfl` must be written without macro hygiene, or `rintro` takes it for a name.
  let subst := mkIdent `rfl
  evalTactic (← `(tactic| first | rintro f $subst:ident $hcond:ident | intro f _ $hcond:ident))

/-- Closes a goal reached under an assumption about a condition that the
exactly known flags contradict. Returns whether it did. -/
private def closeIfImpossible (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [g]
    Tactic.withoutRecover do
      evalTactic (← `(tactic| (refine absurd $(mkIdent `hcond) ?_; decide)))
    return (← getUnsolvedGoals).isEmpty
  catch _ =>
    saved.restore
    -- The flags may come from an error number, known only to be one.
    let isErr ← g.withContext do
      (← getLCtx).anyM fun d => do
        return (← instantiateMVars d.type).isAppOf ``SysErr
    unless isErr do return false
    try
      setGoals [g]
      Tactic.withoutRecover do
        evalTactic (← `(tactic| (
          refine absurd $(mkIdent `hcond) ?_
          simp only [SysErr] at *
          simp only [Cond.eval, Flags.ofResult, AluOp.apply, subBorrow, bind, Option.bind, pure,
            Option.map, Option.some.injEq]
          bv_decide)))
      return (← getUnsolvedGoals).isEmpty
    catch _ =>
      saved.restore
      return false

/-- Shows the flags decide a condition. -/
private def decideCond : TacticM Unit := do
  let subst := mkIdent `rfl
  evalTactic (← `(tactic| first
    | (rintro f $subst:ident; exact ⟨_, rfl⟩)
    | exact Cond.decided_of_known (fun _ h => h) _
    | (refine Cond.decided_of_defined _ ?_; decide)))

/-- The goal among `gs` that came from the placeholder `?name`. Goals are
found by name because the order in which `refine` returns them is not fixed. -/
private def goalNamed (gs : List MVarId) (name : Name) : TacticM MVarId := do
  for g in gs do
    let tag := (← g.getTag).eraseMacroScopes
    if !tag.isAnonymous && tag.components.getLast! == name then return g
  throwError "ty_block: internal error, no goal named {name}"

/-- `ty_step_with r` types one straight-line instruction with the rule `r`,
for a rule the tactics would not choose or could not finish: typically one
with a premise about values, such as a divisor not being zero. Premises that
are not routine are left as goals, after the rest of the block. -/
elab "ty_step_with " r:term : tactic => withMainContext do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  let gs ← try
      runOn goal (do evalTactic (← `(tactic| refine BlockOk.step (Γ' := ?_) rfl ?instr ?rest)))
    catch _ => throwError "ty_step_with: there is no instruction at this address"
  let instr ← goalNamed gs `instr
  let rest ← goalNamed gs `rest
  let premises ← try
      runOn instr (do evalTactic (← `(tactic| refine' $r ..)))
    catch e => throwError "ty_step_with: the rule does not fit this instruction\n{e.toMessageData}"
  let mut left : List MVarId := []
  for pass in [0, 1] do
    for p in premises do
      if ← p.isAssigned then continue
      unless ← isProp (← p.getType) do continue
      let after ← try
          runOn p (do evalTactic (← `(tactic| first | ty_side | assumption)))
        catch _ => pure [p]
      if pass == 1 then left := left ++ after
  setGoals [rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left ++ others)

/-- What ending a block did. -/
private inductive Finish
  /-- The block is finished; these goals are left. -/
  | done (left : List MVarId)
  /-- A conditional jump was typed and the block continues in `rest`. -/
  | continues (rest : MVarId) (left : List MVarId)
  /-- This instruction needs information the tactic does not have. -/
  | needsHelp (msg : MessageData)

/-- Types the control transfer at the head of a block goal. -/
private def finishBlock (goal : MVarId) (instr : Instr) : TacticM Finish := do
  match instr with
  | .jmp (.rel _) =>
    let gs ← runOn goal (do evalTactic (← `(tactic| refine BlockOk.last rfl (HasType.jmp ?_))))
    let [acc] := gs | throwError "ty_block: unexpected goals at `jmp`"
    return .done (← proveAccepts acc)
  | .syscall =>
    -- `write` and `read` are typed as steps; what reaches here is `exit`, or
    -- a call the type system has no rule for.
    let ctx := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs[5]!
    match ← syscallNumber ctx with
    | some 60 =>
      let gs ← try
          runOn goal (do evalTactic (← `(tactic|
            refine BlockOk.last rfl (HasType.syscallExit (linux_exit rfl)))))
        catch _ => throwError "`syscall`: the operating system here is not the Linux model"
      return .done gs
    | some 9 =>
      return .needsHelp m!"`syscall`: an `mmap` needs the layout of the new block; use \
        `ty_mmap <fields>` or `ty_mmap_kind <kind>`"
    | some nr =>
      throwError "`syscall`: call number {nr} has no rule. The calls that can be typed are \
        `read` (0), `write` (1), `mmap` (9) and `exit` (60)"
    | none =>
      let actual ← goal.withContext do
        ppTy (← reduce (← mkAppM ``CtxOf.regs #[ctx, mkConst ``Reg.rax]))
      throwError "`syscall`: the call number in `rax` must be exactly known, but its type is \
        `{actual}`"
  | .ret =>
    let gs ← try
        runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last rfl
            (FnSig.ret_of (sig := ?_) (saved := ?_) ?caller ?regs ?sp rfl rfl))))
      catch _ =>
        throwError "`ret` needs a return address on top of the stack, but the context does \
          not have one there"
    let mut left := []
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``FnSig.CallerOk then
        try
          discard <| runOn g (do evalTactic (← `(tactic| assumption)))
        catch _ =>
          throwError "`ret` needs the caller's requirement (`sig.CallerOk …`) among the hypotheses"
      else if t.isAppOf ``Sub then
        left := left ++ (← runOn g (do evalTactic (← `(tactic| ty_sub))))
      else if ← isProp t then
        left := left ++ (← runOn g (do evalTactic (← `(tactic| sub_regs))))
    return .done left
  | .jcc _ _ =>
    -- First try to end the block here, with the next instruction at a label.
    let before ← saveState
    try
      let gs ← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.last rfl (HasType.jcc ?dec ?taken ?fall))))
      let dec ← goalNamed gs `dec
      let taken ← goalNamed gs `taken
      let fall ← goalNamed gs `fall
      discard <| runOn dec decideCond
      let [takenAcc] ← runOn taken introBranch | throwError "unexpected goals"
      let leftTaken ← proveAccepts takenAcc
      let [fallAcc] ← runOn fall introBranch | throwError "unexpected goals"
      let leftFall ← proveAccepts fallAcc
      return .done (leftTaken ++ leftFall)
    catch _ =>
      before.restore
    -- Otherwise the block continues after the jump.
    let gs ← runOn goal (do evalTactic (← `(tactic| refine BlockOk.branch rfl ?dec ?taken ?rest)))
    let dec ← goalNamed gs `dec
    let taken ← goalNamed gs `taken
    let rest ← goalNamed gs `rest
    try
      discard <| runOn dec decideCond
    catch _ =>
      throwError "`{instr.toAsm}`: the flags known here do not decide the condition"
    let [takenAcc] ← runOn taken introBranch | throwError "unexpected goals"
    -- A side that the exactly known flags rule out needs nothing more.
    let leftTaken ← if ← closeIfImpossible takenAcc then pure [] else proveAccepts takenAcc
    let [rest'] ← runOn rest introBranch | throwError "unexpected goals"
    if ← closeIfImpossible rest' then return .done leftTaken
    return .continues rest' leftTaken
  | .jmp (.ind _) =>
    let before ← saveState
    -- a tail call through a function pointer, on behalf of this function's caller
    let tail? ← try
        let gs ← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last rfl (HasType.jmpFn (sig := ?_) (saved := ?_) (ret := ?_)
            (rest := ?_) (room := ?_) ?fn ?caller ?sub))))
        discard <| runOn (← goalNamed gs `fn) (do evalTactic (← `(tactic| ty_operand)))
        discard <| runOn (← goalNamed gs `caller) (do evalTactic (← `(tactic| assumption)))
        let left ← runOn (← goalNamed gs `sub) (do evalTactic (← `(tactic| ctx_sub)))
        pure (some left)
      catch _ =>
        before.restore
        pure none
    if let some left := tail? then return .done left
    let gs ← runOn goal (do evalTactic (← `(tactic|
      refine BlockOk.last rfl (HasType.jmpInd (Δ := ?_) ?code ?sub))))
    let code ← goalNamed gs `code
    let sub ← goalNamed gs `sub
    try
      discard <| runOn code (do evalTactic (← `(tactic| ty_operand)))
    catch _ =>
      throwError "`{instr.toAsm}`: the operand does not hold a pointer to code here. A register \
        holding the exact address of a label becomes one with `ty_fn_ptr` (a function) or \
        `ty_code_ptr` (any other label)"
    let left ← try
        runOn sub (do evalTactic (← `(tactic| ctx_sub)))
      catch _ =>
        throwError "`{instr.toAsm}`: the stack, the free room or the flags do not match what \
          the target expects"
    rejectImpossible left
    return .done left
  | .ud2 =>
    -- Reached only if no state matches the context; that is left to prove
    -- unless the flags predicate is plainly unsatisfiable.
    let hstate := mkIdent `hstate
    let gs ← runOn goal (do evalTactic (← `(tactic|
      (refine BlockOk.last rfl (HasType.unreachable ?_)
       intro _ _ _ _ _ $hstate:ident
       first | exact ($hstate).flags | skip))))
    return .done gs
  | .call _ =>
    return .needsHelp m!"`{instr.toAsm}`: a call needs the callee's signature; use `ty_call <signature>`"
  | _ =>
    return .needsHelp m!"`{instr.toAsm}` is not handled by `ty_block`"

/-- Types a conditional jump in the middle of a block. The side that jumps
is settled as `ty_block` would settle it; the side that carries on is left
as the goal, so that something can be said about it before going further. -/
elab "ty_branch" : tactic => do
  let others := (← getGoals).drop 1
  let saved ← saveState
  match ← typeStep with
  | .endOfBlock instr =>
    let goal ← getMainGoal
    match ← finishBlock goal instr with
    | .done l => setGoals (l ++ others)
    | .continues rest l => setGoals (rest :: l ++ others)
    | .needsHelp m => throwError m
  | .stepped =>
    saved.restore
    throwError "ty_branch: the instruction here does not transfer control; use `ty_step`"
  | .notABlock => throwError "ty_branch: the goal is not a block"

/-- Types a whole block of a labelled program: the straight-line
instructions, then the control transfer that ends it. Jump targets are found
by label. Conditional jumps in the middle of the block are followed.

Goals are left for whatever needs an argument: facts a target context
demands (with the branch condition available as `hcond`), and register types
that do not obviously match. The tactic stops at a `call`, which needs
`ty_call`. -/
elab "ty_block" : tactic => do
  let others := (← getGoals).drop 1
  let mut left : List MVarId := []
  repeat
    let mut endInstr? : Option Instr := none
    repeat
      match ← typeStep with
      | .stepped => continue
      | .endOfBlock instr => endInstr? := some instr; break
      | .notABlock => break
    let some instr := endInstr? | break
    let goal ← getMainGoal
    match ← finishBlock goal instr with
    | .done l =>
      left := left ++ l
      setGoals []
      break
    | .continues rest l =>
      left := left ++ l
      setGoals [rest]
    | .needsHelp _ => break
  setGoals ((← getGoals) ++ left ++ others)

/-- `ty_call sig` types a `call` that ends a block, to a function with
signature `sig`. The callee and the return point are found by label. Left as
goals: argument registers whose types do not obviously match what the
function expects, and register types after the return that do not obviously
match the return point's context. -/
elab "ty_call " sig:term : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  -- Find the instruction, to tell a direct call from an indirect one.
  let parts ← try
      runOn goal (do evalTactic (← `(tactic| refine BlockOk.last rfl ?typed)))
    catch _ => throwError "ty_call: the goal is not a block with an instruction at its address"
  let typed ← goalNamed parts `typed
  let typedTy ← instantiateMVars (← typed.getType)
  let instr? ← knownInstr typedTy.getAppArgs[6]!
  let ctx := typedTy.getAppArgs[5]!
  let noRoom (instr : Instr) : TacticM MessageData := do
    let room ← typed.withContext do ppClean (← reduce (← mkAppM ``CtxOf.room #[ctx]))
    return m!"`{instr.toAsm}`: there is no room on the stack for the return address: the \
      context has room for {room}"
  -- A call through an operand holding a function pointer is typed like a
  -- direct call to that function.
  let viaPointer? ← match instr? with
    | some (.call (.ind _)) =>
      let before ← saveState
      try
        let gs ← runOn typed (do evalTactic (← `(tactic|
          refine HasType.callFn (sig := $sig) (ret := ?_) ?callee rfl ?retpoint ?args ?sp ?back
            ?need)))
        discard <| runOn (← goalNamed gs `callee) (do evalTactic (← `(tactic| ty_operand)))
        pure (some gs)
      catch _ =>
        before.restore
        pure none
    | _ => pure none
  match instr? with
  | some (.call (.rel _)) => pure ()
  | some (.call (.ind rm)) =>
    if viaPointer?.isNone then
      let instr := Instr.call (.ind rm)
      -- Otherwise the operand may hold a pointer to code expecting one context.
      let gs ← try
          runOn typed (do evalTactic (← `(tactic|
            refine FnSig.callInd_ok (sig := $sig) (saved := ?_) (ret := ?_) (rest := ?_)
              ?callee rfl ?retpoint ?args ?sp ?stack)))
        catch _ => throwError (← noRoom instr)
      let callee ← goalNamed gs `callee
      try
        discard <| runOn callee (do evalTactic (← `(tactic| ty_operand)))
      catch _ =>
        throwError "`{instr.toAsm}`: the operand does not hold a pointer to a function with this \
          signature, or there is no room on the stack for the return address. A register \
          holding the exact address of a function becomes a pointer to it with `ty_fn_ptr`"
      let mut left : List MVarId := []
      left := left ++ (← proveAtLabel (← goalNamed gs `retpoint) (pure []))
      left := left ++ (← runOn (← goalNamed gs `args) (do evalTactic (← `(tactic| sub_regs))))
      left := left ++ (← runOn (← goalNamed gs `sp) (do evalTactic (← `(tactic| ty_sub))))
      let stack ← goalNamed gs `stack
      let stackLeft ← try
          runOn stack (do evalTactic (← `(tactic| ty_stack)))
        catch _ => pure [stack]
      unless stackLeft.isEmpty do
        throwError "`{instr.toAsm}`: the stack here does not match the one the function pointer \
          expects"
      setGoals (left ++ others)
      return
  | some instr => throwError "ty_call: the instruction here is `{instr.toAsm}`, not a call"
  | none => throwError "ty_call: the instruction at this address is not known"
  let gs ← match viaPointer? with
    | some gs => pure gs
    | none =>
      try
        runOn typed (do evalTactic (← `(tactic|
          refine FnSig.call_ok (sig := $sig) (ret := ?_) ?callee rfl ?retpoint ?args ?sp ?back
            ?need)))
      catch _ => throwError (← noRoom (instr?.getD .nop))
  let mut left : List MVarId := []
  -- the callee first: it involves no unknowns
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``FnSig.At then
      let [entry] ← runOn g (do evalTactic (← `(tactic| intro _ _ _ _ hK)))
        | throwError "ty_call: unexpected goals"
      left := left ++ (← proveAtLabel entry (pure []))
  -- then the return point, which fixes the context after the call
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if !(← isProp t) then continue
    if t.isAppOf ``FnSig.At || t.isAppOf ``CtxSub || t.isForall || t.isAppOf ``LE.le ||
        t.isAppOf ``Sub then continue
    left := left ++ (← proveAtLabel g (pure []))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``CtxSub then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| ctx_sub))))
    else if t.isForall then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| sub_regs))))
    else if t.isAppOf ``Sub then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| ty_sub))))
    else if t.isAppOf ``LE.le then
      -- The stack the function needs is a field of its signature: the
      -- signature is unfolded so that arithmetic can see the number.
      let sigName? := (t.appFn!.appArg!.getAppArgs.back?.bind (·.getAppFn.constName?))
      let after ← try
          runOn g (do evalTactic (← `(tactic| first | decide | omega)))
        catch e =>
          match sigName? with
          | some c =>
            try
              runOn g (do evalTactic (← `(tactic|
                (unfold $(mkIdent c); dsimp only; first | decide | omega))))
            catch _ => throw e
          | none => throw e
      left := left ++ after
  setGoals (left ++ others)

/-- `ty_code_ptr r to Δ`: register `r` holds exactly the address of a label
that allows context `Δ`; from here on it is a pointer to code expecting `Δ`,
which can be stored, jumped through or called through. What the label
demands of `Δ`, such as a function's requirement on its caller, is proved
where it is routine and otherwise left as goals. -/
elab "ty_code_ptr " r:term " to " Δ:term : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  let gs ← try
      runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.codePtr (r := $r) (Δ := $Δ) ?ne rfl ?here ?rest)))
    catch _ =>
      throwError "ty_code_ptr: the register does not hold an exactly known address here"
  discard <| runOn (← goalNamed gs `ne) (do evalTactic (← `(tactic| decide)))
  let mut left : List MVarId := []
  for g in ← proveAtLabel (← goalNamed gs `here) (pure []) do
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``FnSig.CallerOk then
      let parts ← runOn g (do evalTactic (← `(tactic| refine FnSig.CallerOk.mk ?ret ?room)))
      for p in parts do
        let after ← try
            runOn p (do evalTactic (← `(tactic| first | ctx_sub | decide | omega)))
          catch _ => pure [p]
        left := left ++ after
    else left := left ++ [g]
  setGoals [← goalNamed gs `rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left ++ others)

/-- `ty_fn_ptr r to sig`: register `r` holds exactly the address of a
function with signature `sig`; from here on it is a pointer to that function,
which can be stored, passed on, and called by any caller. -/
elab "ty_fn_ptr " r:term " to " sig:term : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  let gs ← try
      runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.fnPtr (r := $r) (sig := $sig) ?ne rfl ?here ?rest)))
    catch _ =>
      throwError "ty_fn_ptr: the register does not hold an exactly known address here"
  discard <| runOn (← goalNamed gs `ne) (do evalTactic (← `(tactic| decide)))
  let [entry] ← runOn (← goalNamed gs `here) (do evalTactic (← `(tactic| intro _ _ _ _ hK)))
    | throwError "ty_fn_ptr: unexpected goals"
  let left ← try
      proveAtLabel entry (pure [])
    catch e =>
      throwError "ty_fn_ptr: the address is not that of a function with this signature\n\
        {e.toMessageData}"
  setGoals [← goalNamed gs `rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left ++ others)

/-- Types an `mmap` at the head of a block goal with the given lemma applied
to the layout asked for, and proves what it needs of the registers. -/
private def typeMmap (rule : TSyntax `term) : TacticM Unit := do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  setGoals [goal]
  try
    evalTactic (← `(tactic| refine BlockOk.sys rfl $rule ?_))
  catch _ =>
    throwError "`mmap` is system call 9 of the Linux model: `rax` must hold exactly 9"
  let gs ← getGoals
  -- what the registers hold and what the kind is first: that settles the
  -- length and the fields
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        setGoals [g]
        try
          Tactic.withoutRecover do evalTactic (← `(tactic| rfl))
        catch _ =>
          let reg := (regName? (← whnf lhs.appArg!)).getD "the register"
          let actual ← g.withContext do
            let regTy ← whnf lhs
            let shown? ← if regTy.isAppOfArity ``Ty.eq 1 then
                try
                  let n ← evalAddr (← instantiateMVars regTy.appArg!)
                  pure (some s!"exactly 0x{String.ofList (Nat.toDigits 16 n)}")
                catch _ => pure none
              else pure none
            match shown? with
            | some shown => pure shown
            | none => ppTy (← reduce lhs)
          if reg == "rsi" then
            throwError "`mmap` needs the length in `rsi` to be exactly known, but its type is \
              `{actual}`"
          else if reg == "rdx" then
            throwError "`mmap` is typed only for memory to read and write: `rdx` must hold \
              exactly 3, but its type is `{actual}`"
          else
            throwError "`mmap` is typed only for private memory that is not a file: `{reg}` \
              must hold exactly 0x22, but its type is `{actual}`"
      else if lhs.isAppOf ``MemTy.kinds then
        setGoals [g]
        try
          Tactic.withoutRecover do evalTactic (← `(tactic| rfl))
        catch _ =>
          throwError "`mmap`: the memory typing declares no kind {lhs.appArg!}"
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else
      setGoals [g]
      try
        Tactic.withoutRecover do
          evalTactic (← `(tactic| first
            | decide
            | rfl
            | exact List.cons_ne_nil _ _
            | (simp only [List.length_cons, List.length_nil]; omega)
            | (simp; done)))
      catch _ =>
        if t.isAppOf ``LE.le then
          throwError "`mmap`: the block's fields do not fit in the length in `rsi`"
        else if t.isAppOf ``Ne then
          throwError "`mmap`: a block needs at least one field"
        else
          throwError "`mmap`: every field of the new block must admit zero, since that is \
            what fresh memory holds: an integer, or a value that may be null"
  let some rest := rest? | throwError "ty_mmap: unexpected goals"
  setGoals [rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ others)

/-- `ty_mmap fields`: the `syscall` here is an `mmap` for fresh memory, to be
used as a block with these fields. Afterwards `rax` holds an error number or
a writable pointer to the new block; `ty_err` tells them apart. -/
elab_rules : tactic
  | `(tactic| ty_mmap $fields) => do
    typeMmap (← `(linux_mmap (fields := $fields) (len := ?_) rfl ?_ ?_ ?_ ?_ ?_ ?_))

/-- `ty_mmap_kind tag`: as `ty_mmap`, for a block of the declared kind
`tag`. Afterwards `rax` holds an error number or a writable pointer to a
block of that kind. -/
elab_rules : tactic
  | `(tactic| ty_mmap_kind $tag) => do
    typeMmap (← `(linux_mmap_kind (tag := $tag) (fields := ?_) (len := ?_) rfl ?_ ?_ ?_ ?_
      ?_ ?_ ?_))

/-- `ty_into h` types the instruction here and ends the block with it. Use it
when the next instruction is at a label and the block should hand over to
that label's context instead of typing the label's code a second time; `h`
is the fact that the label allows some context, as for `ty_accept`. -/
macro_rules
  | `(tactic| ty_into $h) =>
    `(tactic| (refine BlockOk.last rfl (HasType.straight (Γ' := ?_) ?st ?acc)
               case' st => ty_straight
               case' acc => ty_accept $h))

end TypedAsm
