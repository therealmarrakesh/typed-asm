import TypedAsm.Tactic.Lemmas

/-!
# The tactics: basic

Comparing contexts, side conditions, bringing a goal to the form it is kept in, and the small tactics the rest are built from.
-/

namespace TypedAsm

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
def headForm? (g : Lean.MVarId) : Lean.Meta.MetaM (Option (Lean.MVarId × Bool)) :=
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
      try simp only [BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceSignExtend,
        BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero]))
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
         | exact Sub.strLess _
         | (refine Sub.orErrMono ?_; ty_sub)
         | (refine Sub.orErr ?_; ty_sub)
         -- the stack pointer's type after moves that cancel or add up
         | (simp only [Ty.shift_shift]
            first | exact Sub.refl _ | (refine Sub.shift_congr ?_; decide))))

/-- Compares register types one register at a time. Registers it cannot
settle are left as goals. -/
macro "sub_regs" : tactic =>
  `(tactic| (intro r hr; cases r <;> first | exact absurd rfl hr | (try ty_sub)))

/-- Compares two pieces of the stack: the same, a typed value at a weaker
type, or what one holds forgotten. -/
macro "ty_subshape" : tactic =>
  `(tactic| focus first
    | exact SubShape.refl _
    | (refine SubShape.slot ?_; ty_sub)
    | exact SubShape.raw _
    -- each typed value wanted is found among those there, at a weaker type
    | (refine SubShape.mk rfl ?_
       repeat (first
         | (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩
            first
            | (refine ⟨_, List.mem_cons_self .., rfl, ?_⟩; ty_sub)
            | (refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, ?_⟩; ty_sub)
            | (refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
                rfl, ?_⟩; ty_sub)
            | (refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_self ..))), rfl, ?_⟩; ty_sub))
         | (intro _ h; cases h))
       done))

/-- Compares two stacks piece by piece. -/
macro "ty_stack" : tactic =>
  `(tactic| first
    | exact SubList.refl _
    | ((repeat (first
        | exact SubList.refl _
        | (refine SubList.cons ?_ ?_; ty_subshape))); done))

/-- Shows one flags predicate implies another, in the common cases. -/
macro "ty_flags" : tactic => do
  -- `rfl` must be written without macro hygiene, or `rintro` takes it for a name.
  let subst := Lean.mkIdent `rfl
  `(tactic| first
    | exact fun _ h => h
    | exact fun _ _ => trivial
    | (rintro f $subst:ident; exact Flags.ofResult_defined _ _ _))

open Lean Meta Elab Tactic in
/-- Proves `CtxSub Γ Δ` when `Δ` is still to be chosen, by choosing `Γ`: a
label that allows every context allows this one. -/
elab "ctx_same" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOfArity ``CtxSub 2 && t.appArg!.isMVar do
    throwError "the context to compare with is known"
  evalTactic (← `(tactic| exact CtxSub.refl _))

/-- Proves `CtxSub Γ Δ`. The stack, room and flags must be settled
automatically; register comparisons it cannot settle are left as goals. -/
macro "ctx_sub" : tactic =>
  `(tactic| first | ctx_same | (
    refine CtxSub.mk ?regs ?stack ?room ?flags ?sp ?owned ?above
    case owned => rfl
    case above => first | rfl | omega | (dsimp only; omega)
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
       first
         | assumption
         | omega
         | (simp; first | assumption | omega)
         | (simp [Scale.shift]; first | assumption | omega))
    -- a slot after the first of a list that goes on as a run of one type
    | (show (_ :: _)[_ + 1]? = _
       rw [List.getElem?_cons_succ]
       refine getElem?_replicate_of_lt ?_
       first | assumption | omega | (simp; first | assumption | omega))
    -- a slot after the first, in the first of two runs that follow it
    | (show (_ :: _)[_ + 1]? = _
       rw [List.getElem?_cons_succ,
         List.getElem?_append_left (by simp only [List.length_replicate]; omega)]
       refine getElem?_replicate_of_lt ?_
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

macro "ty_index_core" : tactic =>
  `(tactic| first
    | (refine index8_slot _ _ ?_ ?_ <;> decide)
    | (refine index_bytes _ _ _ ?_; decide))

open Lean Meta Elab Tactic in
/-- Proves which byte a scaled index lands on. A goal with no scaled index
in it is refused at once: matching it against the lemmas for one would have
the two sides worked out at length before the mismatch showed. -/
elab "ty_index" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some sh := t.find? (·.isAppOfArity ``HShiftLeft.hShiftLeft 6)
    | throwError "no scaled index here"
  -- The lemma for whole eight-byte cells is tried only on an index scaled
  -- by eight: on another scale it fails, but only after the two sides have
  -- been worked out at length.
  let by8 ← try
      let n ← whnf sh.appArg!
      let k? := match n with
        | .lit (.natVal k) => some k
        | _ => if n.isConstOf ``Nat.zero then some 0 else n.nat?
      pure (k?.isNone || k? == some 3)
    catch _ => pure true
  if by8 then evalTactic (← `(tactic| ty_index_core))
  else evalTactic (← `(tactic| (refine index_bytes _ _ _ ?_; decide)))

open Lean Meta Elab Tactic in
/-- Writes out a shape that the goal asks the size or the typed values of,
where it is named by a definition: `node.size` becomes the size of what
`node` is defined as. Fails if there is nothing to write out. -/
elab "ty_shape_open" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let fns := [``ShapeOf.size, ``ShapeOf.free, ``ShapeOf.valAt, ``ShapeOf.sole]
  let changed ← IO.mkRef false
  let target' ← Meta.transform target (pre := fun e => do
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConst && fns.contains f.constName! && args.size ≥ 2 then
      let S := args[1]!
      if S.isAppOf ``ShapeOf.mk || S.hasLooseBVars then return .continue
      let S' ← whnf S
      if S'.isAppOf ``ShapeOf.mk then
        changed.set true
        return .continue (mkAppN f (args.set! 1 S'))
    return .continue)
  unless ← changed.get do throwError "no shape to write out"
  replaceMainGoal [← goal.replaceTargetDefEq target']

/-! An array of `n` elements of one shape, reached three ways: through a
pointer stepped along it (`a * k + f`: element `k`, byte `f` of it), at a
fixed number of bytes from its start, and through an index scaled by the
element's size. -/

namespace ShapeOf

variable {S : Shape} {n a k f o i off m : Nat} {t : Ty}

theorem valAt_rep_elem (hf : S.fits = true) (ha : a = S.size) (hi : k < n)
    (hv : S.valAt f = some t) : (S.rep n).valAt (a * k + f) = some t := by
  subst ha; rw [Nat.mul_comm]; exact valAt_rep hf hi hv

theorem sole_rep_elem (hf : S.fits = true) (ha : a = S.size) (hi : k < n)
    (hin : f + 8 ≤ S.size) (hs : S.sole f = true) : (S.rep n).sole (a * k + f) = true := by
  subst ha; rw [Nat.mul_comm]; exact sole_rep hf hi hin hs

theorem free_rep_elem (hf : S.fits = true) (ha : a = S.size) (hi : k < n)
    (hin : f + m ≤ S.size) (hfree : S.free f m = true) :
    (S.rep n).free (a * k + f) m = true := by
  subst ha; rw [Nat.mul_comm]; exact free_rep hf hi hin hfree

theorem valAt_rep_at (hf : S.fits = true) (hi : o / S.size < n)
    (hv : S.valAt (o % S.size) = some t) : (S.rep n).valAt o = some t := by
  have := valAt_rep hf hi hv
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

theorem sole_rep_at (hf : S.fits = true) (hi : o / S.size < n)
    (hin : o % S.size + 8 ≤ S.size) (hs : S.sole (o % S.size) = true) :
    (S.rep n).sole o = true := by
  have := sole_rep hf hi hin hs
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

theorem free_rep_at (hf : S.fits = true) (hi : o / S.size < n)
    (hin : o % S.size + m ≤ S.size) (hfree : S.free (o % S.size) m = true) :
    (S.rep n).free o m = true := by
  have := free_rep hf hi hin hfree
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

theorem valAt_rep_idx (hf : S.fits = true) (h8 : S.size = 8) (hoff : off % 8 = 0)
    (hi : off / 8 + i < n) (hv : S.valAt 0 = some t) :
    (S.rep n).valAt (off + 8 * i) = some t := by
  have := valAt_rep hf hi hv
  rw [h8] at this
  rwa [show (off / 8 + i) * 8 + 0 = off + 8 * i by omega] at this

theorem sole_rep_idx (hf : S.fits = true) (h8 : S.size = 8) (hoff : off % 8 = 0)
    (hi : off / 8 + i < n) (hs : S.sole 0 = true) :
    (S.rep n).sole (off + 8 * i) = true := by
  have := sole_rep hf hi (f := 0) (by omega) hs
  rw [h8] at this
  rwa [show (off / 8 + i) * 8 + 0 = off + 8 * i by omega] at this

end ShapeOf

/-- Proves a premise about an element of an array: a bound on which element
it is, from the hypotheses, or a fact about the element's own shape, by
working it out. -/
macro "ty_elem" : tactic =>
  `(tactic| first
    | exact rfl
    | decide
    | assumption
    | omega
    | ((try ty_shape_open)
       simp only [ShapeOf.raw, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
         Nat.reduceSub, Nat.zero_add, Nat.add_zero, BitVec.reduceToNat, BitVec.toNat_ofNat,
         Nat.reducePow, List.cons_append, List.nil_append, stackOff_zero, stackOff_cons_succ,
         ShapeOf.slot_size, ShapeOf.raw_size]
       first | assumption | omega))

open Lean Meta Elab Tactic in
/-- Proves a premise about an element of an array if it is a proposition,
and passes over it if it is a value still to be found: another premise
settles that. -/
elab "ty_elem_goal" : tactic => do
  if ← isProp (← getMainTarget) then
    evalTactic (← `(tactic| ty_elem))

macro "ty_val_core" : tactic =>
  `(tactic| first
    | (refine' ShapeOf.valAt_rep_elem ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.sole_rep_elem ?_ ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.free_rep_elem ?_ ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.valAt_rep_idx ?_ ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.sole_rep_idx ?_ ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.valAt_rep_at ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.sole_rep_at ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.free_rep_at ?_ ?_ ?_ ?_ <;> ty_elem_goal))

open Lean Meta Elab Tactic in
/-- Proves which typed value an array has at a place in one of its elements,
that it is the only one there, or that bytes of an element are plain. A goal
about a shape that is not an array is refused at once: matched against the
lemmas for arrays, the shape would be worked out in full by each of them
before the mismatch showed. -/
elab "ty_val" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let isRep (e : Expr) : Bool := (e.find? (·.isConstOf ``ShapeOf.rep)).isSome
  let mut found := isRep t
  unless found do
    -- the shape may be named by a definition: look a few definitions deep
    let fns := [``ShapeOf.valAt, ``ShapeOf.sole, ``ShapeOf.free]
    if let some app := t.find? (fun e => e.isApp && fns.any e.getAppFn.isConstOf) then
      if app.getAppNumArgs ≥ 2 then
        let mut S := app.getAppArgs[1]!
        for _ in [0:4] do
          if isRep S then found := true; break
          match ← unfoldDefinition? S with
          | some S' => S := S'
          | none => break
        -- A shape still unknown is passed over: the premise that settles
        -- it comes first, and this one is come back to.
  unless found do throwError "not an array"
  evalTactic (← `(tactic| ty_val_core))

/-- Proves a fact with no unknowns in it from the hypotheses: the fact
itself, or one side of an "or". A goal with unknowns is refused, since a
hypothesis of the right shape would settle them whether or not it was the
one meant. -/
syntax "ty_known" : tactic

/-- Proves a side condition of a typing rule, or fails. -/
syntax "ty_side" : tactic

/-- Proves a fact of arithmetic about the numbers a program computes with:
a bound, or that two exactly known values are the same. The definitions of
the file at hand that the fact and the comparisons among the hypotheses
mention are opened, and what an operation's result is is written out; the
rest is left to `omega` and `bv_omega`. -/
syntax "ty_arith" : tactic

/-- Applies one typing rule and proves all its premises, or fails. The
premises are attempted in order and then again, because proving one can
determine what an earlier one refers to. -/
syntax "ty_rule " term : tactic

/-- Like `ty_rule`, but proves the premises strictly in order and gives up
at the first that fails. For rules whose first premise computes what the
others refer to, where carrying on after a failure would be slow. -/
syntax "ty_rule_ordered " term : tactic

macro "ty_operand_any" : tactic =>
  `(tactic| first
    | ty_rule_ordered ReadOk.reg | ty_rule_ordered ReadOk.slot | ty_rule_ordered ReadOk.slotIndexed
    | ty_rule_ordered ReadOk.field
    | ty_rule_ordered ReadOk.owned | ty_rule_ordered WriteIntOk.owned
    | ty_rule_ordered ReadOk.ownedAt | ty_rule_ordered WriteIntOk.ownedAt
    | ty_rule_ordered WriteIntOk.ownedClear
    | ty_rule_ordered ReadOk.indexed | ty_rule_ordered ReadOk.global_of
    | ty_rule_ordered WriteIntOk.reg | ty_rule_ordered WriteIntOk.slot
    | ty_rule_ordered WriteIntOk.slotIndexed
    | ty_rule_ordered WriteIntOk.field | ty_rule_ordered WriteIntOk.indexed
    | ty_rule_ordered WriteIntOk.global_of
    | ty_rule_ordered Holds.reg | ty_rule_ordered Holds.slot | ty_rule_ordered Holds.field
    | ty_rule_ordered Holds.indexed | ty_rule_ordered Holds.global_of
    | ty_rule_ordered ReadOk.table_of | ty_rule_ordered ReadOk.placed_of
    | ty_rule_ordered WriteIntOk.table_of | ty_rule_ordered WriteIntOk.placed_of
    | ty_rule_ordered Holds.table_of | ty_rule_ordered Holds.placed_of)

open Lean Meta Elab Tactic in
/-- Proves that an operand can be read, can be written, or holds a value of
a given type: it is a register, a stack slot, a field of a pointer, or a field
of a block at a fixed address. Only the rules for the judgment asked and for
the operand's own form are tried, in the order `ty_operand_any` has them;
where the form is not yet known, all are. -/
elab "ty_operand" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let (judgment, rm?) :=
    if t.isAppOfArity ``ReadOk 5 then (``ReadOk, some t.getAppArgs[4]!)
    else if t.isAppOfArity ``WriteIntOk 6 then (``WriteIntOk, some t.getAppArgs[4]!)
    else if t.isAppOfArity ``Holds 5 then (``Holds, some t.getAppArgs[3]!)
    else (Name.anonymous, none)
  let some rm := rm? | evalTactic (← `(tactic| ty_operand_any))
  -- the operand's form: a register; or memory through the stack pointer or
  -- another register, with or without an index; or at a fixed distance
  let rm ← whnfR rm
  let form : Option String ←
    if rm.isAppOfArity ``RM.reg 1 then pure (some "reg")
    else if rm.isAppOfArity ``RM.mem 1 then do
      let m ← whnfR rm.appArg!
      if m.isAppOfArity ``Mem.rip 1 then pure (some "rip")
      else if m.isAppOfArity ``Mem.sib 3 then
        let base ← whnfR m.getAppArgs[0]!
        let index ← whnfR m.getAppArgs[1]!
        if base.isAppOfArity ``Option.none 1 then
          if index.isAppOfArity ``Option.some 2 then pure (some "absIndex")
          else if index.isAppOfArity ``Option.none 1 then pure (some "abs")
          else pure none
        else if !(base.isAppOfArity ``Option.some 2) then pure none
        else
          let b ← whnfR base.appArg!
          let indexed := index.isAppOfArity ``Option.some 2
          let plain := index.isAppOfArity ``Option.none 1
          if !(indexed || plain) || !b.isConst then pure none
          else if b.isConstOf ``Reg.rsp then pure (some (if indexed then "spIndex" else "sp"))
          else pure (some (if indexed then "index" else "base"))
      else pure none
    else pure none
  let some form := form | evalTactic (← `(tactic| ty_operand_any))
  let rules : List Name :=
    match judgment, form with
    | ``ReadOk, "reg" => [``ReadOk.reg]
    | ``ReadOk, "sp" => [``ReadOk.slot, ``ReadOk.owned, ``ReadOk.ownedAt]
    | ``ReadOk, "spIndex" => [``ReadOk.slotIndexed, ``ReadOk.owned, ``ReadOk.ownedAt]
    | ``ReadOk, "base" => [``ReadOk.field, ``ReadOk.owned, ``ReadOk.ownedAt]
    | ``ReadOk, "index" => [``ReadOk.owned, ``ReadOk.ownedAt, ``ReadOk.indexed]
    | ``ReadOk, "rip" => [``ReadOk.owned, ``ReadOk.ownedAt, ``ReadOk.global_of]
    | ``WriteIntOk, "reg" => [``WriteIntOk.reg]
    | ``WriteIntOk, "sp" =>
      [``WriteIntOk.owned, ``WriteIntOk.ownedAt, ``WriteIntOk.ownedClear, ``WriteIntOk.slot]
    | ``WriteIntOk, "spIndex" =>
      [``WriteIntOk.owned, ``WriteIntOk.ownedAt, ``WriteIntOk.ownedClear, ``WriteIntOk.slotIndexed]
    | ``WriteIntOk, "base" =>
      [``WriteIntOk.owned, ``WriteIntOk.ownedAt, ``WriteIntOk.ownedClear, ``WriteIntOk.field]
    | ``WriteIntOk, "index" =>
      [``WriteIntOk.owned, ``WriteIntOk.ownedAt, ``WriteIntOk.ownedClear, ``WriteIntOk.indexed]
    | ``WriteIntOk, "rip" =>
      [``WriteIntOk.owned, ``WriteIntOk.ownedAt, ``WriteIntOk.ownedClear, ``WriteIntOk.global_of]
    | ``ReadOk, "abs" => [``ReadOk.placed_of]
    | ``ReadOk, "absIndex" => [``ReadOk.table_of, ``ReadOk.placed_of]
    | ``WriteIntOk, "abs" => [``WriteIntOk.placed_of]
    | ``WriteIntOk, "absIndex" => [``WriteIntOk.table_of, ``WriteIntOk.placed_of]
    | ``Holds, "abs" => [``Holds.placed_of]
    | ``Holds, "absIndex" => [``Holds.table_of, ``Holds.placed_of]
    | ``Holds, "reg" => [``Holds.reg]
    | ``Holds, "sp" => [``Holds.slot]
    | ``Holds, "base" => [``Holds.field]
    | ``Holds, "index" => [``Holds.indexed]
    | ``Holds, "rip" => [``Holds.global_of]
    | _, _ => []
  if rules.isEmpty then evalTactic (← `(tactic| ty_operand_any))
  else
    let goal ← getMainGoal
    for r in rules do
      let saved ← saveState
      try
        setGoals [goal]
        evalTactic (← `(tactic| ty_rule_ordered $(mkIdent r)))
        return
      catch _ => saved.restore
    throwError "no rule for this operand applies"

/-- Shows that a known offset falls inside a block of known length. -/
macro "ty_inside" : tactic =>
  `(tactic| first
    | decide
    | (simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
         ShapeOf.append, ShapeOf.rep_size,
         List.length_replicate, List.length_set, List.length_cons, List.length_nil,
         List.length_take, List.length_drop, List.length_append]
       first | decide | omega))

/-- Proves that an address is some bytes into an owned block: the block is
looked for among the first few the context lists, and is the one the address
falls inside. The address may be written from the block's own start or from
that of a block next to it, as it is or with a known amount added. -/
syntax "ty_owned_at" : tactic

/-- A block's own address is that of its first byte. -/
theorem owned_addr0 (a : BitVec 64) : a = a + BitVec.ofNat 64 0 := by simp

/-- An address a known number of bytes into a block. -/
theorem owned_addrOff (a d : BitVec 64) : a + d = a + BitVec.ofNat 64 d.toNat := by simp

/-- The address reached through an index with any scale, as a number of
bytes from the base. -/
theorem owned_addrScaled (a c : BitVec 64) (sc : Scale) (disp : BitVec 32)
    (hd : disp.toNat < 2 ^ 31) :
    a + (c <<< sc.shift) + disp.signExtend 64
      = a + BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift + disp.toNat) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize c.toNat * 2 ^ sc.shift = m
  omega

/-- Proves which byte of an owned block an address reached through an index
is that of. -/
syntax "ty_owned_byte" : tactic

/-- Proves which piece of the stack a byte above the stack pointer is in, and
which byte of the piece: the pieces the context lists are tried from the top. -/
syntax "ty_stack_at" : tactic

/-- Shows a fact about where a piece of the stack starts and how long it
is: that a byte or a run of bytes is inside it, say. -/
macro "ty_stack_in" : tactic =>
  `(tactic| first
    | decide
    | omega
    | (simp only [List.cons_append, List.nil_append, ShapeOf.rep_size, ShapeOf.slot_size,
         ShapeOf.raw_size, stackOff_zero,
         stackOff_cons_succ, Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat,
         BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
         Nat.reduceSub, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.pow_zero]
       first | omega | decide)
    | (simp only [List.cons_append, List.nil_append, ShapeOf.rep_size, ShapeOf.slot_size,
         ShapeOf.raw_size, stackOff_zero,
         stackOff_cons_succ, Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat,
         BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
         Nat.reduceSub, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.pow_zero,
         Nat.le_refl]
       done))

open Lean Meta Elab Tactic in
/-- Fails unless the goal is a proposition. A rule's unknowns are goals too,
and a side-condition tactic let loose on one of them would fill it with
whatever of the right type lies nearest. -/
elab "ty_prop_only" : tactic => do
  unless ← isProp (← getMainTarget) do
    throwError "not a proposition"

open Lean Meta Elab Tactic in
unsafe def evalLocateUnsafe (e : Expr) : MetaM (Option (BitVec 64 × Nat)) := do
  evalExpr (Option (BitVec 64 × Nat)) (← inferType e) e

open Lean Meta Elab Tactic in
/-- The block a closed address is found in, and how far into it. -/
@[implemented_by evalLocateUnsafe]
opaque evalLocate (e : Expr) : MetaM (Option (BitVec 64 × Nat))

open Lean Meta Elab Tactic in
/-- Finds the block an address is in, for a closed address: the search is
run, and the block's address and the distance into it are written out as
numbers. Left to `rfl` they would stand as the search itself, and every
later premise that mentions them would have to work it out again. -/
elab "ty_locate" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "not an equation"
  unless lhs.isAppOf ``MemTy.locate do throwError "not a search for a block"
  if lhs.hasFVar || lhs.hasExprMVar then throwError "the address is not closed"
  let lit := toExpr (← evalLocate lhs)
  unless ← isDefEq rhs lit do throwError "no block is found there"
  g.assign (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs lit))
  replaceMainGoal []

/-- The alternatives of `ty_side`, for a goal that is not settled by
computation alone. -/
syntax "ty_side_search" : tactic

open Lean Meta Elab Tactic in
/-- A side condition that is a closed yes-or-no computation, such as whether
some bytes of a shape are plain, has the kernel work it out, and that is the
end of it either way: if the answer is no, nothing else will prove it, and
trying would have the unifier work the same computation out many times
over. One with a variable in it is tried the same way first, since the
answer may not turn on the variable, and goes on to the search if that does
not settle it. Anything else goes straight to the search. -/
elab "ty_side_core" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let yesNo := t.isAppOfArity ``Eq 3 && t.getAppArgs[0]!.isConstOf ``Bool && !t.hasExprMVar
  -- An equation whose left side is one of these is proved by working the
  -- side out, or by the one tactic that knows of it, or is among the
  -- hypotheses. Nothing else in the search could prove it, and a rule that
  -- does not apply fails on just such an equation.
  let lhsIs (n : Name) : Bool := t.isAppOfArity ``Eq 3 && t.getAppArgs[1]!.isAppOf n
  let narrow? : Option (TSyntax `tactic) ←
    if lhsIs ``MemTy.locate then
      -- an address with a variable in it is in no block that can be found
      -- by searching, and the search would run until its depth is used up
      if t.getAppArgs[1]!.hasFVar then pure (some (← `(tactic| ty_known)))
      else pure (some (← `(tactic| first | ty_locate | exact rfl | ty_known)))
    else if lhsIs ``CtxOf.regs || lhsIs ``MulDivOp.eval || lhsIs ``Ty.isInt then
      pure (some (← `(tactic| first | exact rfl | ty_known)))
    else if lhsIs ``CtxOf.room then
      pure (some (← `(tactic| first | exact rfl | omega | ty_known)))
    else if lhsIs ``ShapeOf.valAt || lhsIs ``ShapeOf.sole then
      -- at a place that turns on a variable the lookup cannot be worked
      -- out, and trying runs it until the depth allowed is used up
      let place := t.getAppArgs[1]!.appArg!
      let known ← if !place.hasFVar then pure true else
        try
          let v ← whnf place
          pure (v.isRawNatLit || v.nat?.isSome || v.isConstOf ``Nat.zero)
        catch _ => pure true
      if known then pure (some (← `(tactic| first | exact rfl | ty_val | ty_known)))
      else pure (some (← `(tactic| first | ty_val | ty_known)))
    else pure none
  if yesNo && !t.hasFVar then
    evalTactic (← `(tactic| decide +kernel))
  else if let some narrow := narrow? then
    if yesNo then evalTactic (← `(tactic| first | decide +kernel | ($narrow:tactic)))
    else evalTactic narrow
  else if yesNo then
    evalTactic (← `(tactic| first | decide +kernel | ty_side_search))
  -- A judgment with a tactic of its own goes to that tactic, or is found
  -- among the hypotheses: nothing else in the search could prove it, and
  -- trying everything else on it is most of what a failed rule costs.
  else if t.isAppOf ``StackAt then
    evalTactic (← `(tactic| first | ty_stack_at | ty_known))
  else if t.isAppOf ``OwnedAt then
    evalTactic (← `(tactic| first | ty_owned_at | ty_known))
  else if t.isAppOf ``OwnedByte then
    evalTactic (← `(tactic| first | ty_owned_byte | ty_known))
  else if t.isAppOf ``EaIs then
    evalTactic (← `(tactic| first
      | exact EaIs.base (by decide) rfl
      | exact EaIs.indexed (by decide) rfl rfl
      | exact EaIs.abs
      | exact EaIs.absIndexed rfl
      | ty_known))
  else if t.isAppOf ``Sub then
    evalTactic (← `(tactic| first | ty_sub | ty_known))
  else if t.isAppOf ``ReadOk || t.isAppOf ``WriteIntOk || t.isAppOf ``Holds then
    evalTactic (← `(tactic| first | ty_operand | ty_known))
  else if t.isAppOf ``byteDisp then
    evalTactic (← `(tactic| first | (refine byteDisp_of _ ?_; decide) | ty_known))
  else
    evalTactic (← `(tactic| ty_side_search))

macro_rules
  | `(tactic| ty_side) => `(tactic| ty_prop_only; ty_side_core)
  | `(tactic| ty_side_search) =>
    `(tactic| first
      -- which byte an index lands on, before anything else: left to `rfl`,
      -- the byte would be found as an unevaluated sum of the two addresses
      | ty_index
      -- not the `rfl` tactic: on an inequality it would compare the two sides
      -- as if for equality, working both out in full, before giving up
      | exact rfl
      | decide
      | exact EaIs.base (by decide) rfl
      | exact EaIs.indexed (by decide) rfl rfl
      | exact EaIs.abs
      | exact EaIs.absIndexed rfl
      | ty_owned_at
      | ty_owned_byte
      | ty_stack_at
      -- a bound against the length of a long list, without counting it out
      | (simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
           ShapeOf.append, ShapeOf.rep_size,
           List.length_replicate, List.length_set, List.length_cons, List.length_nil]
         first | decide | omega)
      -- a bound on a byte reached through an index, from a bound on the index
      | (simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
           ShapeOf.append, ShapeOf.rep_size,
           List.length_replicate, List.length_set, List.length_cons, List.length_nil,
           Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow,
           Nat.reduceMod,
           Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.pow_zero]
         omega)
      -- the same, against a shape named by a definition
      | (ty_shape_open
         simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
           ShapeOf.append, ShapeOf.rep_size,
           List.length_replicate, List.length_set, List.length_cons, List.length_nil,
           Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat, BitVec.reduceToNat,
           Nat.reducePow, Nat.reduceMod,
           Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.pow_zero]
         omega)
      -- bytes reached through an index keep clear of each typed value of the
      -- block, from a bound on the index
      | ((try ty_shape_open)
         simp only [ShapeOf.free, ShapeOf.clearOf, List.all_cons, List.all_nil, Bool.and_true,
           Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
           Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat, BitVec.reduceToNat,
           Nat.reducePow, Nat.reduceMod,
           Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.pow_zero]
         omega)
      | (refine byteDisp_of _ ?_; decide)
      | ty_stack_in
      | ty_val
      | ty_field
      | ty_sub
      | ty_carry
      | ty_decided
      | ty_cond_value
      | ty_known
      | ty_operand)

macro_rules
  | `(tactic| ty_rule $r) =>
    `(tactic| (((refine' $r .. <;> try ty_side) <;> try ty_side); done))

/-- A pointer stepped one element past element `b` of elements `a` bytes
long is at element `b + 1`: the form a loop's invariant is stated in. -/
theorem elem_succ (a b : Nat) : a * b + a = a * (b + 1) := rfl

open Lean Meta Simp in
/-- Decides a test of whether one named register is another, and takes the
branch. Looking a register up in a context leaves such tests behind. -/
dsimproc_decl regIte (ite (@Eq Reg _ _) _ _) := fun e => do
  let_expr ite _ c _ a b := e | return .continue
  let_expr Eq _ x y := c | return .continue
  let .const nx _ := x | return .continue
  let .const ny _ := y | return .continue
  unless (← isConstructorApp x) && (← isConstructorApp y) do return .continue
  return .visit (if nx == ny then a else b)

/-- Simplifies the context in a block goal, without changing its shape. Each
rule wraps the previous context in a record update that mentions it once per
field, so without this the context would multiply in size with every
instruction. -/
macro "ty_dsimp_core" : tactic =>
  `(tactic| dsimp only [↓regIte, RegMap.get, entryCtx, entryCtxArgs,
      CtxOf.setReg, CtxOf.moveSp, Ty.shift, CtxOf.afterAlu, CtxOf.afterSyscall,
      CtxOf.afterMulDiv,
      ShiftOp.apply, Scale.shift,
      ShiftOp.flagsAfter, Width.bits, Nat.reduceEqDiff, Nat.reduceBEq, ↓reduceIte,
      AluOp.writesDst, List.set_cons_zero, List.set_cons_succ, List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ, List.cons_append, List.nil_append, List.length_cons,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      stackOff_zero, stackOff_cons_succ, ShapeOf.slot_size, ShapeOf.raw_size,
      List.length_nil, List.drop_zero,
      Bool.cond_true, Bool.cond_false, Nat.add_zero, Nat.zero_add, BitVec.reduceToNat, Nat.reduceDiv,
      elem_succ,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
      BitVec.reduceSetWidth, BitVec.reduceSignExtend, BitVec.reduceAdd, BitVec.reduceSub,
      BitVec.reduceNeg, BitVec.reduceOfNat])

@[inherit_doc tacticTy_dsimp_core]
macro "ty_dsimp_ctx" : tactic => `(tactic| try ty_dsimp_core)

/-- Brings a block goal to the form it is kept in between instructions: the
address as a number, the register types as a table, and everything in the
context that can be worked out, worked out. A goal of another kind has its
context simplified. -/
syntax "ty_normalize" : tactic

/-- `ty_name r as v`: from here on, the value in register `r` is called `v`
and the register is typed as exactly `v`. Use it on a register typed as an
integer, for example one just loaded from memory, before testing it or
computing with it, so that what is learnt about the value can be used. -/
syntax "ty_name " term " as " ident : tactic

syntax "ty_name_slot " term " as " ident : tactic
syntax "ty_stack_split " "at " term : tactic
syntax "ty_stack_join " "at " term : tactic
syntax "ty_stack_detach " "at " term : tactic
syntax "ty_stack_attach" : tactic
syntax "ty_open " term : tactic
syntax "ty_null " term : tactic
syntax "ty_err " term " as " ident : tactic
syntax "ty_mmap " term : tactic
syntax "ty_mmap_kind " term : tactic
syntax "ty_into " term : tactic
syntax "ty_code_ptr_fwd " term " to " term : tactic
syntax "ty_fn_ptr_fwd " term " to " term : tactic
syntax "ty_byte " "as " ident : tactic
syntax "ty_mmap_own " "as " ident : tactic
syntax "ty_munmap" : tactic
syntax "ty_freeze " term : tactic
syntax "ty_freeze_kind " term " as " term : tactic
syntax "ty_split " term " at " term : tactic
syntax "ty_join " term : tactic
syntax "ty_own_first " term : tactic

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

/-- `ty_open r`: register `r` holds a pointer to a block of some kind. From
here on `r` is an ordinary pointer to a block of the shape the memory typing
lists for that kind, which can be loaded from and stored to. -/
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

/-- Whether an instruction's memory operand is addressed through the stack,
which decides the fault a bad address raises. -/
def Instr.onStack (i : Instr) : Bool :=
  (i.memOperand?.map Mem.onStack).getD false

end TypedAsm
