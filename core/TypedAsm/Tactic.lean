import Lean
import TypedAsm.Program
import TypedAsm.Fn
import TypedAsm.Print

/-!
# Tactics for typing programs

These build typing derivations; the kernel checks the result, so nothing here
is trusted. They handle the mechanical parts and leave as goals whatever
needs an argument, typically a fact about values at a branch.

* `ty_steps` types the straight-line instructions at the start of a block.
* `ty_step` types one.
* `ty_straight` types a single instruction; the two above are built on it.
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
theorem Straight.freeFrame' {next : BitVec 64} {Γ : Ctx} {k : Nat} {imm : BitVec 32}
    (hk : slotDisp k imm) (hlen : (Γ.stack.take k).length = k) :
    Straight next Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm))
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

/-- Simplifies the context in a block goal. Each rule wraps the previous
context in a record update that mentions it once per field, so without this
the context would multiply in size with every instruction. -/
macro "ty_normalize" : tactic =>
  `(tactic| try dsimp only [CtxOf.setReg, CtxOf.afterAlu, CtxOf.afterSyscall, AluOp.writesDst,
      ↓reduceIte])

/-! ## Choosing the rule from the instruction

The tactics below are metaprograms. They look at the instruction, try only
the rules written for its shape, and when none applies they say which
premise of each stood in the way. -/

open Lean Meta Elab Tactic

/-- The straight-line rules that can type an instruction of this shape, most
informative first. An empty list means the type system has no rule for it. -/
def Instr.rules : Instr → List Name
  | .nop => [``Straight.nop]
  | .mov .w64 (.rm_r (.reg _) _) => [``Straight.movRR64]
  | .mov .w32 (.rm_r (.reg _) _) => [``Straight.movRR32]
  | .mov _ (.rm_i (.reg _) _) => [``Straight.movRI]
  | .movAbs _ _ => [``Straight.movAbs]
  | .lea .w64 _ (.rip _) => [``Straight.leaRip, ``Straight.lea]
  | .lea _ _ _ => [``Straight.lea]
  | .mov .w64 (.r_m _ (.sib (some .rsp) none _)) => [``Straight.loadStack]
  | .mov .w64 (.r_m _ (.sib (some _) none _)) => [``Straight.loadField]
  | .mov .w32 (.r_m _ (.sib (some _) none _)) => [``Straight.loadField32]
  | .mov .w64 (.rm_r (.mem (.sib (some .rsp) none _)) _) => [``Straight.storeStack]
  | .mov .w64 (.rm_r (.mem (.sib (some _) none _)) _) =>
    [``Straight.storeField, ``Straight.storeIntR]
  | .mov .w32 (.rm_r (.mem (.sib (some _) none _)) _) => [``Straight.storeIntR]
  | .mov _ (.rm_i (.mem (.sib (some _) none _)) _) => [``Straight.storeIntI]
  | .store8 (.sib (some _) none _) _ => [``Straight.store8Field]
  | .movzx _ _ _ (.mem (.sib (some _) none _)) => [``Straight.movzxField]
  | .movsx _ _ _ (.mem (.sib (some _) none _)) => [``Straight.movsxField]
  | .push _ => [``Straight.push]
  | .pop _ => [``Straight.pop]
  | .alu .sub .w64 (.rm_i (.reg .rsp) _) => [``Straight.allocFrame]
  | .alu .add .w64 (.rm_i (.reg .rsp) _) => [``Straight.freeFrame']
  | .alu _ .w64 (.rm_i (.reg _) _) => [``Straight.aluExact, ``Straight.addPtr, ``Straight.aluRI]
  | .alu _ _ (.rm_i (.reg _) _) => [``Straight.aluRI]
  | .alu _ .w64 (.rm_r (.reg _) _) => [``Straight.aluExactRR, ``Straight.aluRR]
  | .alu _ _ (.rm_r (.reg _) _) => [``Straight.aluRR]
  | .alu _ .w64 (.r_m _ (.sib (some _) none _)) => [``Straight.aluMem]
  | .test .w64 (.reg _) (.reg _) => [``Straight.testExact, ``Straight.test]
  | .test _ (.reg _) _ => [``Straight.test]
  | _ => []

/-- Whether the instruction can send control somewhere other than the next
instruction, which is where a block ends. -/
def Instr.endsBlock : Instr → Bool
  | .jmp _ | .jcc _ _ | .call _ | .ret | .syscall | .ud2 => true
  | _ => false

/-- Every straight-line rule, for instructions whose shape is not known. -/
def allStraightRules : List Name := [``Straight.movRR64, ``Straight.movRR32, ``Straight.movRI, ``Straight.movAbs, ``Straight.leaRip, ``Straight.lea, ``Straight.loadStack, ``Straight.loadField, ``Straight.storeStack, ``Straight.storeField, ``Straight.storeIntR, ``Straight.storeIntI, ``Straight.store8Field, ``Straight.push, ``Straight.pop, ``Straight.allocFrame, ``Straight.freeFrame', ``Straight.aluExact, ``Straight.aluExactRR, ``Straight.loadField32, ``Straight.movzxField, ``Straight.movsxField, ``Straight.addPtr, ``Straight.aluMem, ``Straight.aluRR, ``Straight.aluRI, ``Straight.testExact, ``Straight.test, ``Straight.nop]

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

/-- The name of a register, if the term is one. -/
private def regName? (e : Expr) : Option String :=
  match e.constName? with
  | some (.str ``Reg n) => some n
  | _ => none

/-- Describes, in terms of the program, a rule premise that could not be proved. -/
private def describePremise (ty : Expr) : MetaM MessageData := do
  let ty ← instantiateMVars ty
  if let some (_, lhs, rhs) := ty.eq? then
    -- what a register must hold
    if lhs.isAppOfArity ``CtxOf.regs 3 then
      let reg := (regName? lhs.appArg!).getD "the register"
      let actual ← ppClean (← reduce lhs)
      let wanted :=
        if rhs.isAppOf ``Ty.ptr then
          if rhs.getAppArgs[1]!.isConstOf ``Bool.true then "a writable pointer" else "a pointer"
        else if rhs.isAppOf ``Ty.eq then "an exactly known value"
        else "a value of another type"
      return m!"`{reg}` must hold {wanted}, but its type is `{actual}`"
    if lhs.isAppOf ``AluOp.readsCarry then
      return m!"this rule does not cover operations that read the carry flag"
    if lhs.isAppOfArity ``CtxOf.room 2 then
      return m!"there is not enough free stack: the context has room for {← ppClean (← reduce lhs)}"
    -- a field or stack slot lookup
    let actual ← reduce lhs
    if actual.isAppOf ``Option.none then
      return m!"there is no field or stack slot at that offset"
    if rhs.isAppOf ``Option.some && actual.isAppOf ``Option.some then
      return m!"the field must have type `{← ppClean rhs.appArg!}`, but has type \
        `{← ppClean actual.appArg!}`"
    return m!"needs `{← ppClean ty}`, but the left side is `{← ppClean actual}`"
  if ty.isAppOf ``slotDisp then
    return m!"the displacement must be a non-negative multiple of 8"
  if ty.isAppOf ``innerDisp then
    return m!"the displacement must be non-negative"
  if ty.isAppOfArity ``Sub 2 then
    return m!"a value of type `{← ppClean (← reduce ty.appFn!.appArg!)}` cannot be stored \
      where `{← ppClean ty.appArg!}` is required"
  if ty.isAppOfArity ``Ne 3 && (regName? ty.appArg!) == some "rsp" then
    return m!"`rsp` cannot be this operand"
  if ty.isAppOf ``LE.le then
    return m!"the access would cross the end of an 8-byte field"
  if ty.isForall then
    return m!"the operation reads the carry flag, which is not known to be defined here"
  return m!"needs `{← ppClean ty}`"

/-- Says why a rule did not apply: the first premise that could not be proved. -/
private def explainRule (rule : Name) : TacticM MessageData := do
  let saved ← saveState
  let name := rule.components.getLast!
  try
    try
      evalTactic (← `(tactic| refine' $(mkIdent rule) ..))
    catch _ =>
      return m!"{name}: is for a different form of this instruction"
    let goals ← getGoals
    -- Premises are attempted in order and then again, as in `ty_rule`, so that
    -- what is reported is a premise that fails once everything else is known.
    let mut failed : Array Expr := #[]
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
        if !ok && pass == 1 then
          failed := failed.push (← instantiateMVars (← g.getType))
    -- A premise about the displacement is reported first: the others cannot
    -- be judged until it holds. After that, prefer a premise with no unknowns.
    let isDisp (e : Expr) : Bool := e.isAppOf ``slotDisp || e.isAppOf ``innerDisp
    let chosen := (failed.find? isDisp <|> failed.find? (!·.hasExprMVar) <|> failed[0]?)
    match chosen with
    | some ty => return m!"{name}: {← describePremise ty}"
    | none => return m!"{name}: every premise holds separately, but not together"
  finally
    saved.restore

/-- Types the instruction in a `Straight next Γ i ?Γ'` goal, or explains why not. -/
def typeStraight : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``Straight 4 do
    throwError "ty_straight: the goal is not of the form `Straight next Γ i Γ'`"
  let instrExpr := ty.getAppArgs[2]!
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
    throwError "the type system has no rule for {shown}"
  let mut msg := m!"cannot type {shown} in the current context"
  for rule in rules do
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

/-- Types the first instruction of a block goal if it is a straight-line
instruction, leaving the rest of the block as the main goal. -/
private def typeStep : TacticM StepResult := withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
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
  if let some instr ← knownInstr instrTy.getAppArgs[2]! then
    if instr.endsBlock then
      saved.restore
      return .endOfBlock instr
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

end TypedAsm
