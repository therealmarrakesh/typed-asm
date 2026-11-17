import TypedAsm.Tactic.Walk

/-!
# The tactics: block

Control transfers, whole blocks, calls, and the tactics that say what cannot be read off a program.
-/

namespace TypedAsm

open Lean Meta Elab Tactic

/-! ## Control transfers

For a labelled program the tactic can find where control goes: it looks for
the label at the target address, then for a context allowed at that label
which the current context is at least as strong as. Whatever it cannot
settle is left as a goal: typically a fact about values that the target's
context demands, such as a loop bound. -/

/-- The constructors of the inductive type a term's type belongs to. -/
def ctorsOfType (ty : Expr) : MetaM (List Name) := do
  let ty ← whnf (← instantiateMVars ty)
  let some n := ty.getAppFn.constName? | return []
  match (← getEnv).find? n with
  | some (.inductInfo info) => return info.ctors
  | _ => return []

/-- Whether a proposition compares two values. -/
def isComparison (t : Expr) : Bool :=
  t.isAppOf ``LT.lt || t.isAppOf ``LE.le || t.isAppOf ``GT.gt || t.isAppOf ``GE.ge ||
  t.isAppOf ``Eq || t.isAppOf ``Ne || t.isAppOf ``Not

/-- How the report that a label has no context at all begins. A jump forward
to such a label is typed by typing what is there, in place. -/
def noContextDeclared : String := "no context is declared at label"

/-- Whether an error is the report that a label has no context at all. -/
def isNoContext (e : Exception) : TacticM Bool := do
  return (← e.toMessageData.toString).startsWith noContextDeclared

/-- Proves `Φ a Δ` for a labelled program: finds the label whose address is
`a` and a context allowed there. `check` runs once the context is chosen and
should fail if it is the wrong one; another is then tried. Returns the goals
`check` left, then the premises of the chosen context that remain unproved. -/
def proveAtLabel (g : MVarId) (check : TacticM (List MVarId)) :
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
        -- the two addresses are worked out as numbers and compared; the
        -- kernel checks the equation with the rest of the proof
        let t ← instantiateMVars (← addr.getType)
        let quick? ← (do
          let some (_, lhs, rhs) := t.eq? | return none
          let some x ← addrNat lhs | return none
          let some y ← addrNat rhs | return none
          return some (x == y, lhs) : MetaM (Option (Bool × Expr)))
        match quick? with
        | some (true, lhs) =>
          addr.assign (← mkExpectedTypeHint (← mkEqRefl lhs) t)
          pure true
        | some (false, _) =>
          atLabel.restore
          pure false
        | none =>
          discard <| runOn addr (do evalTactic (← `(tactic| rfl)))
          pure true
      catch _ =>
        atLabel.restore
        pure false
    unless found do continue
    let mut reasons : MessageData := m!""
    let mut declared := false
    for k in ← ctorsOfType (← fact.getType) do
      let atCtx ← saveState
      -- A context for some other label is passed over without comment.
      let premises? ← try
          pure (some (← runOn fact (do evalTactic (← `(tactic| refine' $(mkIdent k) ..)))))
        catch _ =>
          atCtx.restore
          pure none
      let some premises := premises? | continue
      declared := true
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
              runOn p (do evalTactic (← `(tactic| first | assumption | omega | decide | ty_arith)))
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
    unless declared do
      throwError "{noContextDeclared} `{c.components.getLast!}`: a label that is jumped back \
        to, called, or returned to must say what holds there"
    throwError "no context allowed at label `{c.components.getLast!}` accepts the current one{reasons}"
  throwError "there is no label at the target address"

/-- Fails if a register comparison left as a goal can never hold: the two
types are fully known and of different kinds. -/
def rejectImpossible (gs : List MVarId) : TacticM Unit := do
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
def proveAccepts (g : MVarId) : TacticM (List MVarId) := do
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
        -- say so when what differs is the blocks owned
        let sameOwned ← sub.withContext do
          try
            let args := (← instantiateMVars (← sub.getType)).getAppArgs
            let here ← mkAppM ``CtxOf.owned #[args[0]!]
            let there ← mkAppM ``CtxOf.owned #[args[1]!]
            withoutModifyingState (isDefEq here there)
          catch _ => pure true
        unless sameOwned do
          throwError "the blocks owned do not match: a block taken here must be given back \
            or frozen before control goes there"
        -- or what has been detached from the stack
        let sameAbove ← sub.withContext do
          try
            let args := (← instantiateMVars (← sub.getType)).getAppArgs
            let here ← whnf (← mkAppM ``CtxOf.above #[args[0]!])
            let there ← whnf (← mkAppM ``CtxOf.above #[args[1]!])
            if here.isRawNatLit && there.isRawNatLit then pure (here == there) else pure true
          catch _ => pure true
        unless sameAbove do
          throwError "what has been detached from the stack does not match: a piece detached \
            here must be attached again before control goes there"
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

elab_rules : tactic
  | `(tactic| ty_arith) => withMainContext do
    let env ← getEnv
    let own (e : Expr) (acc : Array Name) : Array Name :=
      e.foldConsts acc fun c acc =>
        if acc.contains c || c.isInternal || (env.getModuleIdxFor? c).isSome then acc
        else match env.find? c with
          | some (.defnInfo _) => acc.push c
          | _ => acc
    let mut names := own (← instantiateMVars (← getMainTarget)) #[]
    let mut hyps : Array Ident := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless isComparison ty do continue
      -- the condition itself is not one: what it says is among the others
      if ty.find? (·.isConstOf ``Cond.eval) |>.isSome then continue
      names := own ty names
      hyps := hyps.push (mkIdent d.userName)
    let defs := names.map mkIdent
    evalTactic (← `(tactic|
      (try simp only [$[$defs:ident],*, AluOp.apply, subBorrow_fst, addCarry_fst, imulTrunc_fst,
          BitVec.and_self, BitVec.setWidth_eq, BitVec.reduceSignExtend] at $[$hyps:ident]* ⊢
       first | omega | bv_omega)))

/-- Shows the flags decide a condition. -/
def decideCond : TacticM Unit := do
  let subst := mkIdent `rfl
  evalTactic (← `(tactic| first
    | (rintro f $subst:ident; exact ⟨_, rfl⟩)
    | exact Cond.decided_of_known (fun _ h => h) _
    | (refine Cond.decided_of_defined _ ?_; decide)))

/-- The goal among `gs` that came from the placeholder `?name`. Goals are
found by name because the order in which `refine` returns them is not fixed. -/
def goalNamed (gs : List MVarId) (name : Name) : TacticM MVarId := do
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
      runOn goal (do evalTactic (← `(tactic| refine BlockOk.step (Γ' := ?_) (by ty_fetch) ?instr ?rest)))
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
inductive Finish
  /-- The block is finished; these goals are left. -/
  | done (left : List MVarId)
  /-- A conditional jump was typed and the block continues in `rest`. -/
  | continues (rest : MVarId) (left : List MVarId)
  /-- A jump was typed by typing its target in place: each of these is a
  block still to be typed. -/
  | forks (blocks : List MVarId) (left : List MVarId)
  /-- This instruction needs information the tactic does not have. -/
  | needsHelp (msg : MessageData)

/-- Types a direct `call` that ends a block, to a function whose signature
is read from the context declared at the label it calls. -/
syntax "ty_call_auto" : tactic
syntax "ty_call_with " term : tactic
syntax "ty_call_returning " term:max term:max : tactic

/-- Whether a jump goes forward: to the instruction after it or beyond. -/
def jumpsForward : Instr → Bool
  | .jmp (.rel d) | .jcc _ d => !d.msb
  | _ => false

/-- Whether a code typing is made from a family of contexts given label by
label, so that the labels with a context of their own can be read off it;
or allows no context at all, so that there are none. -/
def declaresByLabel (Φ : Expr) : MetaM Bool := do
  let mut f := Φ
  for _ in [0:4] do
    if f.isAppOf ``CodeTy.ofLabels then break
    -- a typing that allows no context anywhere: its labels are known, and
    -- there are none
    if let .lam _ _ (.lam _ _ b _) _ := f then
      if b.isConstOf ``False then return true
    let some f' ← unfoldDefinition? f | return false
    f := f'.headBeta
  unless f.isAppOf ``CodeTy.ofLabels && f.getAppNumArgs ≥ 3 do return false
  let args := f.getAppArgs
  let .const tn _ := args[args.size - 1]!.getAppFn | return false
  let some (.inductInfo _) := (← getEnv).find? tn | return false
  return true

/-- The addresses of the labels a labelled code typing declares a context
at: where a block may hand over to another. -/
def declaredLabels (Φ : Expr) : MetaM (Array Nat) := do
  let mut f := Φ
  for _ in [0:4] do
    if f.isAppOf ``CodeTy.ofLabels then break
    let some f' ← unfoldDefinition? f | return #[]
    f := f'.headBeta
  unless f.isAppOf ``CodeTy.ofLabels && f.getAppNumArgs ≥ 3 do return #[]
  let args := f.getAppArgs
  let T := args[args.size - 1]!
  let base := args[args.size - 2]!
  let prog := args[args.size - 3]!
  let .const tn _ := T.getAppFn | return #[]
  let some (.inductInfo info) := (← getEnv).find? tn | return #[]
  let mut labels : Array Name := #[]
  for c in info.ctors do
    let some ci := (← getEnv).find? c | continue
    let l ← forallTelescope ci.type fun _ body => do
      let xs := body.getAppArgs
      if xs.size ≥ 2 then pure xs[xs.size - 2]!.getAppFn.constName? else pure none
    if let some l := l then
      unless labels.contains l do labels := labels.push l
  let mut out : Array Nat := #[]
  for l in labels do
    try
      if let some n ← addrNat (← mkAppM ``Asm.addr #[prog, base, mkConst l]) then
        out := out.push n
    catch _ => pure ()
  return out

/-- Types the control transfer at the head of a block goal. -/
def finishBlockCore (goal : MVarId) (instr : Instr) : TacticM Finish := do
  match instr with
  | .jmp (.rel _) =>
    let before ← saveState
    try
      let gs ← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.last (by ty_fetch) (HasType.jmp ?_))))
      let [acc] := gs | throwError "ty_block: unexpected goals at `jmp`"
      return .done (← proveAccepts acc)
    catch e =>
      -- A jump forward to a label with no context that accepts this one is
      -- typed by typing what is there, here and now. A jump back is a loop,
      -- and a loop's head must say what holds each time round.
      unless jumpsForward instr && (← isNoContext e) do throw e
      before.restore
      let [target] ← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.jump (by ty_fetch) ?_))) | throwError "ty_block: unexpected goals at `jmp`"
      let [target'] ← runOn target (do evalTactic (← `(tactic| ty_normalize)))
        | throwError "unexpected goals"
      return .forks [target'] []
  | .syscall =>
    -- `write` and `read` are typed as steps; what reaches here is `exit`, or
    -- a call the type system has no rule for.
    let ctx := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs[5]!
    let sysArg := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs[2]!
    -- Where the program is being shown to end only with a status that is
    -- as wanted, the status must be exactly known here and be so. That it
    -- is, is left as a goal where it does not follow by computing.
    let exitOnly (rule : Name) : TacticM (List MVarId) := do
      let gs ← try
          runOn goal (do evalTactic (← `(tactic|
            refine BlockOk.last (by ty_fetch)
              (HasType.syscallExit ($(mkIdent rule) rfl rfl ?status)))))
        catch _ =>
          let actual ← goal.withContext do
            ppTy (← whnf (← mkAppM ``CtxOf.regs #[ctx, mkConst ``Reg.rdi]))
          throwError "`syscall`: what the program ends with is being shown, so the status in \
            `rdi` must be exactly known here, but its type is `{actual}`"
      let mut left : List MVarId := []
      for g in gs do
        if ← g.isAssigned then continue
        left := left ++ (← try
            runOn g (do evalTactic (← `(tactic|
              first | (dsimp only; decide) | decide | rfl | (dsimp only; ty_arith) | ty_arith)))
          catch _ => pure [g])
      return left
    match ← syscallNumber ctx with
    | some 60 =>
      if sysArg.isAppOf ``Syscall.exitsOnly then return .done (← exitOnly ``linux_exit_only)
      if sysArg.isAppOf ``Syscall.writesOnly && sysArg.getAppArgs[0]!.isAppOf ``Syscall.exitsOnly then
        return .done (← exitOnly ``linux_exit_only_writes)
      if sysArg.isAppOf ``Syscall.writesOnly then
        let gs ← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last (by ty_fetch) (HasType.syscallExit (linux_exit_writes rfl)))))
        return .done gs
      let gs ← try
          runOn goal (do evalTactic (← `(tactic|
            refine BlockOk.last (by ty_fetch) (HasType.syscallExit (linux_exit rfl)))))
        catch _ => throwError "`syscall`: the operating system here is not the Linux model"
      return .done gs
    | some 231 =>
      if sysArg.isAppOf ``Syscall.exitsOnly then
        return .done (← exitOnly ``linux_exit_group_only)
      if sysArg.isAppOf ``Syscall.writesOnly && sysArg.getAppArgs[0]!.isAppOf ``Syscall.exitsOnly then
        return .done (← exitOnly ``linux_exit_group_only_writes)
      if sysArg.isAppOf ``Syscall.writesOnly then
        let gs ← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last (by ty_fetch) (HasType.syscallExit (linux_exit_group_writes rfl)))))
        return .done gs
      let gs ← try
          runOn goal (do evalTactic (← `(tactic|
            refine BlockOk.last (by ty_fetch) (HasType.syscallExit (linux_exit_group rfl)))))
        catch _ => throwError "`syscall`: the operating system here is not the Linux model"
      return .done gs
    | some 9 =>
      -- Unless it is said what the new memory is to hold, the program owns
      -- it as plain bytes: the block goes on twice, for the error and for
      -- the address.
      let before ← saveState
      try
        setGoals [goal]
        Tactic.withoutRecover do evalTactic (← `(tactic| ty_mmap_own as $(mkIdent `p)))
        return .forks (← getGoals) []
      catch _ =>
        before.restore
        return .needsHelp m!"`syscall`: an `mmap` needs the layout of the new block; use \
          `ty_mmap <shape>` or `ty_mmap_kind <kind>`"
    | some 11 =>
      -- giving back a block the context owns
      setGoals [goal]
      evalTactic (← `(tactic| ty_munmap))
      return .forks (← getGoals) []
    | some nr =>
      throwError "`syscall`: call number {nr} has no rule. The calls that can be typed are \
        {typedCalls}"
    | none =>
      let actual ← goal.withContext do
        ppTy (← reduce (← mkAppM ``CtxOf.regs #[ctx, mkConst ``Reg.rax]))
      throwError "`syscall`: the call number in `rax` must be exactly known, but its type is \
        `{actual}`"
  | .ret =>
    let gs ← try
        runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last (by ty_fetch)
            (FnSig.ret_of (sig := ?_) (saved := ?_) ?caller ?regs ?sp rfl rfl ?own ?above))))
      catch _ =>
        let family ← goal.withContext do
          try
            let t := (← instantiateMVars (← goal.getType)).consumeMData
            let stack ← whnf (← mkAppM ``CtxOf.stack #[t.appArg!])
            if stack.isAppOfArity ``List.cons 3 then
              pure ((← instantiateMVars stack.appFn!.appArg!).find?
                (·.isConstOf ``Ty.codeAll)).isSome
            else pure false
          catch _ => pure false
        if family then
          throwError "`ret`: the return address here is ready for a family of contexts, one \
            for each value the function may hand back; say which the function returns into \
            with `ty_return_as`"
        throwError "`ret` needs a return address on top of the stack, but the context does \
          not have one there. Control would go to whatever number is there: a \
          general-protection fault where the processor has no such address, a page fault \
          where there is no code"
    let mut left := []
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``FnSig.CallerOk then
        try
          discard <| runOn g (do evalTactic (← `(tactic| first
            | assumption
            | exact FnSigEx.CallerOk.each (by assumption) _)))
        catch _ =>
          -- with pieces of the stack detached, the stack is not the one the caller expects
          let detached ← goal.withContext do
            try
              let t := (← instantiateMVars (← goal.getType)).consumeMData
              let above ← normAbove (← mkAppM ``CtxOf.above #[t.appArg!])
              pure !(above.isAppOfArity ``CtxOf.above 2 || above.isProj)
            catch _ => pure false
          if detached then
            throwError "`ret`: pieces of the stack are still detached; a function must attach \
              them again (`ty_stack_attach`) and leave the stack as it found it"
          throwError "`ret` needs the caller's requirement (`sig.CallerOk …`) among the hypotheses"
      else if t.isAppOf ``Sub then
        left := left ++ (← runOn g (do evalTactic (← `(tactic| ty_sub))))
      else if (← g.getTag).eraseMacroScopes == `above then
        try
          discard <| deep <| runOn g (do evalTactic (← `(tactic| first
            | rfl
            | exact (FnSigEx.CallerOk.detached (by assumption) _).symm
            | omega
            | (dsimp only; omega)
            | (simp only [← FnSigEx.CallerOk.detached (by assumption)]; omega))))
        catch _ =>
          throwError "`ret`: a piece detached from the stack has not been attached again; a \
            function must leave the stack as it found it"
      else if t.isAppOf ``Eq then
        try
          discard <| deep <| runOn g (do evalTactic (← `(tactic| first
            | rfl
            | exact FnSig.CallerOk.owned_back (by assumption) rfl
            | exact FnSigEx.CallerOk.owned_back (by assumption) _ rfl)))
        catch _ =>
          throwError "`ret`: the blocks owned here are not the ones the function gives back, \
            followed by the caller's own; a function must hand back what its signature says \
            and dispose of anything else it took"
      else if ← isProp t then
        left := left ++ (← runOn g (do evalTactic (← `(tactic| sub_regs))))
    return .done left
  | .jcc _ _ =>
    -- First try to end the block here, where the next instruction is at a
    -- label with a context of its own: elsewhere that cannot succeed, and
    -- trying costs as much as the branch itself.
    let before ← saveState
    let atLabel ← (do
      let ty := (← instantiateMVars (← goal.getType)).consumeMData
      unless ty.isAppOfArity ``BlockOk 6 do return true
      let some n ← addrNat ty.getAppArgs[4]! | return true
      let some m ← instrsOf ty.getAppArgs[1]! | return true
      let some (_, len) := m[n]? | return true
      let labels ← declaredLabels ty.getAppArgs[0]!
      if labels.isEmpty then return true
      return labels.contains (n + len.toNat) : TacticM Bool) <|> pure true
    try
      unless atLabel do throwError "not at a label"
      let gs ← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.last (by ty_fetch) (HasType.jcc ?dec ?taken ?fall))))
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
    let gs ← runOn goal (do evalTactic (← `(tactic| refine BlockOk.branch (by ty_fetch) ?dec ?taken ?rest)))
    let dec ← goalNamed gs `dec
    let taken ← goalNamed gs `taken
    let rest ← goalNamed gs `rest
    try
      discard <| runOn dec decideCond
    catch _ =>
      throwError "`{instr.toAsm}`: the flags known here do not decide the condition. The \
        processor leaves some flags undefined after some instructions, and which way this goes \
        would then not be determined"
    let [takenAcc] ← runOn taken introBranch | throwError "unexpected goals"
    -- A side that the exactly known flags rule out needs nothing more.
    let beforeTaken ← saveState
    let leftTaken? ← try
        pure (some (← if ← closeIfImpossible takenAcc then pure [] else proveAccepts takenAcc))
      catch e =>
        unless jumpsForward instr && (← isNoContext e) do throw e
        beforeTaken.restore
        pure none
    if let some leftTaken := leftTaken? then
      let [rest'] ← runOn rest introBranch | throwError "unexpected goals"
      if ← closeIfImpossible rest' then return .done leftTaken
      let [rest''] ← runOn rest' (do evalTactic (← `(tactic| ty_normalize)))
        | throwError "unexpected goals"
      return .continues rest'' leftTaken
    -- The target has no context that accepts this one: type it in place.
    before.restore
    let gs ← runOn goal (do evalTactic (← `(tactic|
      refine BlockOk.branchIn (by ty_fetch) ?dec ?taken ?rest)))
    let dec ← goalNamed gs `dec
    let taken ← goalNamed gs `taken
    let rest ← goalNamed gs `rest
    discard <| runOn dec decideCond
    let mut blocks : List MVarId := []
    -- the side that carries on first: it is the one `ty_branch` leaves as the goal
    for side in [rest, taken] do
      let [side'] ← runOn side introBranch | throwError "unexpected goals"
      unless ← closeIfImpossible side' do
        let [side''] ← runOn side' (do evalTactic (← `(tactic| ty_normalize)))
          | throwError "unexpected goals"
        blocks := blocks ++ [side'']
    return .forks blocks []
  | .jmp (.ind _) =>
    let before ← saveState
    -- a tail call through a function pointer, on behalf of this function's caller
    let tail? ← try
        let gs ← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last (by ty_fetch) (HasType.jmpFn (sig := ?_) (saved := ?_) (ret := ?_)
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
      refine BlockOk.last (by ty_fetch) (HasType.jmpInd (Δ := ?_) ?code ?sub))))
    let code ← goalNamed gs `code
    let sub ← goalNamed gs `sub
    try
      discard <| runOn code (do evalTactic (← `(tactic| ty_operand)))
    catch _ =>
      throwError "`{instr.toAsm}`: the operand does not hold a pointer to code here. Control \
        would go to whatever number it holds: a general-protection fault where the processor \
        has no such address, a page fault where there is no code. A register holding the \
        exact address of a label becomes a pointer to code with `ty_fn_ptr` (a function) or \
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
      (refine BlockOk.last (by ty_fetch) (HasType.unreachable ?_)
       intro _ _ _ _ _ $hstate:ident
       first | exact ($hstate).flags | skip))))
    return .done gs
  | .call _ =>
    return .needsHelp m!"`{instr.toAsm}`: a call needs the callee's signature; use `ty_call <signature>`"
  | _ =>
    return .needsHelp m!"`{instr.toAsm}` is not handled by `ty_block`"

/-- Ends a block, adding to a rejection where the registers and flags it
speaks of got what they have, and carrying that record on to wherever the
block goes on from here. -/
def finishBlock (goal : MVarId) (instr : Instr) (why? : Option MessageData := none) :
    TacticM Finish := do
  let before ← try trailKey goal catch _ => pure none
  let r ← try
      -- where the checker's walk looked for this ending and found why it is
      -- refused, that is the reason given
      if let some msg := why? then throwError msg
      trace[TypedAsm.fast] "block ending the long way: {instr.toAsm}"
      finishBlockCore goal instr
    catch e =>
      match before with
      | some (key, _, _) =>
        let note ← trailNote key (← e.toMessageData.toString)
        if note == "" then throw e else throwError "{e.toMessageData}{note}"
      | none => throw e
  if let some (key, _, _) := before then
    let t := (← trailRef.get)[key]?.getD {}
    let gs := match r with
      | .continues rest _ => [rest]
      | .forks blocks _ => blocks
      | _ => []
    for g in gs do
      try
        if let some (key', _, _) ← trailKey g then trailRef.modify (·.insert key' t)
      catch _ => pure ()
  return r

/-- Where the instruction after the one here is at a label with a context
of its own, the block is ended with this instruction and handed over to
that label, if some context declared there accepts the one reached and asks
nothing more. Otherwise nothing is done, and the block goes on through the
label as it would have. -/
def tryInto (labels : Array Nat) : TacticM Bool := do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``BlockOk 6 do return false
  if labels.isEmpty then return false
  let some n ← addrNat ty.getAppArgs[4]! | return false
  let some m ← instrsOf ty.getAppArgs[1]! | return false
  let some (i, len) := m[n]? | return false
  if i.endsBlock then return false
  unless labels.contains (n + len.toNat) do return false
  let others := (← getGoals).drop 1
  -- first within a walk: the checker steps the instruction and compares the
  -- context it leaves with one chosen among the label's
  let atStart ← saveState
  let viaWalk ← (do
    try
      setGoals [goal]
      evalTactic (← `(tactic| ty_normalize))
      let goal' ← getMainGoal
      let ty' := (← instantiateMVars (← goal'.getType)).consumeMData
      intoOnly.set true
      runStops.set (some labels)
      labelsKnown.set (← declaresByLabel ty'.getAppArgs[0]!)
      match ← fastStep goal' ty' false with
      | some [] => pure true
      | some _ => trace[TypedAsm.fast] "into: the walk left goals"; pure false
      | none => trace[TypedAsm.fast] "into: the walk declined"; pure false
    catch e => trace[TypedAsm.fast] "into: {e.toMessageData}"; pure false
    finally
      intoOnly.set false
      runStops.set none)
  if viaWalk then
    setGoals others
    return true
  atStart.restore
  refusal.set none
  let saved ← saveState
  try
    let gs ← runOn goal (do evalTactic (← `(tactic|
      refine BlockOk.last (by ty_fetch) (HasType.straight (Γ' := ?_) ?st ?acc))))
    let st ← goalNamed gs `st
    let acc ← goalNamed gs `acc
    unless (← runOn st (do evalTactic (← `(tactic| ty_straight)))).isEmpty do
      throwError "left over"
    unless (← proveAccepts acc).isEmpty do throwError "left over"
    trace[TypedAsm.fast] "run into a label the long way: {i.toAsm}"
    setGoals others
    return true
  catch _ =>
    saved.restore
    return false

/-- The signature of the function an operand points to, where the operand's
type says it is a pointer to a function. -/
def pointerSig (goal : MVarId) (rm : RM) : TacticM (Option Expr) := goal.withContext do
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``BlockOk 6 do return none
  let args := ty.getAppArgs
  let τ0 ← match rm with
    | .reg r => instantiateMVars (← whnfR (← mkAppM ``CtxOf.regs #[args[5]!, toExpr r]))
    | .mem _ =>
      let a := args[4]!
      unless isAddrLit a do return none
      let some n := a.appArg!.nat? | return none
      let some m ← instrsOf args[1]! | return none
      let some (_, len) := m[n]? | return none
      let next := toExpr (BitVec.ofNat 64 (n + len.toNat))
      let τ ← mkFreshExprMVar (mkConst ``Ty)
      let g ← mkFreshExprSyntheticOpaqueMVar
        (mkAppN (mkConst ``Holds) #[args[3]!, next, args[5]!, toExpr rm, τ])
      let saved ← saveState
      let ok ← try
          pure (← runOn g.mvarId! (do evalTactic (← `(tactic| ty_operand)))).isEmpty
        catch _ => pure false
      let τ ← instantiateMVars τ
      saved.restore
      unless ok do return none
      pure τ
  if τ0.isAppOfArity ``FnSig.ty 1 then return some τ0.appArg!
  let τ ← whnf τ0
  if τ.isAppOfArity ``FnSig.ty 1 then return some τ.appArg!
  if τ.isAppOfArity ``Ty.fn 6 then return some (mkAppN (mkConst ``FnSig.mk) τ.getAppArgs)
  return none

/-- What a block or a call left to be shown, tried as arithmetic: a
comparison, or two exactly known values that are to be the same; and then,
where the user has marked facts with `@[asm_fact]`, by those facts with what
is known there. Returns what is still left. -/
def closeArith (left : List MVarId) : TacticM (List MVarId) := do
  let facts ← hasUserFacts
  -- by the user's facts, where arithmetic did not settle it
  let byFacts (gs : List MVarId) : TacticM (List MVarId) := do
    unless facts do return gs
    let mut out : List MVarId := []
    for g in gs do
      let s ← saveState
      try
        let l ← runOn g (do evalTactic (← `(tactic| (simp [asm_fact, *]; done))))
        out := out ++ l
      catch _ =>
        s.restore
        out := out ++ [g]
    return out
  let mut kept : List MVarId := []
  for g in left do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    let after ← try
        if t.hasExprMVar then pure [g]
        else if t.isAppOfArity ``Sub 2 then
          -- not `Sub.of_eq (by …)`: a tactic block inside a term reports its
          -- own failure and gives the goal up, where this one is to fail
          let [eq] ← runOn g (do evalTactic (← `(tactic| refine Sub.of_eq ?_))) | pure [g]
          let s ← saveState
          try runOn eq (do evalTactic (← `(tactic| ty_arith)))
          catch e =>
            s.restore
            let l ← byFacts [eq]
            unless l.isEmpty do throw e
            pure []
        else if isComparison t && !t.hasExprMVar then
          let s ← saveState
          try runOn g (do evalTactic (← `(tactic| ty_arith)))
          catch e =>
            s.restore
            let l ← byFacts [g]
            unless l.isEmpty do throw e
            pure []
        else pure [g]
      catch _ => pure [g]
    kept := kept ++ after
  return kept

/-- A direct call to a function whose results depend on a value it chooses,
typed from the labels alone: the context declared at the function's label is
`sig.entry …` for a signature `sig` with nothing left open, and the label
after the call has one context for each value. Nothing is done unless both
are so and the call then types. -/
def autoCallEx (goal : MVarId) : TacticM (Option (List MVarId)) := goal.withContext do
  let before ← saveState
  try
    let ty := (← instantiateMVars (← goal.getType)).consumeMData
    unless ty.isAppOfArity ``BlockOk 6 do return none
    let Φ := ty.getAppArgs[0]!
    let some n ← addrNat ty.getAppArgs[4]! | return none
    let some m ← instrsOf ty.getAppArgs[1]! | return none
    let some (.call (.rel d), len) := m[n]? | return none
    let t := (BitVec.ofNat 64 n + len + d.signExtend 64).toNat
    let next := n + len.toNat
    let some (_, _, T, labels) ← labelInfo Φ | return none
    let some (_, lFn) := labels.find? (·.1 == t) | return none
    let some (_, lRet) := labels.find? (·.1 == next) | return none
    let .const tn _ := T.getAppFn | return none
    let some (.inductInfo info) := (← getEnv).find? tn | return none
    let mut sig? : Option Expr := none
    let mut rets : Array Expr := #[]
    for k in info.ctors do
      let kTy ← inferType (mkConst k)
      let (s?, r?) ← forallTelescope kTy fun xs body => do
        let args := body.getAppArgs
        if args.size < 2 then return (none, none)
        let l := args[args.size - 2]!
        let ctx := args[args.size - 1]!
        if l.isConstOf lFn && ctx.isAppOf ``FnSigEx.entry && ctx.getAppNumArgs ≥ 7 then
          let sig := ctx.getAppArgs[ctx.getAppNumArgs - 7]!
          return (if sig.hasFVar then none else some sig, none)
        if l.isConstOf lRet && xs.size == 1 then
          unless ← isProp (← inferType xs[0]!) do
            return (none, some (← mkLambdaFVars xs ctx))
        return ((none : Option Expr), (none : Option Expr))
      if let some sg := s? then sig? := some sg
      if let some r := r? then rets := rets.push r
    let some sig := sig?
      | do trace[TypedAsm.fast] "a call: the function's label does not say a signature"; return none
    unless rets.size == 1 do
      trace[TypedAsm.fast] "a call: {rets.size} families of contexts at the return point"
      return none
    setGoals [goal]
    let s ← Term.exprToSyntax sig
    let r ← Term.exprToSyntax rets[0]!
    Tactic.withoutRecover do evalTactic (← `(tactic| ty_call_returning $s $r))
    return some (← getGoals)
  catch e =>
    trace[TypedAsm.fast] "a call to a function that chooses a value: {e.toMessageData}"
    before.restore
    return none

/-- Types a whole block of a labelled program: the straight-line
instructions, then the control transfer that ends it. Jump targets are found
by label. Conditional jumps in the middle of the block are followed.

Goals are left for whatever needs an argument: facts a target context
demands (with the branch condition available as `hcond`), and register types
that do not obviously match. The tactic stops at a `call`, which needs
`ty_call`. -/
elab "ty_block_core" : tactic => do
  let others := (← getGoals).drop 1
  let mut left : List MVarId := []
  -- the blocks still to be typed: this one, and those a jump typed in place
  -- leads to; and the ones the tactic could not carry further
  let mut work : List MVarId := [← getMainGoal]
  let mut stuck : List MVarId := []
  let mut labelsOf : Array (Expr × Array Nat) := #[]
  repeat
    let g :: more := work | break
    work := more
    setGoals [g]
    let mut endInstr? : Option Instr := none
    let mut endWhy : Option MessageData := none
    let mut entered := false
    enterOff.set false
    repeat
      -- A side of a conditional jump the walk left: what the flags say of the
      -- condition is brought in, and a side they rule out needs nothing more.
      let g₀ ← getMainGoal
      if (← instantiateMVars (← g₀.getType)).consumeMData.isForall then
        let behind := (← getGoals).drop 1
        let [g₁] ← runOn g₀ introBranch | throwError "unexpected goals"
        if ← closeIfImpossible g₁ then
          setGoals behind
          entered := true
          break
        let [g₂] ← runOn g₁ (do evalTactic (← `(tactic| ty_normalize)))
          | throwError "unexpected goals"
        setGoals (g₂ :: behind)
      -- where the next instruction is at a label with a context of its own
      -- that accepts the one reached, the block hands over to it
      let labels ← do
        let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
        if ty.isAppOfArity ``BlockOk 6 then
          let Φ := ty.getAppArgs[0]!
          match labelsOf.find? (·.1 == Φ) with
          | some (_, ls) => pure ls
          | none =>
            let ls ← declaredLabels Φ
            labelsOf := labelsOf.push (Φ, ls)
            pure ls
        else pure #[]
      if ← tryInto labels then entered := true; break
      runStops.set (some labels)
      labelsKnown.set (← do
        let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
        if ty.isAppOfArity ``BlockOk 6 then declaresByLabel ty.getAppArgs[0]! else pure false)
      let r ← try typeStep finally runStops.set none
      match r with
      | .stepped => continue
      | .done => entered := true; break
      | .endOfBlock instr why => endInstr? := some instr; endWhy := why; break
      | .notABlock => break
    if entered then
      -- a step that told two cases apart left the other case behind this one
      work := (← getGoals).take ((← getGoals).length - others.length) ++ work
      continue
    let some instr := endInstr? | stuck := stuck ++ (← getGoals); continue
    let goal ← getMainGoal
    -- a step that told two cases apart left the other case behind this one
    work := (← getGoals).drop 1 ++ work
    -- An ending the checker's walk did not type is not typed here: there is
    -- no other way. Where the walk found why it is refused, that is the
    -- error; otherwise the block is left where it stands, for what the
    -- author says next of it.
    match endWhy with
    | some _ => discard <| finishBlock goal instr endWhy
    | none =>
      trace[TypedAsm.fast] "an ending left to be said: {instr.toAsm}"
      stuck := stuck ++ [goal]
  setGoals (stuck ++ (← closeArith left) ++ others)


/-- Types a whole block, as `ty_block_core` does. Where that leaves
something, and the program declares kinds of block, the block is tried again
with an `mmap` in it making a new block of each kind in turn, in place of
memory for the program to own: which it is to be is found, not said. -/
elab "ty_block" : tactic => do
  let goal ← getMainGoal
  let before := (← getGoals).length
  let start ← saveState
  let attempt : TacticM (Option Exception) := do
    try
      evalTactic (← `(tactic| ty_block_core))
      pure none
    catch e => pure (some e)
  let first ← attempt
  if first.isNone && (← getGoals).length < before then return
  -- only at the outermost block, and only where there are kinds to try
  if (← mmapKindRef.get).isSome then
    if let some e := first then throw e
    return
  let kinds ← start.restore *> goal.withContext (do
    let ty := (← instantiateMVars (← goal.getType)).consumeMData
    if ty.isAppOfArity ``BlockOk 6 then declaredKinds ty.getAppArgs[3]! else pure #[])
  for k in kinds do
    start.restore
    mmapKindRef.set (some k)
    let r ← try attempt finally mmapKindRef.set none
    if r.isNone && (← getGoals).length < before then return
  -- as it was the first time
  start.restore
  if let some e ← attempt then throw e

/-- Types a conditional jump in the middle of a block. The side that jumps
is settled as `ty_block` would settle it; the side that carries on is left
as the goal, so that something can be said about it before going further. -/
elab "ty_branch" : tactic => do
  advance
  let others := (← getGoals).drop 1
  let saved ← saveState
  match ← typeStep with
  | .endOfBlock instr why =>
    let goal ← getMainGoal
    match ← finishBlock goal instr why with
    | .done l => setGoals (l ++ others)
    | .continues rest l => setGoals (rest :: l ++ others)
    | .forks blocks l =>
      -- the side that carries on is the goal; what the jump leads to is
      -- typed in place, as `ty_block` types it
      let rest :: taken := blocks | setGoals (l ++ others)
      let mut left : List MVarId := []
      for g in taken do
        left := left ++ (← runOn g (do evalTactic (← `(tactic| ty_block))))
      setGoals (rest :: left ++ l ++ others)
    | .needsHelp m => throwError m
  | .stepped | .done =>
    saved.restore
    throwError "ty_branch: the instruction here does not transfer control; use `ty_step`"
  | .notABlock => throwError "ty_branch: the goal is not a block"

/-- Runs a tactic where it applies. It is tried here, and if it does not
apply, after each further instruction that types by itself, a conditional
jump included (its other side settled as `ty_block` would settle it), for as
far as that goes. If it never applies, its complaint here is the one given.
So what is said of a block is said without the steps up to it being counted. -/
def seeking (tac : TacticM Unit) : TacticM Unit := do
  let start ← saveState
  let attempt : TacticM (Option Exception) := do
    let s ← saveState
    try
      tac
      pure none
    catch e =>
      s.restore
      pure (some e)
  let some first ← attempt | return
  for _ in [0:64] do
    let s ← saveState
    let moved ← try
        match ← typeStep with
        | .stepped => pure true
        | .endOfBlock (.jcc _ _) _ =>
          evalTactic (← `(tactic| ty_branch))
          pure true
        | _ => pure false
      catch _ =>
        s.restore
        pure false
    unless moved do break
    if (← attempt).isNone then return
  start.restore
  throw first

/-- `ty_call sig` types a `call` that ends a block, to a function with
signature `sig`. The callee and the return point are found by label. Left as
goals: argument registers whose types do not obviously match what the
function expects, and register types after the return that do not obviously
match the return point's context. -/
elab "ty_call " sig:term : tactic => do
  advance
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  -- Find the instruction, to tell a direct call from an indirect one.
  let parts ← try
      runOn goal (do evalTactic (← `(tactic| refine BlockOk.last (by ty_fetch) ?typed)))
    catch _ => throwError "ty_call: the goal is not a block with an instruction at its address"
  let typed ← goalNamed parts `typed
  let typedTy ← instantiateMVars (← typed.getType)
  let instr? ← knownInstr typedTy.getAppArgs[6]!
  let ctx := typedTy.getAppArgs[5]!
  let noRoom (instr : Instr) : TacticM MessageData := do
    let room ← typed.withContext do ppClean (← reduce (← mkAppM ``CtxOf.room #[ctx]))
    return m!"`{instr.toAsm}`: there is no room on the stack for the return address: the \
      context has room for {room}. Below the stack the program was given there may be no \
      memory, which is a page fault, or other data, which would be overwritten"
  -- A call through an operand holding a function pointer is typed like a
  -- direct call to that function.
  let viaPointer? ← match instr? with
    | some (.call (.ind _)) =>
      let before ← saveState
      try
        let gs ← runOn typed (do evalTactic (← `(tactic|
          refine HasType.callFn (sig := $sig) (ret := ?_) ?callee rfl ?retpoint ?args ?sp ?back
            ?need ?gives ?own)))
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
              ?callee rfl ?retpoint ?args ?sp ?stack ?own ?above)))
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
      try
        discard <| runOn (← goalNamed gs `own) (do evalTactic (← `(tactic| rfl)))
      catch _ =>
        throwError "ty_call: the blocks owned here are not the ones owned at the return point"
      try
        discard <| runOn (← goalNamed gs `above) (do evalTactic (← `(tactic| first | rfl | omega | (dsimp only; omega))))
      catch _ =>
        throwError "ty_call: what is detached from the stack here is not what is detached at \
          the return point"
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
            ?need ?gives ?own)))
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
        t.isAppOf ``Sub || t.isAppOf ``Eq then continue
    left := left ++ (← proveAtLabel g (pure []))
  -- What the argument registers hold is compared with what the function
  -- expects before anything else: where the signature was left to be found,
  -- and is one of a family, this is what says which.
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isForall && !t.isAppOf ``FnSig.At then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| sub_regs))))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``CtxSub then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| ctx_sub))))
    else if t.isAppOf ``Eq then
      try
        discard <| deep <| runOn g (do evalTactic (← `(tactic| rfl)))
      catch _ =>
        throwError "ty_call: the blocks owned do not match. Those owned here must be the \
          ones the function takes, in its order, then any others; and the return point must \
          own the ones the function gives, then those others"
    else if t.isForall then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| sub_regs))))
    else if t.isAppOf ``Sub then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| ty_sub))))
    else if t.isAppOf ``LE.le && t.hasExprMVar then
      -- which signature it is has not been settled: the room it needs is
      -- left to be compared once it has
      left := left ++ [g]
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
  setGoals ((← closeArith left) ++ others)

macro_rules
  | `(tactic| ty_call_auto) => `(tactic| ty_call ?_)
  | `(tactic| ty_call_with $s) => `(tactic| ty_call $s)

/-- `ty_call sig returning ret` types a `call` that ends a block, direct or
through a pointer, to
a function whose signature `sig : FnSigEx` has results that depend on a
value the function chooses as it returns: typically the address of a block
it made. `ret` gives the context at the instruction after the call for each
such value, and the label there must allow all of them. -/
elab "ty_call " sig:term " returning " ret:term : tactic => do
  advance
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  -- directly, or through an operand that holds a pointer to the function
  let (gs, direct) ← try
      pure (← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.last (by ty_fetch)
          (FnSigEx.call_ok (sig := $sig) (ret := $ret) (frame := ?_) ?callee rfl ?retpoint ?args
            ?sp ?back ?need ?own ?gives ?frame)))), true)
    catch _ =>
      try
        pure (← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last (by ty_fetch)
            (HasType.callFnAll (sig := $sig) (ret := $ret) (frame := ?_) ?callee rfl ?retpoint
              ?args ?sp ?back ?need ?gives ?frame ?own)))), false)
      catch _ =>
        throwError "ty_call: the instruction here must be a call, with room on the stack for \
          the return address"
  let mut left : List MVarId := []
  if direct then
    let [entry] ← runOn (← goalNamed gs `callee) (do evalTactic (← `(tactic| intro _ _ _ _ _ _ hK)))
      | throwError "ty_call: unexpected goals"
    left := left ++ (← proveAtLabel entry (pure []))
  else
    try
      discard <| runOn (← goalNamed gs `callee) (do evalTactic (← `(tactic| ty_operand)))
    catch _ =>
      throwError "ty_call: the operand does not hold a pointer to a function with this \
        signature. A register holding the exact address of a function becomes a pointer to \
        it with `ty_fn_ptr`"
  let [back] ← runOn (← goalNamed gs `retpoint) (do evalTactic (← `(tactic| intro x)))
    | throwError "ty_call: unexpected goals"
  left := left ++ (← proveAtLabel back (pure []))
  left := left ++ (← runOn (← goalNamed gs `args) (do evalTactic (← `(tactic| sub_regs))))
  left := left ++ (← runOn (← goalNamed gs `sp) (do evalTactic (← `(tactic| ty_sub))))
  try
    discard <| deep <| runOn (← goalNamed gs `own) (do evalTactic (← `(tactic| rfl)))
    discard <| deep <| runOn (← goalNamed gs `gives) (do evalTactic (← `(tactic| (intro x; rfl))))
    discard <| deep <| runOn (← goalNamed gs `frame) (do evalTactic (← `(tactic| (intro x; rfl))))
  catch _ =>
    throwError "ty_call: the blocks owned do not match. Those owned here must be the ones \
      the function takes, in its order, then any others; and whatever value the function \
      chooses, the return point must own the ones the function gives, then those others"
  left := left ++ (← runOn (← goalNamed gs `back) (do evalTactic (← `(tactic| (intro x; ctx_sub)))))
  left := left ++ (← runOn (← goalNamed gs `need) (do evalTactic (← `(tactic| first | decide | omega))))
  setGoals (left ++ others)

macro_rules
  | `(tactic| ty_call_returning $s $r) => `(tactic| ty_call $s returning $r)

/-- `ty_return_as x`: the function's return address is ready for a family of
contexts, and the function has decided it returns into the one for `x`. From
here on the return address is typed as code for that context alone, which is
what `ret` needs. -/
elab "ty_return_as " x:term : tactic => seeking do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  for i in [0:16] do
    let saved ← saveState
    try
      setGoals [goal]
      let iq := Syntax.mkNumLit (toString i)
      Tactic.withoutRecover do
        evalTactic (← `(tactic| refine BlockOk.chooseRet (i := $iq) $x rfl ?_))
      evalTactic (← `(tactic| ty_normalize))
      setGoals ((← getGoals) ++ others)
      return
    catch _ => saved.restore
  throwError "ty_return_as: there is no return address ready for a family of contexts on the \
    stack here"

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
      let parts ← runOn g (do evalTactic (← `(tactic| refine FnSig.CallerOk.mk ?gives ?ret ?room)))
      for p in parts do
        let after ← try
            runOn p (do evalTactic (← `(tactic| first | rfl | ctx_sub | decide | omega)))
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
  -- a signature of either kind: plain, or with results chosen at the return
  let (gs, chosen) ← try
      pure (← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.fnPtr (r := $r) (sig := $sig) ?ne rfl ?here ?rest))), false)
    catch _ =>
      try
        pure (← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.fnPtrAll (r := $r) (sig := $sig) ?ne rfl ?here ?rest))), true)
      catch _ =>
        throwError "ty_fn_ptr: the register does not hold an exactly known address here"
  discard <| runOn (← goalNamed gs `ne) (do evalTactic (← `(tactic| decide)))
  let [entry] ← runOn (← goalNamed gs `here) (do
      if chosen then evalTactic (← `(tactic| intro _ _ _ _ _ _ hK))
      else evalTactic (← `(tactic| intro _ _ _ _ hK)))
    | throwError "ty_fn_ptr: unexpected goals"
  let left ← try
      proveAtLabel entry (pure [])
    catch e =>
      throwError "ty_fn_ptr: the address is not that of a function with this signature\n\
        {e.toMessageData}"
  setGoals [← goalNamed gs `rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left ++ others)

elab_rules : tactic
  | `(tactic| ty_code_at) => do
    let goal ← getMainGoal
    let others := (← getGoals).drop 1
    let start ← saveState
    -- what a label demands of the context, shown where it is routine
    let settle (gs : List MVarId) : TacticM Unit := do
      for g in gs do
        if ← g.isAssigned then continue
        let t ← instantiateMVars (← g.getType)
        let left ← if t.isAppOf ``FnSig.CallerOk then (do
            let parts ← runOn g (do evalTactic (← `(tactic|
              first | assumption | refine FnSig.CallerOk.mk ?gives ?ret ?room)))
            let mut left : List MVarId := []
            for p in parts do
              left := left ++ (← runOn p (do evalTactic (← `(tactic|
                first | rfl | ctx_sub | decide | omega))))
            pure left)
          else runOn g (do evalTactic (← `(tactic| first | assumption | decide | omega)))
        unless left.isEmpty do throwError "left over"
    -- code wanting a context allowed at the address
    try
      let gs ← runOn goal (do evalTactic (← `(tactic| refine Or.inl ⟨_, rfl, ?here⟩)))
      settle (← proveAtLabel (← goalNamed gs `here) (pure []))
      setGoals others
      return
    catch _ => start.restore
    -- a function typed there
    try
      let gs ← runOn goal (do evalTactic (← `(tactic|
        refine Or.inr (Or.inl ⟨_, rfl, ?here⟩))))
      let [entry] ← runOn (← goalNamed gs `here) (do evalTactic (← `(tactic| intro _ _ _ _ hK)))
        | throwError "unexpected goals"
      settle (← proveAtLabel entry (pure []))
      setGoals others
      return
    catch _ => start.restore
    let gs ← runOn goal (do evalTactic (← `(tactic|
      refine Or.inr (Or.inr ⟨_, _, _, rfl, ?here⟩))))
    let [entry] ← runOn (← goalNamed gs `here) (do evalTactic (← `(tactic| intro _ _ _ _ _ _ hK)))
      | throwError "unexpected goals"
    settle (← proveAtLabel entry (pure []))
    setGoals others

macro_rules
  | `(tactic| ty_code_ptr_fwd $r to $Δ) => `(tactic| ty_code_ptr $r to $Δ)
  | `(tactic| ty_fn_ptr_fwd $r to $s) => `(tactic| ty_fn_ptr $r to $s)

/-- Types an `mmap` at the head of a block goal with the given lemma applied
to the layout asked for, and proves what it needs of the registers. -/
def typeMmap (rule : TSyntax `term) : TacticM Unit := do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  setGoals [goal]
  try
    evalTactic (← `(tactic| refine BlockOk.sys (by ty_fetch) $rule ?_))
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
          else if reg == "rdi" then
            throwError "`mmap` is typed only where the kernel chooses the place: `rdi` must \
              hold exactly 0, but its type is `{actual}`. Asked for an address, the kernel may \
              put the memory where it would not of its own accord, such as in the reach of \
              the stack"
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
            | (refine ShapeOf.fits_rep ?_ _; first | exact rfl | decide)
            | (simp only [ShapeOf.raw, ShapeOf.rep_size, List.length_cons, List.length_nil,
                List.length_replicate]; omega)
            | (simp; done)))
      catch _ =>
        if t.isAppOf ``LE.le then
          throwError "`mmap`: the block does not fit in the length in `rsi`"
        else if t.isAppOf ``LT.lt then
          throwError "`mmap`: a block needs at least one byte"
        else if t.isAppOf ``Eq && t.appFn!.appArg!.isAppOf ``ShapeOf.fits then
          throwError "`mmap`: a typed value of the new block does not lie inside it"
        else
          throwError "`mmap`: every typed value of the new block must admit zero, since \
            that is what fresh memory holds: a value that may be null"
  let some rest := rest? | throwError "ty_mmap: unexpected goals"
  setGoals [rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ others)

/-- `ty_mmap shape`: the `syscall` here is an `mmap` for fresh memory, to be
used as a block of this shape. Afterwards `rax` holds an error number or a
writable pointer to the new block; `ty_err` tells them apart. -/
elab_rules : tactic
  | `(tactic| ty_mmap $shape) => do
    advance
    typeMmap (← `(linux_mmap (S := $shape) (len := ?_) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_))

/-- `ty_mmap_kind tag`: as `ty_mmap`, for a block of the declared kind
`tag`. Afterwards `rax` holds an error number or a writable pointer to a
block of that kind. -/
elab_rules : tactic
  | `(tactic| ty_mmap_kind $tag) => do
    advance
    typeMmap (← `(linux_mmap_kind (tag := $tag) (S := ?_) (len := ?_) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_))

/-- `ty_byte as b`: the instruction here loads the byte of text a register
points at. Two goals follow: the rest of the block with the byte exactly
zero, then with the byte exactly some `b` that is not zero, where the
pointer is known not to be at the end of its text and may be stepped forward
with `add r, 1`. A test of the byte then decides in each which way it goes. -/
elab_rules : tactic
  | `(tactic| ty_byte as $b) => do
    let goal ← getMainGoal
    let others := (← getGoals).drop 1
    setGoals [goal]
    try
      evalTactic (← `(tactic| refine BlockOk.strByte (by ty_fetch) ?_ ?_ ?_ rfl ?_ ?_))
    catch _ =>
      throwError "ty_byte: the instruction here must be `movzx r, byte ptr [p]` with `p` a \
        pointer into text"
    let mut blocks : List MVarId := []
    for g in ← getGoals do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      setGoals [g]
      if t.isAppOf ``BlockOk then
        evalTactic (← `(tactic| ty_normalize))
        blocks := blocks ++ (← getGoals)
      else if t.isForall then
        evalTactic (← `(tactic| (intro $b:ident hbyte hsmall; ty_normalize)))
        blocks := blocks ++ (← getGoals)
      else
        try
          evalTactic (← `(tactic| decide))
        catch _ =>
          throwError "ty_byte: the byte must go into a register other than the pointer's, \
            and neither may be `rsp`"
    setGoals (blocks ++ others)

/-- `ty_mmap_own as p`: the `syscall` here is an `mmap` for fresh memory that
the program is to own. Two goals follow: the rest of the block with an error
number in `rax`, then with `rax` holding exactly an address `p` and the
context owning the pages at `p` as a block of integers. `hpage` says `p` is
the start of a page, and `hlow` that it is not an error number. -/
elab_rules : tactic
  | `(tactic| ty_mmap_own as $p) => seeking <| withTrail "ty_mmap_own" do
    advance
    let goal ← getMainGoal
    let others := (← getGoals).drop 1
    setGoals [goal]
    try
      evalTactic (← `(tactic|
        refine BlockOk.mmapOwn (len := ?_) (size := ?_) (by ty_fetch) rfl ?_ ?_ ?_ ?_ ?_ ?_
          ?_))
    catch _ =>
      throwError "`mmap` is system call 9 of the Linux model: `rax` must hold exactly 9"
    let gs ← getGoals
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if let some (_, lhs, _) := t.eq? then
        if lhs.isAppOf ``CtxOf.regs then
          setGoals [g]
          try
            Tactic.withoutRecover do evalTactic (← `(tactic| rfl))
          catch _ =>
            throwError "`mmap` needs an exactly known length in `rsi`, 3 in `rdx` (read and \
              write), 0x22 in `r10` (private memory, not a file) and 0 in `rdi` (the kernel \
              chooses the place)"
    -- how many fields the pages make, worked out as a number
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if let some (_, lhs, rhs) := t.eq? then
        if lhs.isMVar then
          let v ← g.withContext do reduce (← instantiateMVars rhs)
          lhs.mvarId!.assign v
          g.assign (← mkEqRefl v)
    let mut blocks : List MVarId := []
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isForall then
        setGoals [g]
        if t.bindingBody!.bindingDomain!.isAppOf ``SysErr then
          evalTactic (← `(tactic| (intro e herr; ty_normalize)))
        else
          evalTactic (← `(tactic| (intro $p:ident hpage hlow; ty_normalize)))
        blocks := blocks ++ (← getGoals)
    setGoals (blocks ++ others)

/-- Among the goals a rule about an owned block leaves, settles by
computation those that say what a register holds, then those that look the
block up. The order matters: the first fix the address the second look for. -/
def closeLookups (gs : List MVarId) : TacticM Unit := do
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        setGoals [g]
        Tactic.withoutRecover do evalTactic (← `(tactic| rfl))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``GetElem?.getElem? || lhs.isAppOf ``MemTy.kinds then
        setGoals [g]
        Tactic.withoutRecover do evalTactic (← `(tactic| rfl))

/-- How many blocks a list of owned blocks has, as far as it is written out. -/
def ownedCount (owned : Expr) : MetaM Nat := do
  let mut e ← whnf owned
  let mut n := 0
  while e.isAppOfArity ``List.cons 3 do
    n := n + 1
    e ← whnf e.appArg!
  return n

/-- How many blocks the context of the block goal owns. -/
def ownedCountHere : TacticM Nat := withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOfArity ``BlockOk 6 do return 0
  ownedCount (← mkAppM ``CtxOf.owned #[t.appArg!])

/-- Closes the goal with the tactic made for one of the places `0` to
`count - 1`, the first that works. -/
def tryPlaces (count : Nat) (mk : Nat → TacticM (TSyntax `tactic)) : TacticM Unit :=
  deep do
  let goal ← getMainGoal
  for k in [0:count] do
    let saved ← saveState
    try
      setGoals [goal]
      Tactic.withoutRecover do evalTactic (← mk k)
      if (← getGoals).isEmpty then return
      saved.restore
    catch _ => saved.restore
  throwError "no owned block fits"

/-- The list of owned blocks a goal about one of them is stated for: its
first explicit argument. -/
def ownedOfGoal : TacticM Expr := withMainContext do
  let t ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  let some owned := t.getAppArgs[0]? | throwError "not a goal about an owned block"
  return owned

elab_rules : tactic
  | `(tactic| ty_owned_at) => do
    tryPlaces (← ownedCount (← ownedOfGoal)) fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine' OwnedAt.of_inside (k := $kq) ?entry ?addr ?inside
          case entry => rfl
          case addr =>
            -- matched as written: comparing two addresses by working them out
            -- is slow, and settles nothing when one is not known
            with_reducible first
            | rfl
            | exact BitVec.add_assoc _ _ _
            | exact OwnedAt.addr_sub _ _ _
            | exact OwnedAt.addr_sub' _ _ _ _
          case inside => ty_inside))
  | `(tactic| ty_owned_byte) => do
    tryPlaces (← ownedCount (← ownedOfGoal)) fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine' OwnedByte.mk (k := $kq) ?entry ?addr ?fit
          case entry => rfl
          case addr =>
            first
            | exact owned_addrScaled _ _ _ _ (by decide)
            | exact owned_addr0 _
            | exact owned_addrOff _ _
          case fit => ty_inside))

/-- A list with its spine written out as far as it can be worked out. -/
partial def spineOf (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  if e'.isAppOfArity ``List.cons 3 then
    return mkApp3 e'.appFn!.appFn!.appFn! e'.appFn!.appFn!.appArg! e'.appFn!.appArg!
      (← spineOf e'.appArg!)
  if e'.isAppOfArity ``List.nil 1 then return e'
  return e

/-- How many pieces of a stack are written out. -/
def stackCount (σ : Expr) : MetaM Nat := do
  return (← consElems σ).1.size

elab_rules : tactic
  | `(tactic| ty_stack_at) => withMainContext do
    let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
    unless t.isAppOfArity ``StackAt 5 do throwError "not a goal about the stack"
    -- the stack written out piece by piece, where a definition stood in for it
    let σ ← spineOf t.getAppArgs[0]!
    replaceMainGoal [← (← getMainGoal).replaceTargetDefEq (mkAppN t.getAppFn (t.getAppArgs.set! 0 σ))]
    tryPlaces (← stackCount σ) fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine' StackAt.of_inside (k := $kq) ?entry ?off ?inside
          case entry => exact rfl
          case off =>
            first
            | (refine stackAt_idx8 ?_ ?_ <;> ty_stack_in)
            | (refine stackAt_bytes ?_; ty_stack_in)
            | (refine stackAt_lit ?_; ty_stack_in)
          case inside => ty_stack_in))

/-- `ty_name_slot d as v`: from here on, the eight bytes `d` bytes above the
stack pointer are typed as exactly the value they hold, which is called `v`. -/
elab_rules : tactic
  | `(tactic| ty_name_slot $d as $v) => withMainContext do
    let others := (← getGoals).drop 1
    setGoals [← getMainGoal]
    evalTactic (← `(tactic| ty_normalize))
    let goal ← getMainGoal
    let t := (← instantiateMVars (← goal.getType)).consumeMData
    unless t.isAppOfArity ``BlockOk 6 do throwError "ty_name_slot: the goal is not a block"
    let n ← stackCount (← mkAppM ``CtxOf.stack #[t.appArg!])
    for k in [0:n] do
      let saved ← saveState
      try
        setGoals [goal]
        let kq := Syntax.mkNumLit (toString k)
        Tactic.withoutRecover do
          evalTactic (← `(tactic| (
            refine BlockOk.nameSlotAt (k := $kq) (d := $d) rfl ?lo ?le ?rest
            case lo => ty_stack_in
            case le => ty_stack_in)))
        evalTactic (← `(tactic| (intro $v:ident; ty_normalize)))
        setGoals ((← getGoals) ++ others)
        return
      catch _ => saved.restore
    throwError "ty_name_slot: there are not eight bytes of one piece of the stack there"

/-- Applies to the block goal the first of the tactics made for the pieces
of its stack that works, leaving the rest of the block. -/
def atStackPiece (name : String) (mk : Nat → TacticM (TSyntax `tactic))
    (failure : MessageData) (past : Nat := 0) : TacticM Unit :=
    withTrail name <| withMainContext do
  let others := (← getGoals).drop 1
  setGoals [← getMainGoal]
  evalTactic (← `(tactic| ty_normalize))
  let goal ← getMainGoal
  let t := (← instantiateMVars (← goal.getType)).consumeMData
  unless t.isAppOfArity ``BlockOk 6 do throwError "{name}: the goal is not a block"
  let n ← stackCount (← mkAppM ``CtxOf.stack #[t.appArg!])
  for k in [0:n + past] do
    let saved ← saveState
    try
      setGoals [goal]
      Tactic.withoutRecover do evalTactic (← mk k)
      evalTactic (← `(tactic| ty_normalize))
      setGoals ((← getGoals) ++ others)
      return
    catch _ => saved.restore
  throwError failure

/-- `ty_stack_split at d`: the piece of the stack that the byte `d` bytes
above the stack pointer is in is from here on two pieces, meeting there. An
access has to keep to one piece, so this is how part of a frame is kept to
exactly the bytes meant for it. -/
elab_rules : tactic
  | `(tactic| ty_stack_split at $d) =>
    atStackPiece "ty_stack_split" (fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine BlockOk.splitStackAt (k := $kq) (d := $d) rfl ?lo ?le ?rest
          case lo => ty_stack_in
          case le => ty_stack_in)))
      m!"ty_stack_split: no piece of the stack has that byte inside it"

/-- `ty_stack_join at d`: the two pieces of the stack that meet `d` bytes
above the stack pointer are from here on one piece. -/
elab_rules : tactic
  | `(tactic| ty_stack_join at $d) =>
    atStackPiece "ty_stack_join" (fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine BlockOk.joinStackAt (k := $kq) (d := $d) rfl rfl ?meet ?rest
          case meet => ty_stack_in)))
      m!"ty_stack_join: no two pieces of the stack meet there"

/-- `ty_stack_detach at d`: the pieces of the stack from the one that begins
`d` bytes above the stack pointer up are from here on blocks the context
owns, first among those it owns, and the stack ends below them. A block can
be handed to a function, which is how a function is handed a local. The
stack pointer's value must be known: name it first with `ty_name .rsp as sp`. -/
elab_rules : tactic
  | `(tactic| ty_stack_detach at $d) =>
    atStackPiece "ty_stack_detach" (fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine BlockOk.detachStackAt (v := ?_) (k := $kq) (d := $d) ?sp ?len ?off ?rest
          case sp => rfl
          case len => first | decide | (simp only [List.length_cons, List.length_nil]; omega)
          case off => first | rfl | (simp [stackOff]; done))))
      m!"ty_stack_detach: the stack pointer's value must be known here (name it with \
        `ty_name .rsp as sp`), and a piece of the stack must begin at that byte"
      -- the pieces not written out may be detached by themselves
      (past := 1)

/-- Attaches to the stack the first block owned, or with `single` unset a
run of blocks standing for pieces not written out, and returns the rest of
the block. -/
def attachOnce (goal : MVarId) (single : Bool) : TacticM MVarId := do
  let tac ← if single then
      `(tactic| refine BlockOk.attachStack (v := ?_) (L := [?_]) (rest := ?_) ?_ ?_ ?_ ?_)
    else `(tactic| refine BlockOk.attachStack (v := ?_) (L := ?_) (rest := ?_) ?_ ?_ ?_ ?_)
  let gs ← runOn goal (do evalTactic tac)
  -- the equations first: they settle the stack pointer's value and what is attached
  for g in gs do
    if ← g.isAssigned then continue
    if (← instantiateMVars (← g.getType)).isAppOf ``Eq then
      discard <| runOn g (do evalTactic (← `(tactic| rfl)))
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if t.isAppOf ``LE.le then
      discard <| runOn g (do evalTactic (← `(tactic| first
        | decide
        | omega
        | (simp only [stackLen_cons, stackLen_nil, ShapeOf.slot_size, ShapeOf.raw_size]; omega))))
  let some rest := rest? | throwError "nothing is left of the block"
  return rest

/-- `ty_stack_attach`: the blocks the context owns that were detached from
the stack, and lie where the stack now ends, are from here on its topmost
pieces again, holding whatever they were left holding. They must come first
among the blocks owned, lowest first, as `ty_stack_detach` left them. -/
elab_rules : tactic
  | `(tactic| ty_stack_attach) => withTrail "ty_stack_attach" <| withMainContext do
    let others := (← getGoals).drop 1
    setGoals [← getMainGoal]
    evalTactic (← `(tactic| ty_normalize))
    let mut goal ← getMainGoal
    let mut any := false
    for _ in [0:64] do
      let saved ← saveState
      let next? ← try
          let g ← Tactic.withoutRecover (attachOnce goal true)
          setGoals [g]
          evalTactic (← `(tactic| ty_normalize))
          pure (some (← getMainGoal))
        catch _ =>
          saved.restore
          try
            let g ← Tactic.withoutRecover (attachOnce goal false)
            setGoals [g]
            evalTactic (← `(tactic| ty_normalize))
            pure (some (← getMainGoal))
          catch _ =>
            saved.restore
            pure none
      let some next := next? | break
      goal := next
      any := true
    unless any do
      throwError "ty_stack_attach: the first block the context owns is not one detached from \
        the stack that lies where the stack now ends; the stack pointer's value must be known \
        too"
    setGoals (goal :: others)

/-- Applies a rule about the owned block at one of the places in the
context's list, whichever fits, and returns the goals it leaves. -/
def withOwnedPlace (mk : Nat → TacticM (TSyntax `tactic)) (failure : MessageData)
    (places? : Option (List Nat) := none) : TacticM (List MVarId) := deep do
  let goal ← getMainGoal
  let places ← match places? with
    | some ps => pure ps
    | none => pure (List.range (← ownedCountHere))
  for k in places do
    let saved ← saveState
    try
      setGoals [goal]
      Tactic.withoutRecover do evalTactic (← mk k)
      let gs ← getGoals
      closeLookups gs
      return gs
    catch _ => saved.restore
  throwError failure

/-- `ty_munmap`: the `syscall` here is a `munmap` of a block the context
owns, whose address is in `rdi` and whose whole size is in `rsi`. Afterwards
the context no longer owns it. -/
elab_rules : tactic
  | `(tactic| ty_munmap) => withTrail "ty_munmap" do
    advance (some 11)
    let others := (← getGoals).drop 1
    let gs ← withOwnedPlace (fun k => do
        let kq := Syntax.mkNumLit (toString k)
        `(tactic| refine BlockOk.sys (by ty_fetch)
            (linux_munmap (k := $kq) (a := ?_) (len := ?_) (S := ?_) ?_ ?_ ?_ ?_ ?_) ?_))
      m!"`munmap` is typed for a block the context owns: `rax` must hold exactly 11, `rdi` \
        exactly the address of an owned block, and `rsi` an exactly known length"
    let mut rest? : Option MVarId := none
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``BlockOk then rest? := some g
      else
        setGoals [g]
        try
          deep <| Tactic.withoutRecover do
            evalTactic (← `(tactic| first
              | (simp only [List.length_replicate, List.length_set, List.length_cons,
                  List.length_nil]; decide)
              | decide
              | (simp; done)))
        catch _ =>
          throwError "`munmap`: the length in `rsi` must cover exactly the owned block; a \
            block that was split must be joined again first, or its parts given back one by one"
    let some rest := rest? | throwError "ty_munmap: unexpected goals"
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    setGoals ((← getGoals) ++ others)

/-- Freezes the owned block whose address is in a register, with the rule given. -/
def freezeWith (mk : Nat → TacticM (TSyntax `tactic)) (name : String := "ty_freeze")
    (after : TacticM Unit := pure ()) (places : Option (List Nat) := none)
    (failure : MessageData :=
      m!"{name}: the register must hold exactly the address of a block the context owns") :
    TacticM Unit := withTrail name do
  let others := (← getGoals).drop 1
  let gs ← withOwnedPlace mk failure places
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else
      setGoals [g]
      try
        deep <| Tactic.withoutRecover do
          evalTactic (← `(tactic| first
            | decide
            | exact List.cons_ne_nil _ _
            | exact rfl
            | (simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
                ShapeOf.append, List.length_replicate, List.length_set, List.length_cons,
                List.length_nil, List.length_take, List.length_drop, List.length_append]
               first | decide | omega)
            | (simp; done)))
      catch _ =>
        -- a bound against a block's size is shown with the size worked out
        let t ← if t.isAppOfArity ``LE.le 4 then
            pure (mkApp (mkApp t.appFn!.appFn! (← reduce t.appFn!.appArg!)) (← reduce t.appArg!))
          else pure t
        throwError "{name}: could not show{indentExpr t}"
  let some rest := rest? | throwError "{name}: unexpected goals"
  setGoals [rest]
  after
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ others)

/-- `ty_freeze r`: register `r` holds exactly the address of a block the
context owns. From here on the block is an ordinary one that anything may
point to, of the shape it has now, and `r` is a writable pointer to it. It
can no longer be given back, nor its typed values change type. -/
elab_rules : tactic
  | `(tactic| ty_freeze $r) => do
    freezeWith fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| refine BlockOk.freeze (r := $r) (k := $kq) (w := true) (base := ?_) (S := ?_)
          ?_ ?_ ?_ ?_ ?_)

/-- `ty_freeze_kind r as tag`: as `ty_freeze`, but the block joins the
declared kind `tag`, whose shape it must have, and `r` becomes a pointer to
a block of that kind. -/
elab_rules : tactic
  | `(tactic| ty_freeze_kind $r as $tag) => do
    freezeWith fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| refine BlockOk.freezeKind (r := $r) (k := $kq) (tag := $tag) (w := true)
          (base := ?_) (S := ?_) ?_ ?_ ?_ ?_ ?_ ?_)

/-- `ty_split r at m`: register `r` holds exactly the address of a block the
context owns, of at least `m` bytes. From here on the context owns two
blocks in its place: the first `m` bytes where the block was, and the rest
`m` bytes on. Each can be stored to, frozen or given back on its own. -/
elab_rules : tactic
  | `(tactic| ty_split $r at $m) => seeking do
    freezeWith (name := "ty_split") fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| refine BlockOk.splitOwned (r := $r) (k := $kq) (m := $m) (base := ?_) (S := ?_)
          ?_ ?_ ?_ ?_)

/-- `ty_join r`: register `r` holds exactly the address of a block the
context owns, and the context also owns the block that starts where that one
ends. From here on it owns one block in their place, with the bytes of the
first followed by those of the second. -/
elab_rules : tactic
  | `(tactic| ty_join $r) => withTrail "ty_join" do
    let n ← ownedCountHere
    freezeWith (name := "ty_join")
      (places := some ((List.range (n * n)).filter fun c => c / n ≠ c % n))
      (failure := m!"ty_join: the register must hold exactly the address of a block the \
        context owns, and the context must own the block that starts where that one ends")
      (fun c => do
        let k₁ := Syntax.mkNumLit (toString (c / n))
        let k₂ := Syntax.mkNumLit (toString (c % n))
        `(tactic| refine BlockOk.joinOwned (r := $r) (k₁ := $k₁) (k₂ := $k₂) (base := ?_)
            (S₁ := ?_) (S₂ := ?_) ?_ ?_ ?_ ?_ ?_ ?_))
      (do evalTactic (← `(tactic| try simp only [Nat.max_def, Nat.min_def, Nat.reduceLeDiff,
            ↓reduceIte])))

/-- `ty_loaded` proves that a starting state meets an entry contract, when
the state is one with the program loaded and `rip` set to the entry,
perhaps given a stack with arguments first: the form the simulator's
starting states have. What is left to show is settled by computing: that
each of the program's bytes is where it should be, and arithmetic about
where things are. -/
elab "ty_loaded" : tactic => withMainContext do
  let g ← getMainGoal
  let others := (← getGoals).drop 1
  let t ← whnfR (← instantiateMVars (← g.getType))
  let tac ←
    if t.isAppOf ``TypedAsm.Entry then
      `(tactic| refine Entry.ofLoad ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    else if t.isAppOf ``TypedAsm.EntryArgs then
      `(tactic| refine EntryArgs.ofLoad _ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    else if t.isAppOf ``TypedAsm.EntryTexts then
      `(tactic| refine EntryTexts.ofLoad _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    else throwError "ty_loaded: the goal is not an entry contract"
  let gs ← try runOn g (do evalTactic tac)
    catch _ =>
      throwError "ty_loaded: the state must be one with the program loaded and `rip` set to \
        its entry"
  -- that the program is in memory, to be used again for the blocks that say
  -- their bytes
  let mut holds? : Option MVarId := none
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    if (t.find? (·.isAppOfArity ``State.Holds 2)).isSome then holds? := some g
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    try
      -- That each block that says its bytes holds them: nothing to look at
      -- where none does; otherwise they are compared with the program's own
      -- bytes, which are in memory.
      if (t.find? (·.isConstOf ``saidCheck)).isSome then
        let quick ← (do
          let s ← saveState
          try
            discard <| runOn g (do evalTactic (← `(tactic| decide)))
            pure true
          catch _ => s.restore; pure false)
        unless quick do
          let some h := holds? | throwError "no proof that the program is in memory"
          let hq ← Term.exprToSyntax (mkMVar h)
          discard <| runOn g (do evalTactic (← `(tactic|
            exact saidCheck_of_parts $hq
              (by set_option maxRecDepth 100000 in decide +kernel))))
        continue
      -- that the program is in memory: each byte is looked at, by the
      -- kernel; anything else: by the kernel too. Stating the check for a
      -- long run of data takes more nesting than the default allows.
      -- Which it is is told from the goal. Trying the first on a goal of the
      -- other kind fails only after the two have been compared at length.
      if let some holds := t.find? (·.isAppOfArity ``State.Holds 2) then
        -- The state is looked at to see how it was made. One made by loading
        -- the program needs no byte looked at, of memory or of the program:
        -- that each line's bytes are in its segment is so for every program,
        -- and what is compared here is only where the lines and the segments
        -- are. Any other state has each byte looked at.
        let p := holds.appFn!.appArg!
        let p' ← (do
          match p.getAppFn.constName? with
          | some _ => pure ((← unfoldDefinition? p).getD p)
          | none => pure p)
        let viaLoad : Option (TSyntax `tactic) ←
          if p'.isAppOf ``State.setReg then
            pure (some (← `(tactic|
              exact Asm.prepared_holds _ _ _ _ _ _ _
                (by set_option maxRecDepth 100000 in decide +kernel)
                (by set_option maxRecDepth 100000 in decide +kernel)
                (by set_option maxRecDepth 100000 in decide +kernel))))
          else if p'.isAppOf ``Asm.load then
            pure (some (← `(tactic|
              exact Asm.load_holds _ _ _ _ (by set_option maxRecDepth 100000 in decide +kernel)
                (by set_option maxRecDepth 100000 in decide +kernel))))
          else pure none
        let done ← match viaLoad with
          | some tac =>
            let before ← saveState
            try
              discard <| runOn g (do evalTactic tac)
              pure true
            catch _ =>
              before.restore
              pure false
          | none => pure false
        unless done do
          discard <| runOn g (do evalTactic (← `(tactic|
            exact State.holds_of_check (by set_option maxRecDepth 100000 in decide +kernel))))
      else
        discard <| runOn g (do evalTactic (← `(tactic|
          (set_option maxRecDepth 100000 in decide +kernel))))
    catch _ =>
      throwError "ty_loaded: the starting state does not meet the entry contract; this does \
        not hold:{indentExpr t}"
  setGoals others

/-- `ty_own_first r`: register `r` holds exactly the address of a block the
context owns. From here on that block is listed first among the owned ones.
The order means nothing, but a call hands a function the blocks its
signature takes from the front of the list, in the signature's order.

`ty_own_first p`, with `p` an address, says the same of the block at `p`,
whatever the registers hold: it can be said anywhere the block is owned. -/
elab_rules : tactic
  | `(tactic| ty_own_first $r) => do
    -- told apart by what the term is: a register, or an address
    let isReg ← withMainContext do
      try
        discard <| Term.withoutErrToSorry <|
          Term.elabTermEnsuringType r (some (mkConst ``Reg))
        pure true
      catch _ => pure false
    if isReg then
      freezeWith (name := "ty_own_first") fun k => do
        let kq := Syntax.mkNumLit (toString k)
        `(tactic| refine BlockOk.frontOwned (r := $r) (k := $kq) (base := ?_) (S := ?_) ?_ ?_ ?_)
    else
      freezeWith (name := "ty_own_first")
        (failure := m!"ty_own_first: the context owns no block at that address") fun k => do
        let kq := Syntax.mkNumLit (toString k)
        `(tactic| refine BlockOk.frontOwnedAt (k := $kq) (base := $r) (S := ?_) ?_ ?_)

/-- `ty_into h` types the instruction here and ends the block with it. Use it
when the next instruction is at a label and the block should hand over to
that label's context instead of typing the label's code a second time; `h`
is the fact that the label allows some context, as for `ty_accept`. -/
macro_rules
  | `(tactic| ty_into $h) =>
    `(tactic| (refine BlockOk.last (by ty_fetch) (HasType.straight (Γ' := ?_) ?st ?acc)
               case' st => ty_straight
               case' acc => ty_accept $h))

open Lean Meta Elab Tactic in
/-- Makes the stack room a function was handed visible as what the function
needs and some more, for each fact in scope that a caller met a signature:
the room, till then a number nothing is known of, becomes `m + need`. -/
elab "ty_room" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.isAppOf ``FnSig.CallerOk || t.isAppOf ``FnSigEx.CallerOk do continue
    -- only where the room is still a bare variable
    let room := if t.isAppOf ``FnSig.CallerOk then t.getAppArgs[4]! else t.getAppArgs[6]!
    unless room.isFVar do continue
    let h := mkIdent d.userName
    let m := mkIdent `m
    let rfl' := mkIdent `rfl
    evalTactic (← `(tactic| obtain ⟨$m, $rfl'⟩ := ($h).room_split))
    return
  throwError "no fact here says a caller met a signature with room still unknown"

open Lean Meta Elab Tactic in
/-- `ty_program` proves a labelled program well typed block by block,
`BlocksOk Φ fetch sys Ψ`: for each context declared at a label, the block
from that label is typed with `ty_block`, a function's block with its stack
room made visible first (`ty_room`).

A label whose block needs something said is given a case after it,

```
ty_program
case next =>
  ty_into At.loop
```

named for the label's context and binding its arguments, as with `case`.
Such a label's block is typed only as its case says, and not tried first
without. A label with no case whose block does not type by itself is
reported, with what stood in the way. -/
syntax (name := tyProgram) "ty_program" (Lean.Parser.Tactic.case)* : tactic

open Lean Meta Elab Tactic in
@[tactic tyProgram] def evalTyProgram : Tactic := fun stx => do
  let arms := stx[1].getArgs
  evalTactic (← `(tactic| (refine BlocksOk.of_labels ?_; intro l Γ h; cases h)))
  let goals ← getGoals
  -- the label each case is for
  let named := arms.map fun arm => (arm[1].getSepArgs[0]![0][0].getId.eraseMacroScopes, arm)
  let mut used : Array Name := #[]
  let mut left : List MVarId := []
  for g in goals do
    let tag := (← g.getTag).eraseMacroScopes
    match named.find? (fun x => !x.1.isAnonymous && x.1.isSuffixOf tag) with
    | some (name, arm) =>
      used := used.push name
      setGoals [g]
      evalTactic arm
      left := left ++ (← getGoals)
    | none =>
      let start ← saveState
      let mut done := false
      let mut why : MessageData := m!""
      try
        setGoals [g]
        let before ← saveState
        try evalTactic (← `(tactic| ty_room)) catch _ => before.restore
        Tactic.withoutRecover do evalTactic (← `(tactic| ty_block))
        let rest ← getGoals
        if rest.isEmpty then done := true
        else
          -- what was left to be shown, before it is forgotten
          let mut shown : MessageData := m!""
          for r in rest.take 3 do
            let ty ← instantiateMVars (← r.getType)
            if ty.isAppOf ``BlockOk then
              shown := shown ++ m!"\n• the block is not typed to its end"
            else shown := shown ++ m!"\n• left to be shown: {← r.withContext (ppExpr ty)}"
          why := shown
          start.restore
      catch e =>
        why := m!"\n• {e.toMessageData}"
        start.restore
      unless done do
        -- Said here, with the reason, and the goal given up: otherwise all
        -- that would be said is that a goal was left.
        logError m!"the block at label `{tag.components.getLast!}` does not type by itself:{why}\n\
          What it needs is said in a block after `ty_program`, beginning \
          `case {tag.components.getLast!}`."
        admitGoal g
  for (name, arm) in named do
    unless used.contains name do
      throwErrorAt arm "no context is declared under the name `{name}`"
  setGoals left

end TypedAsm
