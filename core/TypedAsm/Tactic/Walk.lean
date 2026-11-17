import TypedAsm.Tactic.Basic
import TypedAsm.Tactic.Match

/-!
# The tactics: walk

The walk through a block: the checker driven from the tactics, what it refuses and why, and handing a block over at a label, a call or a return.
-/

namespace TypedAsm

open Lean Meta Elab Tactic

/-! ## What could go wrong

A rule is refused because the instruction could do something the machine
does not allow, or leave memory other than its type says. Each reason for a
refusal ends by saying which. -/

/-- A number that is not known to be an address, used as one. -/
def hazardAddress (onStack : Bool) : String :=
  if onStack then
    ". Used as an address through the stack, an arbitrary number is a stack fault where the \
      processor has no such address, and a page fault where there is no memory for it"
  else
    ". Used as an address, an arbitrary number is a general-protection fault where the \
      processor has no such address, and a page fault where there is no memory for it"

/-- An access that may fall outside what it is known to be inside. -/
def hazardBounds : String :=
  ". Where nothing is known to be, there may be no memory, which is a page fault, or other \
    data, which would be read or overwritten unnoticed"

/-- A store that would leave a block holding something other than its type says. -/
def hazardConfusion : String :=
  ". The memory would no longer hold what its type says, and a later use of the value there \
    could fault"

/-- Whether the instruction can send control somewhere other than the next
instruction, which is where a block ends. -/
def Instr.endsBlock : Instr → Bool
  | .jmp _ | .jcc _ _ | .call _ | .ret | .syscall | .ud2 => true
  | _ => false

unsafe def evalInstrUnsafe (e : Expr) : MetaM Instr :=
  evalExpr Instr (mkConst ``Instr) e

unsafe def evalAddrUnsafe (e : Expr) : MetaM Nat := do
  let v ← evalExpr (BitVec 64) (mkApp (mkConst ``BitVec) (mkNatLit 64)) e
  return v.toNat

unsafe def evalNatUnsafe (e : Expr) : MetaM Nat :=
  evalExpr Nat (mkConst ``Nat) e

/-- The number a closed term for a number denotes. -/
@[implemented_by evalNatUnsafe]
opaque evalNat (e : Expr) : MetaM Nat

/-- The number a closed address term denotes. -/
@[implemented_by evalAddrUnsafe]
opaque evalAddr (e : Expr) : MetaM Nat


unsafe def evalFetchUnsafe (e : Expr) : MetaM (Option (Instr × BitVec 64)) := do
  evalExpr (Option (Instr × BitVec 64)) (← inferType e) e

/-- What a closed lookup of an instruction comes to. -/
@[implemented_by evalFetchUnsafe]
opaque evalFetch (e : Expr) : MetaM (Option (Instr × BitVec 64))

unsafe def evalTableUnsafe (e : Expr) : MetaM (List (Nat × Instr × BitVec 64)) := do
  evalExpr (List (Nat × Instr × BitVec 64)) (← inferType e) e

/-- The instructions, each with its address, that a closed table comes to. -/
@[implemented_by evalTableUnsafe]
opaque evalTable (e : Expr) : MetaM (List (Nat × Instr × BitVec 64))

deriving instance ToExpr for Lookup

instance : Inhabited Lookup := ⟨.none⟩

/-- A balanced search tree over instructions listed with their addresses. -/
partial def lookupTree (xs : Array (Nat × Instr × BitVec 64)) (lo hi : Nat) : Lookup :=
  if hi ≤ lo then .none
  else if hi = lo + 1 then
    match xs[lo]? with
    | some (a, i, len) => .leaf a i len
    | none => .none
  else
    let m := (lo + hi) / 2
    .node (lookupTree xs lo m) ((xs[m]?.map (·.1)).getD 0) (lookupTree xs m hi)

/-- For each program's instruction table met so far: its instructions with
their addresses, as the program gives them, and its search tree written out. -/
initialize layoutCache : IO.Ref (Std.HashMap Expr (Expr × Expr)) ← IO.mkRef {}

/-- For each program met so far, the lemma that its instruction table is the
search of its tree. A lemma is used again only where it is in scope. -/
initialize lemmaCache : IO.Ref (Std.HashMap Expr (Expr × Name)) ← IO.mkRef {}

/-- For each program met so far, what is at each address. -/
initialize instrCache : IO.Ref (Std.HashMap Expr (Std.HashMap Nat (Instr × BitVec 64))) ←
  IO.mkRef {}

/-- What a program's instruction table is remembered under, and the table.
The key is the program's lines and load address themselves, not their
names: a name may come to stand for other lines while an editor is open. -/
def programKey (fetch : Expr) : MetaM (Option (Expr × Expr)) := do
  -- unfold to `Asm.fetch base prog`, a walk along `Asm.table base prog`
  let mut f := fetch
  for _ in [0:8] do
    if f.isAppOf ``Asm.fetch then break
    let some f' ← unfoldDefinition? f | return none
    f := f'.headBeta
  unless f.isAppOfArity ``Asm.fetch 4 do return none
  let value (e : Expr) : MetaM Expr := do
    let .const n _ := e | return e
    match (← getEnv).find? n with
    | some (.defnInfo d) => return d.value
    | _ => return e
  let table ← mkAppM ``Asm.table #[f.appFn!.appArg!, f.appArg!]
  return some (mkApp2 fetch (← value f.appFn!.appArg!) (← value f.appArg!), table)

/-- A program's instruction table as a function that searches a tree written
out in full, with a proof that the table is that function. The proof is
`Lookup.sound`, whose premises the kernel settles by computing once for the
program; it is kept as a lemma of its own, and every lookup afterwards is a
few comparisons of numbers. -/
def layoutOf (fetch : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (key, table) ← programKey fetch | return none
  if let some (found, name) := (← lemmaCache.get)[key]? then
    if (← getEnv).contains name then return some (found, mkConst name)
  let (table, tree) ← do
    if let some r := (← layoutCache.get)[key]? then pure r
    else
      let listed ← try pure (← evalTable table).toArray catch _ => return none
      let r := (table, toExpr (lookupTree listed 0 listed.size))
      layoutCache.modify (·.insert key r)
      pure r
  let a := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let found ← withLocalDeclD `a a fun x => do
    mkLambdaFVars #[x] (mkApp2 (mkConst ``Lookup.find) tree (← mkAppM ``BitVec.toNat #[x]))
  let type ← mkEq fetch found
  let rflTrue ← mkEqRefl (mkConst ``Bool.true)
  let value := mkAppN (mkConst ``Lookup.sound)
    #[table, tree, rflTrue, ← mkEqRefl (mkApp (mkConst ``Lookup.toList) tree)]
  let name ← mkAuxLemma [] type (← mkExpectedTypeHint value type)
  lemmaCache.modify (·.insert key (found, name))
  return some (found, mkConst name)

/-- What is at each address of a program, by its instruction table. -/
def instrsOf (fetch : Expr) : MetaM (Option (Std.HashMap Nat (Instr × BitVec 64))) := do
  let some (key, table) ← programKey fetch | return none
  if let some m := (← instrCache.get)[key]? then return some m
  let listed ← try evalTable table catch _ => return none
  let m : Std.HashMap Nat (Instr × BitVec 64) :=
    listed.foldl (fun m (a, i, len) => m.insertIfNew a (i, len)) {}
  instrCache.modify (·.insert key m)
  return some m

/-- A proof that the lookup `lhs` of an instruction comes to `found`, which
it must: the kernel checks it by `rfl`, on the program's search tree where
there is one. -/
def fetchProof (lhs found : Expr) : MetaM Expr := do
  let direct ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs found)
  if lhs.isApp then
    match ← layoutOf lhs.appFn! with
    | some (table, h) =>
      let walked := mkApp table lhs.appArg!
      mkEqTrans (← mkCongrFun h lhs.appArg!)
        (← mkExpectedTypeHint (← mkEqRefl walked) (← mkEq walked found))
    | none => pure direct
  else pure direct

/-- `ty_fetch` proves `fetch a = some (i, len)` for a known program and
address by running the lookup, and fills in whatever of `i` and `len` is
unknown with what it found, written out in full. The proof is by `rfl`, but
it is the kernel alone that checks it: found by unifying, the instruction
would be an unevaluated term that walks the whole program again each time it
is looked at. -/
elab "ty_fetch" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := t.consumeMData.eq? | throwError "ty_fetch: not an equation"
  if lhs.hasFVar || lhs.hasMVar then
    evalTactic (← `(tactic| rfl))
    return
  let v? ← try pure (some (← evalFetch lhs)) catch _ => pure none
  let some v := v? | do
    evalTactic (← `(tactic| rfl))
    return
  let some (i, len) := v | throwError "there is no instruction at this address"
  let found := toExpr (some (i, len))
  unless ← isDefEq rhs found do
    throwError "the instruction at this address is{indentExpr (toExpr i)}"
  g.assign (← fetchProof lhs found)
  replaceMainGoal []

/-- Whether a term is an address written as a number. -/
def isAddrLit (e : Expr) : Bool :=
  e.isAppOfArity ``BitVec.ofNat 2 && e.appArg!.nat?.isSome

/-- A list with its spine worked out: each tail brought to the form of an
element followed by a list, as far as that goes, and a number of elements
dropped from an unknown list written as a number. -/
partial def normList (e : Expr) : MetaM Expr := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    return mkApp3 e.appFn!.appFn!.appFn! e.appFn!.appFn!.appArg! e.appFn!.appArg!
      (← normList e.appArg!)
  if e.isAppOfArity ``List.drop 3 then
    let n := e.appFn!.appArg!
    if n.nat?.isNone then
      let n' ← whnf n
      if let some k := n'.nat? then
        return mkApp2 e.appFn!.appFn! (mkNatLit k) e.appArg!
  return e

/-- A number written out, if the term is one that can be worked out. -/
def natOf (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.nat? then return some n
  if e.hasMVar then return none
  let v ← whnf e
  match v with
  | .lit (.natVal n) => return some n
  | _ => return v.nat?

/-- The elements of a list term, as far as its spine is written out, and
whether that is all of it. -/
partial def consElems (e : Expr) : MetaM (Array Expr × Bool) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    let (rest, whole) ← consElems e.appArg!
    return (#[e.appFn!.appArg!] ++ rest, whole)
  return (#[], e.isAppOfArity ``List.nil 1)

/-- A block's shape with its size and its typed values worked out: the form
it is kept in after a split, a join or a store has been applied to it. -/
def normShape (S : Expr) : MetaM Expr := do
  let S' ← whnf S
  unless S'.isAppOfArity ``ShapeOf.mk 3 do return S
  let τ := S'.appFn!.appFn!.appArg!
  let size ← match ← natOf S'.appFn!.appArg! with
    | some n => pure (mkNatLit n)
    | none => pure S'.appFn!.appArg!
  let (elems, whole) ← consElems S'.appArg!
  unless whole do return mkApp3 (S'.getAppFn) τ size S'.appArg!
  let mut out : Array Expr := #[]
  for p in elems do
    let p' ← whnf p
    if p'.isAppOfArity ``Prod.mk 4 then
      let o ← match ← natOf p'.appFn!.appArg! with
        | some n => pure (mkNatLit n)
        | none => pure p'.appFn!.appArg!
      out := out.push (mkApp2 p'.appFn!.appFn! o p'.appArg!)
    else out := out.push p
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, τ]
  return mkApp3 (S'.getAppFn) τ size (← mkListLit pairTy out.toList)

/-- A list of owned blocks with its spine and each block's shape worked out. -/
partial def normOwned (e : Expr) : MetaM Expr := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    let hd := e.appFn!.appArg!
    let hd' ← whnf hd
    let hd'' ← if hd'.isAppOfArity ``Prod.mk 4 then
        pure (mkApp hd'.appFn! (← normShape hd'.appArg!))
      else pure hd
    return mkApp3 e.appFn!.appFn!.appFn! e.appFn!.appFn!.appArg! hd'' (← normOwned e.appArg!)
  normList e

/-- The stack with each piece that an instruction has just changed worked
out, as far as its spine is written out: eight bytes holding one typed value
are written as a slot, bytes holding none as plain bytes. -/
partial def normStack (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  unless e'.isAppOfArity ``List.cons 3 do return e
  let hd := e'.appFn!.appArg!
  let keep := hd.isAppOf ``ShapeOf.slot || hd.isAppOf ``ShapeOf.raw || hd.isAppOf ``ShapeOf.rep
    || hd.isFVar
  let hd' ← if keep then pure hd else do
    let S ← normShape hd
    if S.isAppOfArity ``ShapeOf.mk 3 then
      let τ := S.appFn!.appFn!.appArg!
      let size := S.appFn!.appArg!
      let (elems, whole) ← consElems S.appArg!
      if whole && elems.size == 0 then pure (mkApp2 (mkConst ``ShapeOf.raw) τ size)
      else if whole && elems.size == 1 then
        let p := elems[0]!
        if p.isAppOfArity ``Prod.mk 4 && size.nat? == some 8 && p.appFn!.appArg!.nat? == some 0
        then pure (mkApp2 (mkConst ``ShapeOf.slot) τ p.appArg!)
        else pure S
      else pure S
    else pure S
  return mkApp3 e'.appFn!.appFn!.appFn! e'.appFn!.appFn!.appArg! hd' (← normStack e'.appArg!)

/-- A count of bytes detached from the stack with as much of it added up as
is known: a field of a context given by a definition is looked up, and the
length of a stack written out piece by piece is the sizes of its pieces. -/
partial def normAbove (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``CtxOf.above 2 then
    let c ← whnf e.appArg!
    if c.isAppOfArity ``CtxOf.mk 7 then return ← normAbove c.getAppArgs[6]!
    return e
  if e.isAppOfArity ``stackLen 2 then
    let mut sizes : Array Nat := #[]
    let mut l ← whnf e.appArg!
    while l.isAppOfArity ``List.cons 3 do
      let some n ← natOf (← whnf (← mkAppM ``ShapeOf.size #[l.appFn!.appArg!])) | return e
      sizes := sizes.push n
      l ← whnf l.appArg!
    if sizes.isEmpty then return e
    let mut out ← if l.isAppOfArity ``List.nil 1 then pure (mkNatLit 0)
      else pure (mkApp e.appFn! l)
    if l.isAppOfArity ``List.nil 1 then
      return mkNatLit (sizes.foldl (· + ·) 0)
    for n in sizes.reverse do
      out ← mkAppM ``HAdd.hAdd #[mkNatLit n, out]
    return out
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 then
    let a ← normAbove e.appFn!.appArg!
    let b ← normAbove e.appArg!
    match a.nat?, b.nat? with
    | some x, some y =>
      return mkNatLit (if e.isAppOfArity ``HAdd.hAdd 6 then x + y else x - y)
    | _, _ => return mkApp2 e.appFn!.appFn! a b
  return e

/-- A context written as its six parts, with each register's type and the
list of owned blocks worked out where a definition stood in for them: a
signature's field, say. Returns nothing if there was nothing to do. -/
def workOutCtx (ctx : Expr) : MetaM (Option Expr) := do
  unless ctx.isAppOfArity ``CtxOf.mk 7 do return none
  let args := ctx.getAppArgs
  let mut regs := args[1]!
  let mut changed := false
  if regs.isAppOfArity ``RegMap.get 2 && regs.appArg!.isAppOfArity ``RegMap.mk 17 then
    let tbl := regs.appArg!.getAppArgs
    let mut out := tbl
    for i in [1:17] do
      let e := tbl[i]!
      unless (← isConstructorApp e) || e.getAppFn.isFVar do
        let e' ← whnf e
        unless e' == e do
          out := out.set! i e'
          changed := true
    regs := mkApp regs.appFn! (mkAppN regs.appArg!.getAppFn out)
  let owned ← normOwned args[5]!
  unless owned == args[5]! do changed := true
  let stack ← normStack args[2]!
  unless stack == args[2]! do changed := true
  -- how much is detached from the stack, added up as far as it is known
  let above ← normAbove args[6]!
  unless above == args[6]! do changed := true
  unless changed do return none
  return some (mkAppN ctx.getAppFn
    ((((args.set! 1 regs).set! 2 stack).set! 5 owned).set! 6 above))

def regIdx : Reg → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3 | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14
  | .r15 => 15

def allRegs : Array Reg :=
  #[.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The rules a context is tidied by, read once from `ty_dsimp_core`. -/
initialize ctxSimpCache : IO.Ref (Option (Simp.Context × Simp.SimprocsArray)) ← IO.mkRef none

def ctxSimp : TacticM (Simp.Context × Simp.SimprocsArray) := do
  if let some r := ← ctxSimpCache.get then return r
  let stx ← `(tactic| ty_dsimp_core)
  let some stx ← liftMacroM (expandMacro? stx) | throwError "ty_dsimp_core does not expand"
  let r ← mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  ctxSimpCache.set (some (r.ctx, r.simprocs))
  return (r.ctx, r.simprocs)

/-- For each address term worked out so far, the number it comes to. -/
initialize addrCache : IO.Ref (Std.HashMap Expr Nat) ← IO.mkRef {}

/-- The number a closed address term comes to, by the kernel's evaluator.
What is remembered is remembered under the term with the definitions it
names written out, since a name may come to stand for something else while
an editor is open. -/
def addrNat (e : Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasExprMVar then return none
  if isAddrLit e then return e.appArg!.nat?
  let mut key := e
  for a in e.getAppArgs do
    if let .const n _ := a then
      if let some (.defnInfo d) := (← getEnv).find? n then key := mkApp key d.value
  if let some n := (← addrCache.get)[key]? then return some n
  let n? ← try
      let v ← ofExceptKernelException
        (Kernel.whnf (← getEnv) {} (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit 64) e))
      match v with
      | .lit (.natVal n) => pure (some n)
      | _ => pure (some (← evalAddr e))
    catch _ => pure none
  if let some n := n? then addrCache.modify (·.insert key n)
  return n?

/-- A term with every field taken of a context written out replaced by that
field. A rule's result mentions the context it started from once for each
field it keeps, and each mention is the whole of it. -/
partial def stripProjs (e : Expr) : Expr :=
  e.replace fun e =>
    match e with
    | .app f x =>
      if x.isAppOfArity ``CtxOf.mk 7 && f.isApp && f.appFn!.isConst then
        let i? := match f.appFn!.constName! with
          | ``CtxOf.regs => some 1 | ``CtxOf.stack => some 2 | ``CtxOf.room => some 3
          | ``CtxOf.flags => some 4 | ``CtxOf.owned => some 5 | ``CtxOf.above => some 6
          | _ => none
        i?.map fun i => stripProjs x.getAppArgs[i]!
      else none
    | .proj ``CtxOf i x =>
      if x.isAppOfArity ``CtxOf.mk 7 then some (stripProjs x.getAppArgs[i + 1]!) else none
    | _ => none

/-- A field taken of a context, followed in through whatever the context is
built by until the field itself is reached: the kernel's evaluator opens
each context on the way, and nothing else is worked out. -/
def peelField (env : Environment) (lctx : LocalContext) (e : Expr) : Expr := Id.run do
  let mut e := e
  for _ in [0:64] do
    let (i?, c) := match e with
      | .app f x =>
        if f.isApp && f.appFn!.isConst then
          (match f.appFn!.constName! with
            | ``CtxOf.regs => some 1 | ``CtxOf.stack => some 2 | ``CtxOf.room => some 3
            | ``CtxOf.flags => some 4 | ``CtxOf.owned => some 5 | ``CtxOf.above => some 6
            | _ => none, x)
        else (none, x)
      | .proj ``CtxOf i x => (some (i + 1), x)
      | _ => (none, e)
    let some i := i? | break
    match Kernel.whnf env lctx c with
    | .ok cw =>
      if cw.isAppOfArity ``CtxOf.mk 7 then e := cw.getAppArgs[i]! else break
    | .error _ => break
  return e

/-- Whether a term is a constructor applied, or something applied that
cannot be looked into: the forms a register's type is kept in. -/
def settledHead (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .fvar _ => true
  | .const n _ => match env.find? n with
    | some (.ctorInfo _) => true
    | _ => false
  | _ => false

/-- A context brought to the form it is kept in, without `dsimp` over the
whole of it: it is opened by the kernel's evaluator, each register's type is
worked out by itself, and each part is then tidied alone. -/
def normalCtx (Γ : Expr) : TacticM (Option Expr) := do
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  let ctxW ← kwhnf Γ
  unless ctxW.isAppOfArity ``CtxOf.mk 7 do return none
  let nargs := ctxW.getAppArgs
  let (sctx, sprocs) ← ctxSimp
  let tidy (e : Expr) : MetaM Expr := do return (← Meta.dsimp (stripProjs e) sctx sprocs).1
  let τ := nargs[0]!
  let mut tbl : Array Expr := #[τ]
  for r in allRegs do
    let raw := mkApp nargs[1]! (toExpr r)
    let e ← kwhnf raw
    tbl := tbl.push (← tidy (if settledHead env e then e else raw.headBeta))
  let mut ctxN := mkAppN ctxW.getAppFn #[τ,
    mkApp2 (mkConst ``RegMap.get) τ (mkAppN (mkConst ``RegMap.mk) tbl),
    ← tidy (peelField env lctx nargs[2]!), ← tidy (peelField env lctx nargs[3]!),
    ← tidy (peelField env lctx nargs[4]!), ← tidy (peelField env lctx nargs[5]!),
    ← tidy (peelField env lctx nargs[6]!)]
  if let some c ← workOutCtx ctxN then ctxN ← tidy c
  return some ctxN

/-- A block goal brought to the form it is kept in, without `dsimp` over
the whole of it. Returns whether it did so. -/
def fastNormalize (g : MVarId) (t : Expr) : TacticM Bool := g.withContext do
  if t.hasExprMVar then return false
  let args := t.getAppArgs
  let Γ := args[5]!
  let some ctxN ← normalCtx Γ | return false
  let a := args[4]!
  let aN ← if isAddrLit a then pure a else
    match ← addrNat a with
    | some n => pure (toExpr (BitVec.ofNat 64 n))
    | none => pure a
  let new ← mkFreshExprSyntheticOpaqueMVar
    (mkAppN t.getAppFn #[args[0]!, args[1]!, args[2]!, args[3]!, aN, ctxN]) (← g.getTag)
  g.assign (mkAppN (mkConst ``BlockOk.regsEta) #[args[0]!, args[1]!, args[2]!, args[3]!, a, Γ, new])
  replaceMainGoal [new.mvarId!]
  return true

elab_rules : tactic
  | `(tactic| ty_normalize) => do
    let g ← getMainGoal
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isAppOfArity ``BlockOk 6 do
      evalTactic (← `(tactic| ty_dsimp_ctx))
      return
    let saved ← saveState
    if ← (try fastNormalize g t catch _ => do saved.restore; pure false) then return
    -- a context given by name is opened up
    let mut opened := t
    for _ in [0:4] do
      let ctx := opened.appArg!
      if ctx.isAppOf ``CtxOf.mk || ctx.isFVar || ctx.isMVar || !ctx.getAppFn.isConst then break
      let some ctx' ← unfoldDefinition? ctx | break
      opened := mkApp opened.appFn! ctx'.headBeta
    unless opened == t do
      replaceMainGoal [← g.replaceTargetDefEq opened]
    -- the register types, as a table of the sixteen
    let regs ← whnfR (← mkAppM ``CtxOf.regs #[opened.appArg!])
    unless regs.isAppOf ``RegMap.get && regs.appArg!.isAppOf ``RegMap.mk do
      evalTactic (← `(tactic| refine BlockOk.regsEta ?_))
    evalTactic (← `(tactic| ty_dsimp_ctx))
    -- what a definition still stands in for, worked out
    let g ← getMainGoal
    let t := (← instantiateMVars (← g.getType)).consumeMData
    if t.isAppOfArity ``BlockOk 6 then
      if let some ctx' ← g.withContext (workOutCtx t.appArg!) then
        replaceMainGoal [← g.replaceTargetDefEq (mkApp t.appFn! ctx')]
        evalTactic (← `(tactic| ty_dsimp_ctx))
    -- the address, as a number
    let g ← getMainGoal
    let t := (← instantiateMVars (← g.getType)).consumeMData
    if t.isAppOfArity ``BlockOk 6 then
      let a := t.appFn!.appArg!
      unless isAddrLit a || a.hasFVar || a.hasMVar do
        try
          let n ← evalAddr a
          let lit := toExpr (BitVec.ofNat 64 n)
          let g' ← g.replaceTargetDefEq (mkApp (mkApp t.appFn!.appFn! lit) t.appArg!)
          replaceMainGoal [g']
        catch _ => pure ()

/-- The instruction a closed term denotes. -/
@[implemented_by evalInstrUnsafe]
opaque evalInstr (e : Expr) : MetaM Instr

/-- The instruction in a goal, if it is fully known. -/
def knownInstr (e : Expr) : MetaM (Option Instr) := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasFVar then return none
  try return some (← evalInstr e) catch _ => return none

/-- Runs a tactic with room for long lists. A stack described slot by slot
can be long, and walking such a list takes more nested calls than Lean allows
by default. -/
def deep {α : Type} (x : TacticM α) : TacticM α :=
  withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 16384 }) x

/-- Shows a term without the internal names of unknowns. -/
def ppClean (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.mvars false) (ppExpr (← instantiateMVars e))
  -- One line, however long: these appear inside sentences.
  return fmt.pretty (width := 100000)

/-- The elements of a list written out in full, if the term is one. -/
partial def listElems? (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    (listElems? e.appArg!).map (e.appFn!.appArg! :: ·)
  else none

mutual

/-- A block's shape in the notation used in messages: `16 bytes` for plain
bytes, the typed values with where they start otherwise, and `4 × (…)` for
an array. -/
partial def ppShape (S : Expr) : MetaM String := do
  let S ← instantiateMVars S
  if S.isAppOfArity ``ShapeOf.rep 3 then
    return s!"{← ppClean S.appFn!.appArg!} × ({← ppShape S.appArg!})"
  if S.isAppOfArity ``ShapeOf.raw 2 then
    return s!"{← ppClean S.appArg!} bytes"
  if S.isAppOfArity ``ShapeOf.mk 3 then
    let size ← ppClean S.appFn!.appArg!
    match listElems? S.appArg! with
    | some [] => return s!"{size} bytes"
    | some elems =>
      let mut parts : List String := []
      for p in elems do
        if p.isAppOfArity ``Prod.mk 4 then
          parts := parts ++ [s!"{← ppTy p.appArg!} at byte {← ppClean p.appFn!.appArg!}"]
        else parts := parts ++ [← ppClean p]
      return s!"{size} bytes with {", ".intercalate parts}"
    | none => return ← ppClean S
  ppClean S

/-- A type in the notation used in messages: `int`, `exactly 5`,
`pointer to [int, int]`. Falls back to the Lean term for anything else. -/
partial def ppTy (e : Expr) : MetaM String := do
  -- a type read out of a block's shape arrives as a projection to be worked out
  let e ← whnfR (← instantiateMVars e)
  if e.isConstOf ``Ty.int then return "int"
  if e.isAppOfArity ``Ty.eq 1 then return s!"exactly {← ppClean e.appArg!}"
  if e.isAppOfArity ``Ty.code 1 then return "code pointer"
  if e.isAppOf ``Ty.fn || e.isAppOf ``FnSig.ty || e.isAppOf ``Ty.fnAll || e.isAppOf ``FnSigEx.ty then
    return "function pointer"
  if e.isAppOfArity ``Ty.nullable 1 then return s!"{← ppTy e.appArg!} or null"
  if e.isAppOfArity ``Ty.orErr 1 then return s!"{← ppTy e.appArg!} or an error number"
  if e.isAppOfArity ``Ty.str 1 then
    return if e.appArg!.isConstOf ``Bool.true then "pointer into text, not at its end"
      else "pointer into text"
  if e.isAppOfArity ``Ty.ref 3 then
    let args := e.getAppArgs
    let kind := if args[1]!.isConstOf ``Bool.true then "pointer" else "read-only pointer"
    let index ← ppClean args[2]!
    return s!"{kind} to a block of kind {← ppClean args[0]!}" ++
      (if index == "0" then "" else s!", at byte {index}")
  if e.isAppOfArity ``Ty.ptr 3 then
    let args := e.getAppArgs
    let kind := if args[1]!.isConstOf ``Bool.true then "pointer" else "read-only pointer"
    let index ← ppClean args[2]!
    return s!"{kind} to {← ppShape args[0]!}" ++
      (if index == "0" then "" else s!", at byte {index}")
  ppClean e

end

/-- The name of a register, if the term is one. -/
def regName? (e : Expr) : Option String :=
  match e.constName? with
  | some (.str ``Reg n) => some n
  | _ => none

/-- The outcome of trying to take one step in a block. -/
inductive StepResult
  | stepped
  /-- The block was typed to its end: it was handed over at a label. -/
  | done
  /-- The instruction here ends the block; with why the checker refuses that
  ending, where its walk looked and found it refused. -/
  | endOfBlock (instr : Instr) (why : Option MessageData := none)
  | notABlock

/-- Runs a tactic on one goal and returns the goals it leaves. -/
def runOn (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  setGoals [g]
  -- Without this a failing step is logged and its goal admitted, and the
  -- caller would carry on as if it had succeeded. The fresh scope gives the
  -- named placeholders in `tac` names of their own: without it, a second use
  -- of the same step in one tactic call would be handed the first one's proof.
  deep (Tactic.withoutRecover (withFreshMacroScope tac))
  getUnsolvedGoals

/-- The system call number a context puts in `rax`, if it is exactly known. -/
def syscallNumber (ctx : Expr) : MetaM (Option Nat) := do
  let regTy ← whnf (← mkAppM ``CtxOf.regs #[ctx, mkConst ``Reg.rax])
  unless regTy.isAppOfArity ``Ty.eq 1 do return none
  let v ← instantiateMVars regTy.appArg!
  if v.hasExprMVar || v.hasFVar then return none
  try return some (← evalAddr v) catch _ => return none

/-- A system call that returns and asks nothing of the program's memory:
its number, its name and its rule. -/
def plainCalls : List (Nat × String × Name) :=
  [(1, "write", ``linux_write), (3, "close", ``linux_close), (8, "lseek", ``linux_lseek),
   (257, "openat", ``linux_openat), (74, "fsync", ``linux_fsync),
   (75, "fdatasync", ``linux_fdatasync), (39, "getpid", ``linux_getpid)]

/-- A system call that stores into a buffer: its number and name, the rule
for a buffer in a memory block and the rule for one on the stack, the
register holding the buffer, and how much is stored there: the count in a
register, or a fixed number of bytes. -/
def bufferCalls : List (Nat × String × Name × Name × String × (String ⊕ Nat)) :=
  [(0, "read", ``linux_read, ``linux_read_stack, "rsi", .inl "rdx"),
   (5, "fstat", ``linux_fstat, ``linux_fstat_stack, "rsi", .inr 144),
   (228, "clock_gettime", ``linux_clock_gettime, ``linux_clock_gettime_stack, "rsi", .inr 16),
   (318, "getrandom", ``linux_getrandom, ``linux_getrandom_stack, "rdi", .inl "rsi")]

/-- Whether a call number is one that is typed as a step in a block. -/
def isStepCall (nr : Nat) : Bool :=
  plainCalls.any (·.1 == nr) || bufferCalls.any (·.1 == nr)

/-- The names of the calls that can be typed, for messages. -/
def typedCalls : String :=
  "`read` (0), `write` (1), `close` (3), `fstat` (5), `lseek` (8), `mmap` (9), `getpid` (39), \
   `exit` (60), `fsync` (74), `fdatasync` (75), `clock_gettime` (228), `exit_group` (231), \
   `openat` (257) and `getrandom` (318)"

/-- The shape of a system call's rule: what it leaves to be found out. -/
inductive SysShape
  /-- Nothing but the call number. -/
  | plain
  /-- A buffer in a memory block; `sized` if the count comes from a register. -/
  | block (sized : Bool)
  /-- A buffer on the stack. -/
  | stack (sized : Bool)

/-- Applies a system call's rule at the head of a block goal and returns the
goals it leaves: its premises, and the rest of the block. -/
def applySysRule (goal : MVarId) (rule : Name) (shape : SysShape) :
    TacticM (List MVarId) := do
  let r := mkIdent rule
  let tac ← match shape with
    | .plain => `(tactic| refine BlockOk.sys (by ty_fetch) ($r ?_) ?_)
    | .block true =>
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (S := ?_) (off := ?_) (len := ?_) ?_ ?_ ?_ ?_ ?_) ?_)
    | .block false =>
      `(tactic| refine BlockOk.sys (by ty_fetch) ($r (S := ?_) (off := ?_) ?_ ?_ ?_ ?_) ?_)
    | .stack true =>
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (v := ?_) (d := ?_) (k := ?_) (i := ?_) (S := ?_) (len := ?_)
            ?_ ?_ ?_ ?_ ?_ ?_) ?_)
    | .stack false =>
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (v := ?_) (d := ?_) (k := ?_) (i := ?_) (S := ?_) ?_ ?_ ?_ ?_ ?_) ?_)
  try
    runOn goal (do evalTactic tac)
  catch _ => throwError "`syscall`: the operating system here is not the Linux model"

/-- An exactly known value is itself with nothing added: an address that is
the stack pointer's own is zero bytes above it. -/
theorem Ty.eq_add_zero (v : BitVec 64) : Ty.eq v = Ty.eq (v + 0) := by simp

/-- Types a call whose buffer is on the stack, at the head of a block goal.
Returns the rest of the block. -/
def typeBufferStack (goal : MVarId) (rule : Name) (sized : Bool) : TacticM MVarId := do
  let gs ← applySysRule goal rule (.stack sized)
  -- what the registers hold first: that settles where the buffer is
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        discard <| runOn g (do evalTactic (← `(tactic| first | rfl | exact Ty.eq_add_zero _)))
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``StackAt then
      discard <| runOn g (do evalTactic (← `(tactic| ty_stack_at)))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if (← isProp t) then
      discard <| runOn g (do evalTactic (← `(tactic| ty_stack_in)))
  let some rest := rest? | throwError "unexpected goals"
  return rest

/-- Types a call whose buffer is in memory the program owns, at the head of a
block goal. Returns the rest of the block. -/
def typeBufferOwned (goal : MVarId) (rule : Name) (sized : Bool) : TacticM MVarId := do
  let r := mkIdent rule
  let tac ← if sized then
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (k := ?_) (lo := ?_) (a := ?_) (v := ?_) (S := ?_) (len := ?_) ?_ ?_ ?_ ?_ ?_) ?_)
    else
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (k := ?_) (lo := ?_) (a := ?_) (v := ?_) (S := ?_) ?_ ?_ ?_ ?_) ?_)
  let gs ← runOn goal (do evalTactic tac)
  -- what the registers hold, then which block and field the buffer starts at
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        discard <| runOn g (do evalTactic (← `(tactic| rfl)))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``OwnedByte then
      discard <| deep <| runOn g (do evalTactic (← `(tactic| ty_owned_byte)))
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if (← isProp t) then
      discard <| deep <| runOn g (do evalTactic (← `(tactic| ty_inside)))
  let some rest := rest? | throwError "unexpected goals"
  return rest

/-- A `write` where what the program writes is being shown: the buffer's
address must be exactly known and lie in a block that says its bytes, and
the count exactly known; the bytes offered are then that part of what the
block says. That they satisfy the condition is settled by computing where
it can be, and is left to be shown otherwise. Returns the rest of the block
and what is left. -/
def typeWriteOnly (goal : MVarId) : TacticM (MVarId × List MVarId) := goal.withContext do
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  let Ψ := ty.getAppArgs[3]!
  let ctx := ty.getAppArgs[5]!
  let regTy (r : Name) : MetaM Expr := do whnf (← mkAppM ``CtxOf.regs #[ctx, mkConst r])
  let bufTy ← regTy ``Reg.rsi
  unless bufTy.isAppOfArity ``Ty.eq 1 do
    throwError "`write`: what the program writes is being shown, so the buffer's address in \
      `rsi` must be exactly known, but its type is `{← ppTy bufTy}`. A pointer's type does \
      not say which block it points into, and only a block that says its bytes \
      (`asm_typing … data`) has its address kept"
  let a ← try evalAddr bufTy.appArg! catch _ =>
    throwError "`write`: the buffer's address in `rsi` is not a number written out"
  -- the block the address is in: one that says its bytes
  let mut Ψ' := Ψ
  for _ in [0:4] do
    if Ψ'.isAppOfArity ``MemTy.ofList 2 then break
    let some u ← unfoldDefinition? Ψ' | break
    Ψ' := u.headBeta
  unless Ψ'.isAppOfArity ``MemTy.ofList 2 do
    throwError "`write`: the program's blocks are not a list written out"
  let mut l ← whnf Ψ'.appFn!.appArg!
  let mut found : Option (Nat × Nat) := none
  for _ in [0:256] do
    unless l.isAppOfArity ``List.cons 3 do break
    let cell ← whnf l.getAppArgs[1]!
    if cell.isAppOfArity ``Prod.mk 4 then
      let base ← try evalAddr cell.getAppArgs[2]! catch _ => pure 0
      let lay ← whnf cell.getAppArgs[3]!
      if lay.isAppOfArity ``Layout.mk 5 then
        let said ← whnf lay.getAppArgs[4]!
        if said.isAppOf ``Option.some then
          let n ← try evalNat (← mkAppM ``List.length #[said.appArg!]) catch _ => pure 0
          if base ≤ a && a < base + n then found := some (base, a - base)
    l ← whnf l.getAppArgs[2]!
  let some (base, off) := found
    | throwError "`write`: what the program writes is being shown, and the buffer at address \
        {a} is in no block that says its bytes. Only what a block says it holds is known \
        to be what is written"
  let baseQ ← `((($(Syntax.mkNumLit (toString base)) : BitVec 64)))
  let offQ := Syntax.mkNumLit (toString off)
  let gs ← try
      runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.sys (by ty_fetch)
          (linux_write_only (base := $baseQ) (off := $offQ) (l := ?_) (bs := ?_) rfl rfl rfl rfl ?hl
            ?hs ?ha ?hin ?hR)
          ?rest)))
    catch e =>
      trace[TypedAsm.fast] "write: {e.toMessageData}"
      throwError "`write`: what the program writes is being shown, so `rax` must hold \
        exactly 1, and `rdi` and `rdx` exactly known values"
  let mut rest? : Option MVarId := none
  let mut left : List MVarId := []
  let tagOf (g : MVarId) : MetaM Name := do return (← g.getTag).eraseMacroScopes
  -- which block, what it says, where in it, and that the bytes are within
  -- it: in that order, each settling what the next speaks of
  for want in [`hl, `hs, `ha, `hin] do
    for g in gs do
      if ← g.isAssigned then continue
      unless (← tagOf g) == want do continue
      try
        discard <| runOn g (do evalTactic (← `(tactic| first | exact rfl | decide)))
      catch _ =>
        if want == `hin then
          throwError "`write`: the bytes offered from address {a} do not all lie in the \
            block that says its bytes at {base}: it would write out more than is known"
        throwError "`write`: the block at {base} could not be read for what it says"
  for g in gs do
    if ← g.isAssigned then continue
    let tag ← tagOf g
    if tag == `rest then rest? := some g
    else if tag == `hR then
      -- settled by computing where it can be; where it cannot, it is said
      -- what was offered, and the condition is left to be shown of it
      let after ← try
          runOn g (do evalTactic (← `(tactic| first | decide | decide +kernel | rfl | (simp; done))))
        catch _ => pure [g]
      unless after.isEmpty do
        logInfo m!"`write` at address {(← addrNat ty.getAppArgs[4]!).getD 0}: the program offers \
          the {← (do try pure (toString (← evalNat (← mkAppM ``BitVec.toNat #[(← regTy ``Reg.rdx).appArg!]))) catch _ => pure "?")} \
          bytes at address {a}, byte {off} of the block that says its bytes at {base}; \
          that they are as wanted is left to be shown"
      left := left ++ after
  let some rest := rest? | throwError "ty_block: unexpected goals at `syscall`"
  return (rest, left)

/-- Types a system call that returns, at the head of a block goal, leaving
the rest of the block as the main goal. -/
def typeSyscallStep (goal : MVarId) (nr : Nat) : TacticM Unit := do
  trace[TypedAsm.fast] "system call the long way: {nr}"
  let ctx := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs[5]!
  let sysArg := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs[2]!
  if nr == 1 && sysArg.isAppOf ``Syscall.writesOnly then
    let (rest, left) ← typeWriteOnly goal
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    setGoals ((← getGoals) ++ left)
    return
  if let some (_, _, rule) := plainCalls.find? (·.1 == nr) then
    let gs ← applySysRule goal rule .plain
    let mut rest? : Option MVarId := none
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``BlockOk then rest? := some g
      else discard <| runOn g (do evalTactic (← `(tactic| rfl)))
    let some rest := rest? | throwError "ty_block: unexpected goals at `syscall`"
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    return
  let some (_, name, rule, stackRule, bufReg, size) := bufferCalls.find? (·.1 == nr)
    | throwError "`syscall`: call number {nr} is not typed as a step"
  let sized := size.isLeft
  let saved ← saveState
  try
    let rest ← typeBufferStack goal stackRule sized
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    return
  catch _ => saved.restore
  try
    let rest ← typeBufferOwned goal (Name.mkStr rule.getPrefix (rule.getString! ++ "_owned")) sized
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    return
  catch _ => saved.restore
  let gs ← applySysRule goal rule (.block sized)
  let mut rest? : Option MVarId := none
  let mut left : List MVarId := []
  -- what the registers must hold first: that settles the buffer and the count
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if let some (_, lhs, rhs) := t.eq? then
      unless lhs.isAppOf ``CtxOf.regs do continue
      try
        discard <| runOn g (do evalTactic (← `(tactic| rfl)))
      catch _ =>
        let reg := (regName? lhs.appArg!).getD "the register"
        let actual ← g.withContext do ppTy (← reduce (← mkAppM ``CtxOf.regs #[ctx, lhs.appArg!]))
        if rhs.isAppOf ``Ty.ptr then
          throwError "`{name}` needs `{reg}` to hold a writable pointer to the buffer, the \
            address of stack slots taken with `lea` once `rsp` has a name, or the address of \
            a byte of a block the context owns, but its type is `{actual}`"
        else
          throwError "`{name}` needs the count in `{reg}` to be exactly known, but its type is \
            `{actual}`"
  -- then that the bytes the buffer covers are inside the block and plain
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then continue
    unless ← isProp t do continue
    let after ← try
        runOn g (do evalTactic (← `(tactic| first
          | decide
          | exact rfl
          | ty_inside)))
      catch _ =>
        match size with
        | .inl cntReg =>
          throwError "`{name}` could overwrite something that is not plain bytes: the buffer \
            in `{bufReg}` does not have room for the count in `{cntReg}` in plain bytes of \
            its block"
        | .inr bytes =>
          throwError "`{name}` could overwrite something that is not plain bytes: the buffer \
            in `{bufReg}` does not have room in plain bytes of its block for the {bytes} \
            bytes the kernel stores"
    left := left ++ after
  let some rest := rest? | throwError "ty_block: unexpected goals at `syscall`"
  setGoals [rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left)

initialize registerTraceClass `TypedAsm.fast

/-- For each address a block has been typed up to: which instruction last
gave each register, and the flags, what the context says of them there. It is
what lets a rejection say where a type came from. It is kept by address, and
the last block to pass an address is the one remembered. -/
initialize trailRef :
    IO.Ref (Std.HashMap (UInt64 × Nat) (Std.HashMap String (Nat × String))) ← IO.mkRef {}

/-- Why the checker refused the instruction a step was asked to take, where
it did: said in place of trying the rules one by one. -/
initialize refusal : IO.Ref (Option MessageData) ← IO.mkRef none

/-- How many instructions the next walk is to stop after, where the one
after them is known to be refused: the walk up to it is then taken by
itself, and the refusal is of the first instruction of the next. -/
initialize stepLimit : IO.Ref (Option Nat) ← IO.mkRef none

/-- Says, of the program, why the checker refuses an instruction. -/
def explainReject (atoms : Sym.Atoms) (onStack : Bool) : Sym.Reject → MetaM MessageData
  | .spOperand => return m!"`rsp` cannot be this operand"
  | .notPointer r τ writing => do
    let wanted := if writing then "a writable pointer" else "a pointer"
    let (hint, hazard) := match τ with
      | .nullable _ =>
        (": it must be tested for null first, and `ty_null` then gives the two cases",
          ". An access through null is a page fault")
      | .orErr _ =>
        (": it must be tested for an error first, and `ty_err` then gives the two cases",
          ". An error number used as an address is in the kernel's half: a page fault")
      | .ref .. => (": `ty_open` turns it into a pointer to a block of that kind's shape", "")
      | .eq _ => ("", "")
      | _ => ("", hazardAddress onStack)
    return m!"`{r.name64}` must hold {wanted}, but its type is \
      `{← ppTy (← Sym.denTy atoms τ)}`{hint}{hazard}"
  | .indexUnknown r τ => do
    return m!"the index register `{r.name64}` must hold an exactly known value, but its type \
      is `{← ppTy (← Sym.denTy atoms τ)}`; `ty_name` gives an integer a name. An unknown index \
      could reach outside what the base points to, where there may be no memory (a page \
      fault) or other data"
  | .readOnly r τ => do
    return m!"`{r.name64}` must hold a writable pointer, but its type is \
      `{← ppTy (← Sym.denTy atoms τ)}`. A store to memory that is read-only is a page fault"
  | .notOwned =>
    return m!"the address is not known to be inside a block the context owns{hazardBounds}"
  | .noBlock => return m!"the address is not inside any memory block{hazardBounds}"
  | .noPiece =>
    return m!"those bytes are not known to be inside one piece of the stack{hazardBounds}"
  | .pastBlock => return m!"the access would reach past the end of the block{hazardBounds}"
  | .pastOwned =>
    return m!"the access would reach past the end of the block the context owns \
      there{hazardBounds}"
  | .pastPiece =>
    return m!"the access would reach past the end of its piece of the stack{hazardBounds}"
  | .typedThere =>
    return m!"a typed value of the block reaches into those bytes, and plain bytes may not \
      be stored over it{hazardConfusion}"
  | .notClear =>
    return m!"the bytes are not known to be clear of the typed values the block \
      holds{hazardConfusion}"
  | .notSole =>
    return m!"another typed value of the block reaches into those eight bytes{hazardConfusion}"
  | .roomShort room => do
    return m!"there is not enough free stack: the context has room for \
      {← ppClean (← Sym.denNum atoms room)}. Below the stack the program was given there may \
      be no memory, which is a page fault, or other data, which would be overwritten"
  | .framePieces =>
    return m!"the pieces at the top of the stack do not come to exactly that many bytes"
  | .popPiece => return m!"the top of the stack is not a piece of eight bytes"
  | .divUnknown r τ => do
    return m!"`{r.name64}` must hold an exactly known value for a divide, but its type is \
      `{← ppTy (← Sym.denTy atoms τ)}`: a divide is typed only when it is known not to raise \
      a divide error"
  | .divFault =>
    return m!"the divide is not known to produce a result. Dividing by zero, or a quotient \
      that does not fit, is a divide error"
  | .divThere τ? => do
    let held ← match τ? with
      | some τ => ppTy (← Sym.denTy atoms τ)
      | none => pure "int"
    return m!"the value there must be exactly known, but has type `{held}`: a divide is typed \
      only when its divisor is known not to be zero"
  | .noForm => return m!"the checker has no rule for this form of the instruction"

/-- Says, of the program, what a condition a step left could not be shown. -/
def explainCond (atoms : Sym.Atoms) (instr : Instr) (c : Sym.CondS) :
    MetaM MessageData :=
  let inside : MessageData :=
    if instr.onStack then
      m!"those bytes are not known to be inside one piece of the stack: a bound on the index \
        is needed among the hypotheses{hazardBounds}"
    else
      m!"the bytes are not known to be inside the block: a bound on the index is needed among \
        the hypotheses{hazardBounds}"
  match c with
  | .le _ b => do
    match instr with
    | .push _ | .alu .sub .w64 (.rm_i (.reg .rsp) _) =>
      return m!"there is not enough free stack: the context has room for \
        {← ppClean (← Sym.denNum atoms b)}. Below the stack the program was given there may \
        be no memory, which is a page fault, or other data, which would be overwritten"
    | _ => return inside
  | .lt _ _ => return inside
  | .sub τ υ => do
    return m!"a value of type `{← ppTy (← Sym.denTy atoms τ)}` cannot be stored where \
      `{← ppTy (← Sym.denTy atoms υ)}` is required{hazardConfusion}"
  | .cf _ =>
    return m!"the operation reads the carry flag, which is not known to be defined here. The \
      processor leaves it undefined after some instructions, and the result would then not be \
      determined"
  | .decides .any _ =>
    return m!"the flags are not known here, so they do not decide the condition. The \
      processor leaves them undefined after some instructions, and what this one does would \
      then not be determined"
  | .decides _ _ =>
    return m!"the flags known here do not decide the condition. The processor leaves some \
      flags undefined after some instructions, and which way this goes would then not be \
      determined"
  | .nonzeroW _ v => do
    return m!"the divisor, `{← ppClean (← Sym.denVal atoms v)}`, is not known to be \
      non-zero: a check is needed before the divide. Dividing by zero is a divide error"
  | .zeroW _ _ =>
    return m!"`rdx`, the upper half of the dividend, is not known to be zero: clear it \
      before the divide. Otherwise the quotient may not fit, which is a divide error"
  | .sfill _ _ _ =>
    return m!"`rdx` is not known to hold the sign extension of `rax`: use `cqo` or `cdq` \
      before the divide. Otherwise the quotient may not fit, which is a divide error"
  | c => do return m!"needs `{← ppClean (← Sym.denCond atoms c)}`: it is needed among the hypotheses"

/-- Says, of the program, which part of two contexts a comparison could not
be shown of: the part is the one the checker gives the condition. -/
def explainPart (atoms : Sym.Atoms) (p : Sym.Part) (c : Sym.CondS) : MetaM MessageData := do
  match p, c with
  | .reg r, .sub τ υ =>
    return m!"`{r.name64}` has type `{← ppTy (← Sym.denTy atoms τ)}`, but \
      `{← ppTy (← Sym.denTy atoms υ)}` is required"
  | .stack, .sub τ υ =>
    return m!"a slot of the stack holds `{← ppTy (← Sym.denTy atoms τ)}`, but \
      `{← ppTy (← Sym.denTy atoms υ)}` is required there"
  | .stack, _ => return m!"the pieces of the stack are not of the sizes required"
  | .room, .eqN a b =>
    return m!"the free room on the stack is `{← ppClean (← Sym.denNum atoms a)}`, but \
      `{← ppClean (← Sym.denNum atoms b)}` is required"
  | .flags, _ => return m!"what is known of the flags is not what is required"
  | .detached, _ => return m!"the bytes detached from the stack are not those required"
  | .owned, _ =>
    return m!"the blocks owned do not match: a block taken here must be given back or frozen \
      before control goes there"
  | _, c => return m!"needs `{← ppClean (← Sym.denCond atoms c)}`"

/-- Says why two contexts do not compare at all. -/
def explainNoCompare (atoms : Sym.Atoms) : Sym.NoCompare → MetaM MessageData
  | .detached => return m!"pieces of the stack are detached here that are not where control goes"
  | .stackRest => return m!"the stack does not go on as the one required does"
  | .stackPieces got want =>
    return m!"the stack has {got} pieces written out where {want} are required"
  | .stackPiece k got want => do
    return m!"the piece of the stack {k} from the top is `{← ppShape (← Sym.denShape atoms got)}`, \
      but `{← ppShape (← Sym.denShape atoms want)}` is required"

/-- The same of a return: what the function returns with against what the
code returned to requires. -/
def explainRet (atoms : Sym.Atoms) (p : Sym.Part) (c : Sym.CondS) : MetaM MessageData := do
  match p with
  | .detached =>
    return m!"`ret`: pieces of the stack are still detached; a function must attach them \
      again (`ty_stack_attach`) and leave the stack as it found it"
  | .owned =>
    return m!"`ret`: the blocks owned here are not the ones the function gives back, \
      followed by the caller's own; a function must hand back what its signature says and \
      dispose of anything else it took"
  | p => return m!"`ret`: {← explainPart atoms p c}, where the function returns"

/-- Says, of the program, why the checker refuses a system call. -/
def explainSys (atoms : Sym.Atoms) (name : String) : Sym.SysReject → MetaM MessageData
  | .number τ => do
    return m!"`syscall`: the call number in `rax` must be exactly known, but its type is \
      `{← ppTy (← Sym.denTy atoms τ)}`"
  | .noRule nr =>
    return m!"`syscall`: call number {nr.toNat} has no rule. The calls that can be typed are \
      {typedCalls}"
  | .buffer r τ => do
    return m!"`{name}` needs `{r.name64}` to hold a writable pointer to the buffer, the \
      address of stack slots taken with `lea` once `rsp` has a name, or the address of a byte \
      of a block the context owns, but its type is `{← ppTy (← Sym.denTy atoms τ)}`"
  | .count r τ => do
    return m!"`{name}` needs the count in `{r.name64}` to be exactly known, but its type is \
      `{← ppTy (← Sym.denTy atoms τ)}`"
  | .noRoom buf (some cnt) _ =>
    return m!"`{name}` could overwrite something that is not plain bytes: the buffer in \
      `{buf.name64}` does not have room for the count in `{cnt.name64}` in plain bytes of its \
      block"
  | .noRoom buf none bytes =>
    return m!"`{name}` could overwrite something that is not plain bytes: the buffer in \
      `{buf.name64}` does not have room in plain bytes of its block for the {bytes} bytes the \
      kernel stores"
  | .mmapArg .rdi _ τ => do
    return m!"`mmap` is typed only where the kernel chooses the place: `rdi` must hold exactly \
      0, but its type is `{← ppTy (← Sym.denTy atoms τ)}`. Asked for an address, the kernel may \
      put the memory where it would not of its own accord, such as in the reach of the stack"
  | .mmapArg .rdx _ τ => do
    return m!"`mmap` is typed only for memory to read and write: `rdx` must hold exactly 3, \
      but its type is `{← ppTy (← Sym.denTy atoms τ)}`"
  | .mmapArg r _ τ => do
    return m!"`mmap` is typed only for private memory that is not a file: `{r.name64}` must \
      hold exactly 0x22, but its type is `{← ppTy (← Sym.denTy atoms τ)}`"
  | .mmapLen τ => do
    return m!"`mmap` needs the length in `rsi` to be exactly known, but its type is \
      `{← ppTy (← Sym.denTy atoms τ)}`"
  | .munmap =>
    return m!"`munmap` is typed for a block the context owns: `rax` must hold exactly 11, `rdi` \
      exactly the address of an owned block, and `rsi` an exactly known length"

/-- Whether a context is declared for a label. -/
def ctorIsFor (kName lName : Name) : MetaM Bool := do
  forallTelescope (← inferType (mkConst kName)) fun _ body => do
    let args := body.getAppArgs
    pure (args.size ≥ 2 && args[args.size - 2]!.isConstOf lName)

/-- What a walk through a block does at each move: gives a value a name,
opens a pointer to a block of a kind, or steps over an instruction, with the
context it was come to with and what the step left to be shown. -/
inductive WalkMove
  | name (k : Nat) (r : Reg)
  | opened
  | split (at' : Nat) (i : Instr) (len : BitVec 64)
  | jump (at' : Nat) (i : Instr) (len : BitVec 64)
  | step (at' : Nat) (i : Instr) (len : BitVec 64) (arrived : Sym.CtxS) (cs : List Sym.CondS)

/-- Arithmetic left to be shown by the steps of a run, not yet settled. -/
initialize arithLeft : IO.Ref (Array MVarId) ← IO.mkRef #[]

/-- The addresses the walk of a block is to stop before going past: those
with a context of their own to hand over to. Set while a block is walked to
its end; where it is not set, the checker takes one instruction at a time. -/
initialize runStops : IO.Ref (Option (Array Nat)) ← IO.mkRef none

/-- Whether the labels with contexts of their own are all known: they are
where the code typing is made from a family of contexts given label by
label. Only then does a walk follow a jump to an address that is not one. -/
initialize labelsKnown : IO.Ref Bool ← IO.mkRef false

/-- Set when a run has recorded for itself which instruction gave each
register what it holds. -/
initialize trailDone : IO.Ref Bool ← IO.mkRef false

/-- The context the checker's last step left, as it is written and as a
term, with what the term's variables stand for. -/
initialize symKept : IO.Ref (Option (Expr × Sym.CtxS × Sym.Atoms)) ← IO.mkRef none

/-- Shapes' sizes written out, and what has no variable in it worked out, in
something left to be shown: so that arithmetic sees numbers. -/
def normLeaf (kwhnf : Expr → MetaM Expr) (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if e.isAppOfArity ``ShapeOf.size 2 then
      let S ← whnf e.appArg!
      if S.isAppOfArity ``ShapeOf.mk 3 then return .visit S.getAppArgs[1]!
      return .continue
    if e.isApp && !e.hasFVar && !e.hasExprMVar && !e.hasLooseBVars then
      let f := e.getAppFn
      if f.isConst && [``HAdd.hAdd, ``HMul.hMul, ``HPow.hPow, ``HSub.hSub, ``BitVec.toNat,
          ``stackOff, ``Scale.shift, ``NarrowW.bytes].contains f.constName! then
        try
          if let .lit (.natVal k) ← kwhnf e then return .done (mkNatLit k)
        catch _ => pure ()
    return .continue)

/-- Whether the user has marked any fact of their own for the checker: the
library's own are not counted. -/
def hasUserFacts : MetaM Bool := do
  let some ext ← Meta.getSimpExtension? `asm_fact | return false
  let thms ← ext.getTheorems
  return thms.lemmaNames.toList.any fun
    | .decl n .. => n != ``imulTrunc_fst && n != ``aluSub_fst && n != ``aluAdd_fst
    | _ => true

/-- A term rewritten by the facts the user has marked for the checker, with
what is known here: so that a value may be recognised as the one a context
speaks of where a fact says they are the same. -/
def simpFacts (e : Expr) : TacticM Expr := do
  try
    -- numbers are put in the form a fact is stated with: `1`, not `1#64`
    let e ← Meta.transform e (pre := fun x => do
      if x.isAppOfArity ``BitVec.ofNat 2 then
        if let (some w, some k) := (x.getAppArgs[0]!.nat?, x.getAppArgs[1]!.nat?) then
          return .done (← mkNumeral (mkApp (mkConst ``BitVec) (mkNatLit w)) k)
      return .continue)
    let stx ← `(tactic| simp only [asm_fact, *])
    let sc ← mkSimpContext stx (eraseLocal := false)
    let (r, _) ← sc.dischargeWrapper.with fun d? => Lean.Meta.simp e sc.ctx sc.simprocs d?
    return r.expr
  catch ex =>
    trace[TypedAsm.fast] "the facts could not be used: {ex.toMessageData}"
    return e

/-- Proves what the checker leaves to be shown. It is taken apart into its
parts, and each is settled the cheapest way that does: by one of the proofs
offered with what the checker was told, by the two sides being the same, by
working out a comparison of numbers; and only what is left after that goes to
a tactic, arithmetic to `omega` and the rest to the side-condition search. -/
partial def closeNeeds (env : Environment) (lctx : LocalContext)
    (kwhnf tidy : Expr → MetaM Expr) (offered : Array Expr) (P : Expr) : TacticM Expr := do
  let known (e : Expr) : Bool :=
    e.isForall || (match e.getAppFn with
      | .const n _ => [``And, ``True, ``Eq, ``LE.le, ``LT.lt, ``Ne, ``Not, ``Sub, ``Or,
          ``Exists].contains n
      | _ => false)
  let P ← if known P then pure P else kwhnf P
  if P.isAppOfArity ``And 2 then
    let a := P.appFn!.appArg!
    let b := P.appArg!
    return mkApp4 (mkConst ``And.intro) a b (← closeNeeds env lctx kwhnf tidy offered a)
      (← closeNeeds env lctx kwhnf tidy offered b)
  if P.isConstOf ``True then return mkConst ``True.intro
  for pr in offered do
    if Kernel.isDefEqGuarded env lctx (← inferType pr) P then return pr
  if let some (_, lhs, rhs) := P.eq? then
    if Kernel.isDefEqGuarded env lctx lhs rhs then
      return ← mkExpectedTypeHint (← mkEqRefl lhs) P
  let leaf ← tidy P
  if leaf.isConstOf ``True then return mkConst ``True.intro
  let natLit (e : Expr) : MetaM (Option Nat) := do
    if e.hasFVar || e.hasExprMVar then return none
    match ← kwhnf e with
    | .lit (.natVal k) => return some k
    | _ => return none
  let ble (a b : Expr) : MetaM Expr := do
    return mkApp3 (mkConst ``Nat.le_of_ble_eq_true) a b (← mkEqRefl (mkConst ``Bool.true))
  let overNat := leaf.getAppNumArgs ≥ 1 && leaf.getAppArgs[0]!.isConstOf ``Nat
  if leaf.isAppOfArity ``LE.le 4 && overNat then
    let a := leaf.appFn!.appArg!
    let b := leaf.appArg!
    if let some x ← natLit a then
      if let some y ← natLit b then
        if x ≤ y then return ← ble a b
      else if b.isAppOfArity ``HAdd.hAdd 6 then
        let m := b.appFn!.appArg!
        let c := b.appArg!
        if let some y ← natLit c then
          if x ≤ y then
            return mkApp5 (mkConst ``Nat.le_trans) a c b (← ble a c)
              (mkApp2 (mkConst ``Nat.le_add_left) c m)
  if leaf.isAppOfArity ``LT.lt 4 && overNat then
    let a := leaf.appFn!.appArg!
    let b := leaf.appArg!
    if let some x ← natLit a then
      if let some y ← natLit b then
        if x < y then
          return ← mkExpectedTypeHint (← ble (mkNatAdd a (mkNatLit 1)) b) leaf
  -- left for a tactic: arithmetic with the sizes written out, to `omega`
  let arith := overNat &&
    (leaf.isAppOfArity ``LE.le 4 || leaf.isAppOfArity ``LT.lt 4 || leaf.isAppOfArity ``Eq 3)
  let goalTy ← if arith then normLeaf kwhnf leaf else pure leaf
  let g ← mkFreshExprSyntheticOpaqueMVar goalTy
  -- arithmetic is set aside, to be settled with the rest of its kind at once
  if arith then
    arithLeft.modify (·.push g.mvarId!)
    return g
  let saved ← saveState
  let settled ← try
      let left ← runOn g.mvarId! do
        evalTactic (← `(tactic| first
          | trivial
          -- flags known to be defined have the carry flag defined
          | exact fun _ hf => Flags.cf_isSome_of_known hf
          | ty_decided
          | ty_side
          -- two exactly known values the same by arithmetic, with the
          -- definitions of the file at hand opened
          | (refine Sub.of_eq ?_; ty_arith)))
      pure left.isEmpty
    catch _ => pure false
  unless settled do
    saved.restore
    -- by the facts the user has marked for the checker, with what is known here
    unless ← hasUserFacts do throwError "left over"
    let left ← runOn g.mvarId! do
      evalTactic (← `(tactic| first
        | (simp [asm_fact, *]; done)
        | (refine Sub.of_eq ?_; simp [asm_fact, *]; done)))
    unless left.isEmpty do throwError "left over"
  return g

/-- A goal of arithmetic with what a function's requirement of its caller
says of the room on the stack put among its hypotheses: the caller left at
least as much as the function's signature says it needs, written out. -/
def withNeedFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let mut hyps : Array Hypothesis := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let pf? ← (do
      try
        if t.isAppOfArity ``FnSig.CallerOk 5 then
          return some (← mkAppM ``FnSig.CallerOk.room #[d.toExpr])
        if t.isAppOfArity ``FnSigEx.CallerOk 8 then
          let seq := mkLambda `i .default (mkConst ``Nat) (toExpr (0 : BitVec 64))
          let x ← mkAppOptM ``Chosen.dec #[some t.getAppArgs[0]!, none, some seq]
          return some (← mkAppM ``FnSig.CallerOk.room
            #[← mkAppM ``FnSigEx.CallerOk.each #[d.toExpr, x]])
        return none
      catch _ => return none : MetaM (Option Expr))
    let some pf := pf? | continue
    let ty ← whnfR (← inferType pf)
    unless ty.isAppOfArity ``LE.le 4 do continue
    -- what the signature needs, as its definition writes it
    let need := ty.appFn!.appArg!
    let need' ← (do
      try
        unless need.isApp do return need
        let sig := need.appArg!
        let some sigU ← unfoldDefinition? sig | return need
        let w ← whnfR (mkApp need.appFn! sigU)
        return w
      catch _ => return need : MetaM Expr)
    let ty' := mkApp4 ty.getAppFn ty.getAppArgs[0]! ty.getAppArgs[1]! need' ty.appArg!
    unless ← isDefEq ty ty' do continue
    hyps := hyps.push { userName := `hneed, type := ty', value := pf }
  if hyps.isEmpty then return g
  let (_, g') ← g.assertHypotheses hyps
  return g'

/-- Settles the arithmetic `closeNeeds` set aside: all of it by one call
where that succeeds, and otherwise each part by itself. -/
def closeArithLeft : TacticM Unit := do
  let gs ← arithLeft.modifyGet fun gs => (gs, #[])
  if gs.isEmpty then return
  let each : TacticM Unit := do
    for g in gs do
      if ← g.isAssigned then continue
      let left ← try
          runOn g do evalTactic (← `(tactic| first | omega | bv_omega | ty_side))
        catch _ =>
          -- with what the caller's requirement says of the room
          let g' ← withNeedFacts g
          runOn g' do evalTactic (← `(tactic| first | omega | bv_omega))
      unless left.isEmpty do throwError "left over"
  if gs.size == 1 then
    each
    return
  let tys ← gs.mapM fun g => do instantiateMVars (← g.getType)
  -- the parts as one conjunction, the last innermost
  let n := tys.size
  let mut conj := tys[n - 1]!
  let mut tails : Array Expr := #[conj]
  for i in [1:n] do
    conj := mkApp2 (mkConst ``And) tys[n - 1 - i]! conj
    tails := tails.push conj
  let all ← (gs[0]!).withContext do mkFreshExprSyntheticOpaqueMVar conj
  let saved ← saveState
  let ok ← try
      let left ← runOn all.mvarId! do evalTactic (← `(tactic| first | omega | bv_omega))
      pure left.isEmpty
    catch _ => pure false
  unless ok do
    saved.restore
    each
    return
  -- each part from the whole
  let mut h := all
  for i in [0:n] do
    if i == n - 1 then
      gs[i]!.assign h
    else
      let rest := tails[n - 2 - i]!
      gs[i]!.assign (mkApp3 (mkConst ``And.left) tys[i]! rest h)
      h := mkApp3 (mkConst ``And.right) tys[i]! rest h

/-- Introduces the flags hypotheses of one side of a conditional jump. When
the flags are known exactly they are substituted. The fact about which way
the condition went is named `hcond`. -/
def introBranch : TacticM Unit := do
  let hcond := mkIdent `hcond
  -- `rfl` must be written without macro hygiene, or `rintro` takes it for a name.
  let subst := mkIdent `rfl
  evalTactic (← `(tactic| first
    | rintro f $subst:ident $hcond:ident
    | (intro f hflags $hcond:ident; try dsimp only at hflags)))
  -- What an unsigned comparison's outcome says about the two numbers is put
  -- among the hypotheses as `hlt` or `hge`, for bounds on an index.
  let hlt := mkIdent `hlt
  let hge := mkIdent `hge
  -- only where the flags are those of a comparison: matching the lemmas
  -- against flags of another kind would set about computing them
  -- only where the flags are those of a comparison and the condition is one
  -- of "below" and "not below": the lemma is picked from the condition and
  -- the way it went. Matching a lemma against flags or a condition of
  -- another kind would set about computing them.
  let lemma? : Option (Name × Bool) ← withMainContext do
    let some d := (← getLCtx).findFromUserName? `hcond | pure none
    let t ← instantiateMVars d.type
    unless (t.find? (·.isConstOf ``AluOp.cmp)).isSome do return none
    let some (_, lhs, rhs) := t.eq? | pure none
    unless lhs.isAppOfArity ``Cond.eval 2 do return none
    let c := lhs.appArg!
    let went := rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isConstOf ``Bool.true
    let wentNot := rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isConstOf ``Bool.false
    if c.isConstOf ``Cond.b && went then pure (some (``cmp_below, true))
    else if c.isConstOf ``Cond.b && wentNot then pure (some (``cmp_not_below, false))
    else if c.isConstOf ``Cond.ae && went then pure (some (``cmp_ae, false))
    else if c.isConstOf ``Cond.ae && wentNot then pure (some (``cmp_not_ae, true))
    else pure none
  if let some (lem, below) := lemma? then try
    let name := if below then hlt else hge
    Tactic.withoutRecover do evalTactic (← `(tactic|
      (have $name := $(mkIdent lem) $hcond
       try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at $name:ident)))
  catch _ => pure ()
  -- What a test of the zero flag says of the result the flag was set from
  -- is put among the hypotheses as `hz`, that it is zero, or `hnz`, that it
  -- is not: for a comparison the result is the difference.
  let zero? : Option (Name × Bool) ← withMainContext do
    let some d := (← getLCtx).findFromUserName? `hcond | pure none
    let t ← instantiateMVars d.type
    let some (_, lhs, rhs) := t.eq? | pure none
    unless lhs.isAppOfArity ``Cond.eval 2 do return none
    let c := lhs.appArg!
    let F := lhs.appFn!.appArg!
    let went := rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isConstOf ``Bool.true
    let wentNot := rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isConstOf ``Bool.false
    let direct := F.isAppOf ``Flags.ofResult
    let ofOp := F.isAppOfArity ``Prod.snd 3 && F.appArg!.isAppOf ``AluOp.apply
    unless direct || ofOp do return none
    if c.isConstOf ``Cond.e && went then
      pure (some (if direct then ``zero_of_e' else ``zero_of_e, true))
    else if c.isConstOf ``Cond.e && wentNot then
      pure (some (if direct then ``ne_zero_of_not_e' else ``ne_zero_of_not_e, false))
    else if c.isConstOf ``Cond.ne && went then
      pure (some (if direct then ``ne_zero_of_ne' else ``ne_zero_of_ne, false))
    else if c.isConstOf ``Cond.ne && wentNot then
      pure (some (if direct then ``zero_of_not_ne' else ``zero_of_not_ne, true))
    else pure none
  if let some (lem, isZero) := zero? then try
    let name := mkIdent (if isZero then `hz else `hnz)
    Tactic.withoutRecover do evalTactic (← `(tactic|
      (have $name := $(mkIdent lem) $hcond
       try simp only [AluOp.apply, subBorrow_fst, addCarry_fst, BitVec.and_self, BitVec.or_self]
         at $name:ident)))
  catch _ => pure ()

/-- Closes a goal reached under an assumption about a condition that the
exactly known flags contradict. Returns whether it did. -/
def closeIfImpossible (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [g]
    Tactic.withoutRecover do
      evalTactic (← `(tactic| (refine absurd $(mkIdent `hcond) ?_; decide)))
    return (← getUnsolvedGoals).isEmpty
  catch _ =>
    saved.restore
    -- The flags may come from a value known only by a fact about it: an
    -- error number, or a byte that is not zero.
    let isErr ← g.withContext do
      (← getLCtx).anyM fun d => do
        let t ← instantiateMVars d.type
        return t.isAppOf ``SysErr || t.isAppOf ``Ne || t.isAppOf ``LT.lt
    unless isErr do return false
    try
      setGoals [g]
      Tactic.withoutRecover do
        evalTactic (← `(tactic| (
          refine absurd $(mkIdent `hcond) ?_
          try simp only [SysErr] at *
          simp only [Cond.eval, Flags.ofResult, AluOp.apply, subBorrow, bind, Option.bind, pure,
            Option.map, Option.some.injEq]
          try simp only [BitVec.and_self, BitVec.or_self]
          first
            | bv_omega
            | (simp only [BitVec.msb_eq_decide, beq_iff_eq, decide_eq_true_eq,
                 decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false, Nat.not_le,
                 Nat.not_lt]
               bv_omega))))
      return (← getUnsolvedGoals).isEmpty
    catch _ =>
      saved.restore
      return false

/-! ## Handing a block over at a label

Where a block comes to a label with contexts of its own, by a jump or by
running into it, one of those contexts is found that the context reached
may stand for: the label's contexts are tried in turn, each with its
parameters worked out by matching it part by part against the context
reached. The comparison itself is then the checker's, made on terms within
the walk; here the context is only chosen. -/

/-- What is known of a labelled code typing: the program, where it is put,
the contexts given label by label, and the address of each label. -/
initialize labelCache :
    IO.Ref (Array (Expr × Expr × Expr × Expr × Array (Nat × Name))) ← IO.mkRef #[]

/-- Set while a walk is asked only to hand a block over at the label after
its first instruction: if it cannot, it does nothing, and the instruction is
not stepped over. -/
initialize intoOnly : IO.Ref Bool ← IO.mkRef false

/-- What is said where the walk the kernel is asked to confirm is not the
one its driver found: a fault in the tactics, said as one, and never passed
over by typing the block some other way. -/
def disagreement : MessageData :=
  m!"the checker's walk did not come to what was found for this block's ending. This is a \
    fault in the tactics, not in the program"

def labelInfo (Φ : Expr) : MetaM (Option (Expr × Expr × Expr × Array (Nat × Name))) := do
  if let some (_, p, b, T, ls) := (← labelCache.get).find? (·.1 == Φ) then return some (p, b, T, ls)
  let mut f := Φ
  for _ in [0:4] do
    if f.isAppOf ``CodeTy.ofLabels then break
    let some f' ← unfoldDefinition? f | return none
    f := f'.headBeta
  unless f.isAppOf ``CodeTy.ofLabels && f.getAppNumArgs ≥ 3 do return none
  let args := f.getAppArgs
  let T := args[args.size - 1]!
  let base := args[args.size - 2]!
  let prog := args[args.size - 3]!
  let .const tn _ := T.getAppFn | return none
  let some (.inductInfo _) := (← getEnv).find? tn | return none
  let .forallE _ L _ _ ← whnf (← inferType T) | return none
  let .const ln _ := L.getAppFn | return none
  let some (.inductInfo linfo) := (← getEnv).find? ln | return none
  let mut out : Array (Nat × Name) := #[]
  for l in linfo.ctors do
    try
      if let some n ← addrNat (← mkAppM ``Asm.addr #[prog, base, mkConst l]) then
        out := out.push (n, l)
    catch _ => pure ()
  labelCache.modify (·.push (Φ, prog, base, T, out))
  return some (prog, base, T, out)

/-- The type a register holding the address `v` is given, where `v` is the
address of a label with one declared context: a pointer to the function
there, where that context is a signature's entry, and otherwise to the code
there, where the context has nothing left open. -/
def codeTypeAt (Φ : Expr) (v : Nat) : MetaM (Option Expr) := do
  let mut f := Φ
  for _ in [0:4] do
    if f.isAppOf ``CodeTy.ofLabels then break
    let some f' ← unfoldDefinition? f | return none
    f := f'.headBeta
  unless f.isAppOf ``CodeTy.ofLabels && f.getAppNumArgs ≥ 3 do return none
  let args := f.getAppArgs
  let T := args[args.size - 1]!
  let base := args[args.size - 2]!
  let prog := args[args.size - 3]!
  let .const tn _ := T.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? tn | return none
  let mut found : Array (Option Expr) := #[]
  for c in info.ctors do
    let some ci := (← getEnv).find? c | continue
    let r ← forallTelescope ci.type fun xs body => do
      let bs := body.getAppArgs
      unless bs.size ≥ 2 do return none
      let some l := bs[bs.size - 2]!.getAppFn.constName? | return none
      let some n ← addrNat (← mkAppM ``Asm.addr #[prog, base, mkConst l]) | return none
      unless n == v do return none
      let ctx := bs[bs.size - 1]!
      if ctx.isAppOf ``FnSig.entry && ctx.getAppNumArgs ≥ 1 && !ctx.getAppArgs[0]!.hasFVar then
        return some (some (← mkAppM ``FnSig.ty #[ctx.getAppArgs[0]!]))
      if ctx.isAppOf ``FnSigEx.entry && ctx.getAppNumArgs ≥ 3 && !ctx.getAppArgs[2]!.hasFVar then
        return some (some (← mkAppM ``FnSigEx.ty #[ctx.getAppArgs[2]!]))
      if xs.size == 0 && !ctx.hasFVar then return some (some (← mkAppM ``Ty.code #[ctx]))
      return some none
    if let some x := r then found := found.push x
  let #[some τ] := found | return none
  return some τ

/-- How a context reached is made ready to be compared with one wanted,
where the comparison is being looked for on the walk's behalf: registers
holding exactly a block's address are made pointers where the context
wanted has pointers. Set by the walk's driver around each search, so that
the search compares what the checker will. -/
initialize castRef : IO.Ref (Option (Sym.CtxS → Sym.CtxS → Option Sym.CtxS)) ← IO.mkRef none

/-- The context the last search compared, where it was so made ready. -/
initialize castCtx : IO.Ref (Option Sym.CtxS) ← IO.mkRef none

/-- The kind of block an `mmap` is being tried as, where a block did not
type with the memory its program's to own. -/
initialize mmapKindRef : IO.Ref (Option Nat) ← IO.mkRef none

/-- The kinds of block a memory typing declares. -/
def declaredKinds (Ψ : Expr) : MetaM (Array Nat) := do
  let mut Ψ' := Ψ
  for _ in [0:4] do
    if Ψ'.isAppOfArity ``MemTy.ofList 2 then break
    let some u ← unfoldDefinition? Ψ' | break
    Ψ' := u.headBeta
  unless Ψ'.isAppOfArity ``MemTy.ofList 2 do return #[]
  let mut l ← whnf Ψ'.appArg!
  let mut out := #[]
  for _ in [0:256] do
    unless l.isAppOfArity ``List.cons 3 do break
    let cell ← whnf l.getAppArgs[1]!
    if cell.isAppOfArity ``Prod.mk 4 then
      let t ← whnf cell.getAppArgs[2]!
      if let some k := (t.nat? <|> t.rawNatLit?) then out := out.push k
    l ← whnf l.getAppArgs[2]!
  return out

/-- What was shown where an ending was looked for, with what it is a proof
of: the walk's leaf is the same statement wherever the walk names no value,
and is then not shown a second time. -/
initialize leafProofs : IO.Ref (Array (Expr × Expr)) ← IO.mkRef #[]

/-- Keeps the proof an ending was found with, where it speaks of no value
the walk names. -/
def keepLeaf (named : Array (Nat × Reg)) (g : Expr) : MetaM Unit := do
  unless named.isEmpty do return
  let pf ← instantiateMVars g
  if pf.hasExprMVar then return
  let ty ← instantiateMVars (← g.mvarId!.getType)
  leafProofs.modify (·.push (ty, pf))

/-- The proof kept of a statement, if there is one and everything it refers
to is still there. -/
def keptLeaf? (ty : Expr) : MetaM (Option Expr) := do
  let some (_, pf) := (← leafProofs.get).find? (·.1 == ty) | return none
  let env ← getEnv
  return if pf.getUsedConstants.all env.contains then some pf else none

/-- A hand-over found: at which instruction, to which label's context and
which of them, with the parameters it is taken at. The parameters may speak
of the values the walk names, by the variables in `temps` that stood for
them when the context was chosen. -/
structure EnterInfo where
  at' : Nat
  t : Nat
  Δ : Sym.CtxS
  lName : Name
  kName : Name
  params : Array Expr
  temps : Array (Nat × Expr)

/-- Two parts of a context, one with parameters yet to be found, brought
together where they can be: lists piece by piece, so that one piece that
differs does not keep the others' parameters from being found. -/
partial def matchPart (p a : Expr) : MetaM Unit := do
  let p ← instantiateMVars p
  unless p.hasExprMVar do return
  if p.isAppOfArity ``List.cons 3 && a.isAppOfArity ``List.cons 3 then
    matchPart p.getAppArgs[1]! a.getAppArgs[1]!
    matchPart p.getAppArgs[2]! a.getAppArgs[2]!
  else
    try discard <| isDefEq p a catch _ => pure ()

/-- Finds the unknowns of a pattern context that are numbers or values, from
a context reached, by arithmetic on the terms the two are read as
(`Sym.Match`), and assigns them. Unknowns it does not settle are left. -/
def solveByTerms (unknowns : Array Expr) (curE patE : Expr) : MetaM Unit := do
  try
    let patI ← instantiateMVars patE
    let open? ← unknowns.filterM fun m => do
      return (← instantiateMVars m).isMVar
    unless open?.isEmpty do
      let ((cur?, pat?), sc) ← (do
        let a ← Sym.reifyCtx curE
        let b ← Sym.reifyCtx patI
        return (a, b) : Sym.ReifyM _).run {}
      if let (some cur, some pat) := (cur?, pat?) then
        let idx (tbl : Array Expr) : Array (Nat × Expr) :=
          open?.filterMap fun m => (tbl.findIdx? (· == m)).map (·, m)
        let nums := idx sc.num
        let vals := idx sc.val
        let sol := Sym.Match.ctx ⟨nums.toList.map (·.1), vals.toList.map (·.1)⟩ pat cur
        for (i, m) in nums do
          if let some (_, t) := sol.num.find? (·.1 == i) then
            let e ← Sym.denNum sc t
            if !e.hasExprMVar && (← isDefEq (← inferType e) (← inferType m)) then
              m.mvarId!.assign e
        for (i, m) in vals do
          if let some (_, t) := sol.val.find? (·.1 == i) then
            let e ← Sym.denVal sc t
            if !e.hasExprMVar && (← isDefEq (← inferType e) (← inferType m)) then
              m.mvarId!.assign e
  catch _ => pure ()

/-- A value of a kind a function may choose, with its parts unknown: an
unknown for a value by itself, and for a pair an unknown for each side. -/
partial def mkChosen (ι : Expr) : MetaM (Expr × Array Expr) := do
  let ι' ← whnfR ι
  if ι'.isAppOfArity ``Prod 2 then
    let (a, ma) ← mkChosen ι'.getAppArgs[0]!
    let (b, mb) ← mkChosen ι'.getAppArgs[1]!
    return (← mkAppM ``Prod.mk #[a, b], ma ++ mb)
  else
    let m ← mkFreshExprMVar ι
    return (m, #[m])

/-- Each label context that has been written out, as a function of its
parameters: read once, by the constructor that declares it. -/
initialize patCache : IO.Ref (Std.HashMap (Name × UInt64) (Option Expr)) ← IO.mkRef {}

/-- One of a label's contexts taken at the parameters that bring it closest
to a context reached: the parameters, and the context at them. Nothing where
a parameter is left that nothing settles. A parameter that is a number or a
value is found by arithmetic on the terms the two contexts are read as
(`Sym.Match`); what a context demands that is among what is known fixes the
parameters it speaks of; and anything else is found by bringing the two
contexts together as they are written. -/
def matchCtor (kName lName : Name) (ΓE : Expr) : TacticM (Option (Array Expr × Expr)) := do
  let kTy ← inferType (mkConst kName)
  let key := (kName, kTy.hash)
  let pat? ← match (← patCache.get)[key]? with
    | some (some pat) =>
      -- written out before: only whether it is this label's is looked at
      let mine ← forallTelescope kTy fun _ body => do
        let args := body.getAppArgs
        pure (args.size ≥ 2 && args[args.size - 2]!.isConstOf lName)
      pure (if mine then some pat else none)
    | some none => pure none
    | none =>
      let (r, mine) ← forallTelescope kTy fun xs body => do
        let args := body.getAppArgs
        if args.size < 2 then return (none, false)
        let mine := args[args.size - 2]!.isConstOf lName
        let some patN ← normalCtx args[args.size - 1]!
          | do trace[TypedAsm.fast] "{kName}: its context is not written out"
               return (none, mine)
        return (some (← mkLambdaFVars xs patN), mine)
      patCache.modify (·.insert key r)
      pure (if mine then r else none)
  let some patAbs := pat? | return none
  -- the parameters as unknowns of this scope, not of the one the context
  -- was written out in
  let (ms, _, bodyM) ← forallMetaTelescope kTy
  let patM := patAbs.beta ms
  let pat0 := bodyM.appArg!
  -- what a context demands that is no comparison is looked for among what is
  -- known: that fixes the parameters it speaks of to the ones in scope
  for m in ms do
    let t ← instantiateMVars (← inferType m)
    unless ← isProp t do continue
    if t.isAppOf ``LT.lt || t.isAppOf ``LE.le || t.isAppOf ``GT.gt || t.isAppOf ``GE.ge ||
        t.isAppOf ``Eq || t.isAppOf ``Ne || t.isAppOf ``Not then continue
    try m.mvarId!.assumption catch _ => pure ()
  -- the parameters that are numbers or values, by arithmetic on the terms
  solveByTerms ms ΓE patM
  unless patM.isAppOfArity ``CtxOf.mk 7 && ΓE.isAppOfArity ``CtxOf.mk 7 do return none
  let pa := patM.getAppArgs
  let ga := ΓE.getAppArgs
  if pa[1]!.isAppOfArity ``RegMap.get 2 && pa[1]!.appArg!.isAppOfArity ``RegMap.mk 17 &&
      ga[1]!.isAppOfArity ``RegMap.get 2 && ga[1]!.appArg!.isAppOfArity ``RegMap.mk 17 then
    let pt := pa[1]!.appArg!.getAppArgs
    let gt := ga[1]!.appArg!.getAppArgs
    for j in [1:17] do matchPart pt[j]! gt[j]!
  else return none
  for j in [2:7] do matchPart pa[j]! ga[j]!
  let mut params : Array Expr := #[]
  for m in ms do
    if ← isProp (← inferType m) then continue
    let v ← instantiateMVars m
    if v.hasExprMVar then
      trace[TypedAsm.fast] "{kName}: nothing settles the parameter {← inferType m}: {patM}"
      return none
    params := params.push v
  let Δ0 ← instantiateMVars pat0
  if Δ0.hasExprMVar then return none
  return some (params, Δ0)

/-- What is to be shown where a block is handed over: that the code typing
allows the context there, and what the comparison left. -/
def leafType (Φ : Expr) (atoms : Sym.Atoms) (t : Nat) (Δ : Sym.CtxS)
    (cs : List Sym.CondS) : MetaM Expr := do
  let mut allE := mkConst ``True
  for c in cs.reverse do
    allE := mkApp2 (mkConst ``And) (← Sym.denCond atoms c) allE
  return mkApp2 (mkConst ``And)
    (mkAppN Φ #[toExpr (BitVec.ofNat 64 t), ← Sym.denCtx atoms Δ]) allE

/-- The same under what a conditional jump's going one way says of the
flags, where the block is handed over on that side of one. -/
def sideType (Φ : Expr) (atoms : Sym.Atoms) (t : Nat) (Δ : Sym.CtxS)
    (cs : List Sym.CondS) (branch? : Option (Sym.FlagsS × Cond × Bool)) : MetaM Expr := do
  let leaf ← leafType Φ atoms t Δ cs
  let some (fl, c, b) := branch? | return leaf
  let P ← Sym.denFlags atoms fl
  withLocalDeclD `f (mkConst ``Flags) fun f => do
    let ev ← mkEq (← mkAppM ``Cond.eval #[f, toExpr c]) (← mkAppM ``Option.some #[toExpr b])
    mkForallFVars #[f] (← mkArrow (mkApp P f).headBeta (← mkArrow ev leaf))

/-- That the code typing allows a label's context, taken at given
parameters, at the label's address: the proof, the context as it is
written, and what the context demands, left open. -/
def labelProofRaw (Φ : Expr) (lName kName : Name) (params : Array Expr) (t : Nat) :
    TacticM (Expr × Expr × Array MVarId) := do
  let tE := toExpr (BitVec.ofNat 64 t)
  let mut e := mkConst kName
  let mut ty ← inferType e
  let mut pi := 0
  let mut prems : Array MVarId := #[]
  for _ in [0:64] do
    let ty' ← if ty.isForall then pure ty else whnfR ty
    unless ty'.isForall do break
    let d := ty'.bindingDomain!
    if ← isProp d then
      let m ← mkFreshExprSyntheticOpaqueMVar d
      prems := prems.push m.mvarId!
      e := mkApp e m
      ty := ty'.bindingBody!.instantiate1 m
    else
      let some p := params[pi]? | throwError "a parameter is missing"
      pi := pi + 1
      e := mkApp e p
      ty := ty'.bindingBody!.instantiate1 p
  let Δ0 := ty.appArg!
  let stmt := mkAppN Φ #[tE, Δ0]
  let ex ← whnf stmt
  unless ex.isAppOfArity ``Exists 2 do throwError "the code typing is not given by labels"
  let L := ex.getAppArgs[0]!
  let p := ex.getAppArgs[1]!
  let body := (mkApp p (mkConst lName)).headBeta
  unless body.isAppOfArity ``And 2 do throwError "the code typing is not given by labels"
  let A := body.getAppArgs[0]!
  let B := body.getAppArgs[1]!
  let some (_, lhs, _) := A.eq? | throwError "the code typing is not given by labels"
  let eqPf ← mkExpectedTypeHint (← mkEqRefl lhs) A
  let u ← getLevel L
  let pf ← mkExpectedTypeHint
    (mkApp4 (mkConst ``Exists.intro [u]) L p (mkConst lName)
      (mkApp4 (mkConst ``And.intro) A B eqPf e)) stmt
  return (pf, Δ0, prems)

/-- That the code typing allows a label's context, taken at given
parameters, at the label's address: the proof, for the context with its
register types as a table (which must be `Δ`), and what the context demands,
left open. -/
def labelProof (Φ : Expr) (lName kName : Name) (params : Array Expr) (t : Nat)
    (Δ : Sym.CtxS) (atoms : Sym.Atoms) : TacticM (Expr × Array MVarId) := do
  let env ← getEnv
  let lctx ← getLCtx
  let tE := toExpr (BitVec.ofNat 64 t)
  let (pf, Δ0, prems) ← labelProofRaw Φ lName kName params t
  -- with its register types as a table, it is the context the walk compared
  let ΔE ← Sym.denCtx atoms Δ
  let P := mkApp Φ tE
  let tabled := mkApp3 (mkConst ``Ctx.asTable) P Δ0 pf
  unless Kernel.isDefEqGuarded env lctx (← inferType tabled) (mkApp P ΔE) do
    throwError "the context chosen is not the one compared"
  return (← mkExpectedTypeHint tabled (mkApp P ΔE), prems)

/-- Shows the conditions a comparison of contexts left: each by `special`
where that has a way of its own for it, and otherwise as anything the
checker leaves is shown. A condition not shown is reported as the part of
the contexts it is about, where the parts are given. Returns the conditions
as one statement, and its proof. -/
def showConds (atoms : Sym.Atoms) (cs : List Sym.CondS) (parts : List Sym.Part)
    (explain : Sym.Part → Sym.CondS → MetaM MessageData)
    (special : Sym.CondS → Expr → TacticM (Option Expr) := fun _ _ => pure none) :
    TacticM (Expr × Expr) := do
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  let mut hn := mkConst ``True.intro
  let mut allE := mkConst ``True
  arithLeft.set #[]
  let partOf (i : Nat) : Option Sym.Part := if parts.length == cs.length then parts[i]? else none
  let mut i := cs.length
  for c in cs.reverse do
    i := i - 1
    let leaf ← Sym.denCond atoms c
    let h ← try
        match ← special c leaf with
        | some h => pure h
        | none => closeNeeds env lctx kwhnf pure #[] leaf
      catch e =>
        trace[TypedAsm.fast] "a comparison leaves: {leaf}"
        match partOf i with
        | some p => throwError (← explain p c)
        | none => throw e
    hn := mkApp4 (mkConst ``And.intro) leaf allE h hn
    allE := mkApp2 (mkConst ``And) leaf allE
  try closeArithLeft
  catch e =>
    trace[TypedAsm.fast] "a comparison leaves arithmetic: {(← arithLeft.get).map mkMVar}"
    -- the first comparison of numbers the arithmetic does not settle
    let mut j := 0
    for c in cs do
      if (c matches .eqN .. | .le .. | .lt ..) then
        if let some p := partOf j then
          let g ← mkFreshExprSyntheticOpaqueMVar (← Sym.denCond atoms c)
          let ok ← try
              let l ← runOn g.mvarId! (do
                evalTactic (← `(tactic| first | omega | bv_omega | ty_side)))
              pure l.isEmpty
            catch _ => pure false
          unless ok do throwError (← explain p c)
      j := j + 1
    throw e
  return (allE, ← instantiateMVars hn)

/-- Shows what `leafType` states: the label's context at the parameters
found is allowed there, with what it demands shown from what is known; and
each thing the comparison left is shown. Fails if anything is left over. -/
def solveLeaf (g : MVarId) (Φ : Expr) (lName kName : Name) (params : Array Expr)
    (t : Nat) (Δ : Sym.CtxS) (cs : List Sym.CondS) (atoms : Sym.Atoms)
    (parts : List Sym.Part := []) : TacticM Unit :=
    g.withContext do
  let goals ← getGoals
  let (pf2, prems) ← labelProof Φ lName kName params t Δ atoms
  let P := mkApp Φ (toExpr (BitVec.ofNat 64 t))
  let ΔE ← Sym.denCtx atoms Δ
  for m in prems do
    if ← m.isAssigned then continue
    let left ← runOn m do
      evalTactic (← `(tactic| first | assumption | omega | decide | ty_arith))
    unless left.isEmpty do
      trace[TypedAsm.fast] "a premise of `{kName}` is left over: {m}"
      throwError "what the context demands is not known here: \
        `{← ppClean (← instantiateMVars (← m.getType))}`"
  -- what the comparison left, each with the part of the contexts it is about
  let (allE, hn) ← showConds atoms cs parts (explainPart atoms)
  g.assign (mkApp4 (mkConst ``And.intro) (mkApp P ΔE) allE pf2 hn)
  setGoals goals

/-- Shows what `sideType` states: on a side of a conditional jump, what its
going that way says is brought in first, and a side the flags rule out needs
nothing more. -/
def solveSide (g : MVarId) (branch? : Option (Sym.FlagsS × Cond × Bool)) (Φ : Expr)
    (lName kName : Name) (params : Array Expr) (t : Nat) (Δ : Sym.CtxS) (cs : List Sym.CondS)
    (atoms : Sym.Atoms) (parts : List Sym.Part := []) : TacticM Unit := do
  if branch?.isNone then
    solveLeaf g Φ lName kName params t Δ cs atoms parts
    return
  let goals ← getGoals
  let [g₁] ← runOn g introBranch | throwError "unexpected goals"
  unless ← closeIfImpossible g₁ do
    solveLeaf g₁ Φ lName kName params t Δ cs atoms parts
  setGoals goals

/-- Looks for a context allowed at the label at `t` that the context reached
may stand for, with everything that takes shown: tried here with the values
the walk names standing as variables, so that the walk can be given the
context before it is made. -/
def findEnter (Φ : Expr) (atoms : Sym.Atoms) (named : Array (Nat × Reg))
    (cur : Sym.CtxS) (at' t : Nat) (branch? : Option (Sym.FlagsS × Cond × Bool) := none)
    (why? : Option (IO.Ref (Array MessageData)) := none) :
    TacticM (Option (EnterInfo × Sym.Atoms)) := do
  -- why a context declared at the label is not one to hand over to
  let note (k : Name) (m : MessageData) : TacticM Unit := do
    if let some r := why? then r.modify (·.push m!"{k.components.getLast!}: {m}")
  let some (_, _, T, labels) ← labelInfo Φ | return none
  let some (_, lName) := labels.find? (·.1 == t) | return none
  let .const tn _ := T.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? tn | return none
  let bv := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let decls := named.map fun (_, r) => (Name.mkSimple s!"{r.name64}₀", bv)
  withLocalDeclsDND decls fun temps => do
    let mut atoms' := atoms
    for ((k, _), v) in named.zip temps do
      let pad := atoms'.val ++ Array.replicate (k + 1 - atoms'.val.size) (toExpr (0 : BitVec 64))
      atoms' := { atoms' with val := pad.set! k v }
    -- the values of the table without the variables that stood for names
    let unnamed (vals : Array Expr) : Array Expr := Id.run do
      let mut out := vals
      for (k, _) in named do
        if k < out.size then out := out.set! k (toExpr (0 : BitVec 64))
      return out
    let ΓE ← Sym.denCtx atoms' cur
    for kName in info.ctors do
      let s ← saveState
      let r ← try (do
          let some (params, Δ0) ← matchCtor kName lName ΓE
            | do
              if ← ctorIsFor kName lName then
                note kName m!"nothing here settles the parameters its context is declared with"
              return none
          let some ΔN ← normalCtx Δ0
            | do trace[TypedAsm.fast] "{kName}: its context is not written out"; return none
          let (Δ?, atoms'') ← (Sym.reifyCtx ΔN).run atoms'
          let some Δ := Δ? | do trace[TypedAsm.fast] "{kName}: its context is not read"; return none
          -- nothing new that the context speaks of may speak of a value the
          -- walk names
          let fresh := atoms''.val.extract atoms'.val.size atoms''.val.size ++
            atoms''.num.extract atoms'.num.size atoms''.num.size ++
            atoms''.ty.extract atoms'.ty.size atoms''.ty.size ++
            atoms''.shape.extract atoms'.shape.size atoms''.shape.size ++
            atoms''.flags.extract atoms'.flags.size atoms''.flags.size ++
            atoms''.stack.extract atoms'.stack.size atoms''.stack.size ++
            atoms''.owned.extract atoms'.owned.size atoms''.owned.size
          if fresh.any fun e => temps.any fun v => e.containsFVar v.fvarId! then return none
          -- what the stack and the blocks owned go on as may be written
          -- differently in the two contexts and be the same
          let sameAtom (tbl : Array Expr) (i? j? : Option Nat) : MetaM (Option Nat) := do
            let (some i, some j) := (i?, j?) | return j?
            if i == j then return j?
            let (some a, some b) := (tbl[i]?, tbl[j]?) | return j?
            if ← withoutModifyingState (isDefEq a b) then return some i
            return j?
          let Δ := { Δ with
            stackRest := ← sameAtom atoms''.stack cur.stackRest Δ.stackRest
            ownedRest := ← sameAtom atoms''.owned cur.ownedRest Δ.ownedRest }
          let cur ← (do
            match (← castRef.get).bind (· cur Δ) with
            | some c => castCtx.set (some c); pure c
            | none => pure cur)
          let some cs := Sym.subCtx cur Δ
            | do
              trace[TypedAsm.fast] "{kName}: the contexts do not compare"
              if let some w := Sym.subWhy cur Δ then note kName (← explainNoCompare atoms'' w)
              return none
          let parts := (Sym.subParts cur Δ).getD []
          let g ← mkFreshExprSyntheticOpaqueMVar (← sideType Φ atoms'' t Δ cs branch?)
          try solveSide g.mvarId! branch? Φ lName kName params t Δ cs atoms'' parts
          catch e =>
            trace[TypedAsm.fast] "{kName}: {e.toMessageData}"
            note kName e.toMessageData
            throw e
          keepLeaf named g
          let info : EnterInfo := ⟨at', t, Δ, lName, kName, params, (named.map (·.1)).zip temps⟩
          return some (info, { atoms'' with val := unnamed atoms''.val }))
        catch e =>
          trace[TypedAsm.fast] "{kName}: {e.toMessageData}"
          pure none
      s.restore
      if r.isSome then return r
    return none

/-- What a return's leaf says of the context returned to: some context is
the one the code on top of the stack wants, and the one compared stands for it. -/
def leavePred (atoms : Sym.Atoms) (i : Nat) (Δ : Sym.CtxS) : MetaM Expr := do
  let tyE := atoms.ty.getD i (mkConst ``Ty.int)
  let ΔE ← Sym.denCtx atoms Δ
  withLocalDeclD `D (mkConst ``Ctx) fun D => do
    mkLambdaFVars #[D] (mkApp2 (mkConst ``And)
      (mkApp2 (mkConst ``Sub) tyE (← mkAppM ``Ty.code #[D])) (mkApp2 (mkConst ``CtxSub) ΔE D))

/-- What is to be shown where a block returns: that the type on top of the
stack is that of code wanting a context the one compared stands for, and
what the comparison left. -/
def leaveType (atoms : Sym.Atoms) (i : Nat) (Δ : Sym.CtxS) (cs : List Sym.CondS) :
    MetaM Expr := do
  let mut allE := mkConst ``True
  for c in cs.reverse do
    allE := mkApp2 (mkConst ``And) (← Sym.denCond atoms c) allE
  let p ← leavePred atoms i Δ
  return mkApp2 (mkConst ``And) (mkApp2 (mkConst ``Exists [Level.one]) (mkConst ``Ctx) p) allE

/-- Shows what `leaveType` states. `Δ0` is the context the code on the stack
wants, `mid` the context compared as it is written, and `hmid` that `mid`
stands for `Δ0`. -/
def solveLeave (g : MVarId) (i : Nat) (Δ0 mid hmid : Expr) (Δ : Sym.CtxS)
    (cs : List Sym.CondS) (atoms : Sym.Atoms) (hsub? : Option Expr := none)
    (parts : List Sym.Part := []) : TacticM Unit :=
    g.withContext do
  let env ← getEnv
  let lctx ← getLCtx
  let goals ← getGoals
  let tyE := atoms.ty.getD i (mkConst ``Ty.int)
  let ΔE ← Sym.denCtx atoms Δ
  -- the return address's type is that of code wanting the context, or of
  -- code ready for a family of contexts of which it is one
  let A := mkApp2 (mkConst ``Sub) tyE (← mkAppM ``Ty.code #[Δ0])
  let hA₀ := hsub?.getD (mkApp (mkConst ``Sub.refl) tyE)
  unless Kernel.isDefEqGuarded env lctx (← inferType hA₀) A do
    throwError "the return address is not typed as code wanting the context returned to"
  let hA ← mkExpectedTypeHint hA₀ A
  -- the context compared, with its register types as a table, stands for
  -- the one returned to as it does written out
  let P ← withLocalDeclD `X (mkConst ``Ctx) fun X => do
    mkLambdaFVars #[X] (mkApp2 (mkConst ``CtxSub) X Δ0)
  let tabled := mkApp3 (mkConst ``Ctx.asTable) P mid hmid
  let B := mkApp2 (mkConst ``CtxSub) ΔE Δ0
  unless Kernel.isDefEqGuarded env lctx (← inferType tabled) B do
    throwError "the context returned with is not the one compared"
  let hB ← mkExpectedTypeHint tabled B
  let p ← leavePred atoms i Δ
  let ex := mkApp2 (mkConst ``Exists [Level.one]) (mkConst ``Ctx) p
  let pf := mkApp4 (mkConst ``Exists.intro [Level.one]) (mkConst ``Ctx) p Δ0
    (mkApp4 (mkConst ``And.intro) A B hA hB)
  let (allE, hn) ← showConds atoms cs parts (explainRet atoms) fun c leaf => do
    if let .ownedEq .. := c then
      -- the blocks owned are the ones the function gives back, then the
      -- caller's own: that is the caller's requirement
      let m ← mkFreshExprSyntheticOpaqueMVar leaf
      let left ← runOn m.mvarId! do
        evalTactic (← `(tactic| first
          | rfl
          | exact FnSig.CallerOk.owned_back (by assumption) rfl
          | exact FnSigEx.CallerOk.owned_back (by assumption) _ rfl))
      unless left.isEmpty do throwError "left over"
      return some m
    if (leaf.find? (·.isConstOf ``CtxOf.above)).isSome then
      -- how much is detached from the stack is the same whichever value a
      -- function with a chosen result returns with: its caller's requirement
      let m ← mkFreshExprSyntheticOpaqueMVar leaf
      let left ← try
          runOn m.mvarId! do
            evalTactic (← `(tactic| first
              | rfl
              | exact (FnSigEx.CallerOk.detached (by assumption) _).symm
              | exact FnSigEx.CallerOk.detached (by assumption) _))
        catch _ => pure [m.mvarId!]
      if left.isEmpty then return some m
    return none
  g.assign (mkApp4 (mkConst ``And.intro) ex allE pf hn)
  setGoals goals

/-- A return found typed within a walk: at which instruction, the context
compared as a term and as written, the context the code returned to wants,
and that the one stands for the other. -/
structure LeaveInfo where
  at' : Nat
  Δ : Sym.CtxS
  Δ0 : Expr
  mid : Expr
  hmid : Expr
  /-- Where the return address is ready for a family of contexts: that it
  is ready for the one returned into. -/
  hsub : Option Expr := none
  temps : Array (Nat × Expr) := #[]

/-- Looks at a return. The type on top of the stack says what context the
code returned to wants. Where that is written out, it is what the context
the return leaves is compared with. Where it is a caller's, known only by
the requirement a function has of its caller, the comparison is with what
the function's signature says it returns with, which the requirement makes
stand for the caller's. Everything that takes is shown here first, with the
values the walk names standing as variables. -/
def findLeave (atoms : Sym.Atoms) (named : Array (Nat × Reg)) (cur : Sym.CtxS)
    (at' : Nat) (why? : Option (IO.Ref (Option MessageData)) := none) :
    TacticM (Option (LeaveInfo × Sym.Atoms)) := do
  -- why the return is refused, where it is
  let note (m : MessageData) : TacticM Unit := do
    if let some r := why? then r.set (some m)
  let noAddress : MessageData := m!"`ret` needs a return address on top of the stack, but the \
    context does not have one there. Control would go to whatever number is there: a \
    general-protection fault where the processor has no such address, a page fault where \
    there is no code"
  let isFamily : MessageData := m!"`ret`: the return address here is ready for a family of \
    contexts, one for each value the function may hand back; say which the function returns \
    into with `ty_return_as`"
  let some (i, after) := Sym.afterRet cur
    | do trace[TypedAsm.fast] "return: the top of the stack is not seen to be a return address: {toExpr cur.stack}, rsp {toExpr (cur.regs.get .rsp)}"; note noAddress; return none
  let some tyE := atoms.ty[i]? | do note noAddress; return none
  let tyW ← whnf tyE
  unless tyW.isAppOfArity ``Ty.code 1 || tyW.isAppOfArity ``Ty.codeAll 1 do
    trace[TypedAsm.fast] "return: the type on top of the stack is not code's: {tyW}"
    note noAddress
    return none
  let family := tyW.isAppOfArity ``Ty.codeAll 1
  let Δ0 := tyW.appArg!
  -- the context to compare with, and that it stands for the one wanted
  let written ← (do
    if family then return none
    if Δ0.isFVar then return none
    let some _ ← normalCtx Δ0 | return none
    return some (Δ0, ← mkAppM ``CtxSub.refl #[Δ0]) : TacticM (Option (Expr × Expr)))
  let via ← match written with
    | some x => pure (some x)
    | none => (do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        unless t.isAppOfArity ``FnSig.CallerOk 5 do continue
        let a := t.getAppArgs
        unless a[2]! == Δ0 do continue
        let mid ← mkAppM ``FnSig.returned #[a[0]!, a[1]!, a[3]!, a[4]!,
          ← mkAppM ``CtxOf.owned #[Δ0], ← mkAppM ``CtxOf.above #[Δ0]]
        return some (mid, ← mkAppM ``FnSig.CallerOk.ret #[d.toExpr])
      -- a function whose results depend on a value it chooses, once it has
      -- said which: the requirement of its caller, at that value
      if Δ0.isApp then
        let x := Δ0.appArg!
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let t ← instantiateMVars d.type
          unless t.isAppOfArity ``FnSigEx.CallerOk 8 do continue
          let a := t.getAppArgs
          unless a[3]! == Δ0.appFn! do continue
          let hmid ← mkAppM ``FnSigEx.CallerOk.retAt #[d.toExpr, x]
          let hmidTy ← whnfR (← inferType hmid)
          unless hmidTy.isAppOfArity ``CtxSub 2 do continue
          return some (hmidTy.getAppArgs[0]!, hmid)
      return none : TacticM (Option (Expr × Expr)))
  unless family || via.isSome do
    trace[TypedAsm.fast] "return: nothing says what the code returned to accepts"
    note m!"`ret` needs the caller's requirement (`sig.CallerOk …`) among the hypotheses"
    return none
  let bv := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let decls := named.map fun (_, r) => (Name.mkSimple s!"{r.name64}₀", bv)
  let s ← saveState
  let r ← withLocalDeclsDND decls fun temps => do
    let mut atoms' := atoms
    for ((k, _), v) in named.zip temps do
      let pad := atoms'.val ++ Array.replicate (k + 1 - atoms'.val.size) (toExpr (0 : BitVec 64))
      atoms' := { atoms' with val := pad.set! k v }
    try
      -- A return address ready for a family of contexts, one for each value
      -- the function may choose: which value it returns with is found from
      -- what it returns with, and its caller's requirement is taken there.
      let chosen ← (do
        unless family do return none
        let afterE ← Sym.denCtx atoms' after
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let t ← instantiateMVars d.type
          unless t.isAppOfArity ``FnSigEx.CallerOk 8 do continue
          let a := t.getAppArgs
          let ι := a[0]!
          let ret := a[3]!
          let some inst ← (try pure (some (← synthInstance (mkApp (mkConst ``Chosen) ι)))
            catch _ => pure none) | continue
          let seqTy ← mkArrow (mkConst ``Nat) bv
          let want ← withLocalDeclD `s seqTy fun sv => do
            mkLambdaFVars #[sv] (mkApp ret (mkApp3 (mkConst ``Chosen.dec) ι inst sv))
          unless ← isDefEq Δ0 want do continue
          let (xM, opens) ← mkChosen ι
          let Δx := (mkApp ret xM).headBeta
          let pat ← mkAppM ``FnSig.returned #[← mkAppM ``FnSigEx.pick #[a[1]!, xM], a[2]!, a[4]!,
            a[5]!, ← mkAppM ``CtxOf.owned #[Δx], ← mkAppM ``CtxOf.above #[Δx]]
          let some patN ← normalCtx pat | continue
          solveByTerms opens afterE patN
          let x ← instantiateMVars xM
          if x.hasExprMVar then
            trace[TypedAsm.fast] "return: nothing settles which value the function returns with"
            continue
          let Δ1 := (mkApp ret x).headBeta
          -- with the blocks owned written out: the ones the function gives
          -- for that value, then what its caller owned besides
          let hmid ← mkAppM ``FnSigEx.CallerOk.retAt #[d.toExpr, x]
          let hmidTy ← whnfR (← inferType hmid)
          unless hmidTy.isAppOfArity ``CtxSub 2 do continue
          let mid := hmidTy.getAppArgs[0]!
          return some (Δ1, mid, hmid, mkApp4 (mkConst ``Sub.codeAll_at) ι inst ret x)
        return none : TacticM (Option (Expr × Expr × Expr × Expr)))
      let some (Δ0, mid, hmid, hsub?) := (match chosen, via with
          | some (Δ1, mid, hmid, hsub), _ => some (Δ1, mid, hmid, some hsub)
          | none, some (mid, hmid) => if family then none else some (Δ0, mid, hmid, none)
          | none, none => none)
        | do trace[TypedAsm.fast] "return: nothing says which context the function returns into"
             note isFamily
             return none
      let some ΔN ← normalCtx mid
        | do trace[TypedAsm.fast] "return: the context is not written out: {mid}"; return none
      let (Δ?, atoms'') ← (Sym.reifyCtx ΔN).run atoms'
      let some Δ := Δ? | do trace[TypedAsm.fast] "return: the context is not read: {ΔN}"; return none
      let sameAtom (tbl : Array Expr) (i? j? : Option Nat) : MetaM (Option Nat) := do
        let (some i, some j) := (i?, j?) | return j?
        if i == j then return j?
        let (some a, some b) := (tbl[i]?, tbl[j]?) | return j?
        if ← withoutModifyingState (isDefEq a b) then return some i
        return j?
      let Δ := { Δ with
        stackRest := ← sameAtom atoms''.stack after.stackRest Δ.stackRest
        ownedRest := ← sameAtom atoms''.owned after.ownedRest Δ.ownedRest }
      let after ← (do
        match (← castRef.get).bind (· cur Δ) with
        | some c =>
          castCtx.set (some c)
          pure (((Sym.afterRet c).map (·.2)).getD after)
        | none => pure after)
      let some cs := Sym.subCtx after Δ
        | do
          trace[TypedAsm.fast] "return: the contexts do not compare"
          match Sym.subWhy after Δ with
          | some .detached => note (← explainRet atoms'' .detached (.eqN after.above Δ.above))
          | some w => note m!"`ret`: {← explainNoCompare atoms'' w}, where the function returns"
          | none => pure ()
          return none
      let g ← mkFreshExprSyntheticOpaqueMVar (← leaveType atoms'' i Δ cs)
      solveLeave g.mvarId! i Δ0 mid hmid Δ cs atoms'' hsub? ((Sym.subParts after Δ).getD [])
      keepLeaf named g
      let mut vals := atoms''.val
      for (k, _) in named do
        if k < vals.size then vals := vals.set! k (toExpr (0 : BitVec 64))
      return some ((⟨at', Δ, Δ0, mid, hmid, hsub?, (named.map (·.1)).zip temps⟩ : LeaveInfo),
        { atoms'' with val := vals })
    catch e =>
      trace[TypedAsm.fast] "return: {e.toMessageData}"
      note e.toMessageData
      pure none
  s.restore
  return r

/-- A call found typed within a walk: where, to which function's context
and which return point, each a label's context at parameters; the variable
that is the type of the return address; and the two contexts as terms. -/
structure CallInfo where
  at' : Nat
  t : Nat
  next : Nat
  j : Nat
  R : Sym.CtxS
  Δ : Sym.CtxS
  R0 : Expr
  lRet : Name
  kRet : Name
  paramsR : Array Expr
  lFn : Name
  kFn : Name
  paramsFn : Array Expr
  temps : Array (Nat × Expr)

/-- What is to be shown where a block calls. -/
def callType (Φ : Expr) (atoms : Sym.Atoms) (c : CallInfo) (cs : List Sym.CondS) :
    MetaM Expr := do
  let mut allE := mkConst ``True
  for x in cs.reverse do
    allE := mkApp2 (mkConst ``And) (← Sym.denCond atoms x) allE
  let tyE := atoms.ty.getD c.j (mkConst ``Ty.int)
  let RE ← Sym.denCtx atoms c.R
  let ΔE ← Sym.denCtx atoms c.Δ
  return mkApp2 (mkConst ``And) (← mkEq tyE (← mkAppM ``Ty.code #[RE]))
    (mkApp2 (mkConst ``And) (mkAppN Φ #[toExpr (BitVec.ofNat 64 c.next), RE])
      (mkApp2 (mkConst ``And) (mkAppN Φ #[toExpr (BitVec.ofNat 64 c.t), ΔE]) allE))

/-- Shows what a context demands from something known that says the same
but for numbers written differently, such as the room on the stack: each
such number is shown equal by arithmetic, with what the caller's requirement
says of the room. Whether it did. -/
def closeFromHyp (m : MVarId) : TacticM Bool := m.withContext do
  let t ← instantiateMVars (← m.getType)
  if t.hasExprMVar then return false
  let targs := t.getAppArgs
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ht ← instantiateMVars d.type
    unless ht.getAppFn == t.getAppFn && ht.getAppNumArgs == targs.size do continue
    let hargs := ht.getAppArgs
    let saved ← saveState
    let r ← try (do
        -- that the two statements are the same, argument by argument
        let mut eq ← mkEqRefl t.getAppFn
        let mut differs := false
        for (a, b) in targs.zip hargs do
          if ← withoutModifyingState (isDefEq a b) then
            eq ← mkCongrFun eq a
          else
            unless (← whnf (← inferType a)).isConstOf ``Nat do return false
            let e ← mkFreshExprSyntheticOpaqueMVar (← mkEq a b)
            let g ← withNeedFacts e.mvarId!
            let left ← runOn g (do evalTactic (← `(tactic| omega)))
            unless left.isEmpty do return false
            eq ← mkCongr eq (← instantiateMVars e)
            differs := true
        unless differs do return false
        m.assign (← mkEqMPR eq d.toExpr)
        return true : TacticM Bool)
      catch _ => pure false
    if r then return true
    saved.restore
  return false

/-- Shows a function's requirement of its caller, from what the function
returns with standing for the context at the return point. -/
def closeCallerOk (m : MVarId) : TacticM Unit := do
  let gs ← runOn m do
    evalTactic (← `(tactic| refine ⟨?gives, ?back, ?need⟩))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    let left ← if t.isAppOf ``CtxSub then
        runOn g (do evalTactic (← `(tactic| ctx_sub)))
      else if t.isAppOf ``LE.le then
        let sigName? := (t.appFn!.appArg!.getAppArgs.back?.bind (·.getAppFn.constName?))
        try runOn g (do evalTactic (← `(tactic| first | decide | omega)))
        catch e =>
          match sigName? with
          | some c =>
            try
              runOn g (do evalTactic (← `(tactic|
                (unfold $(mkIdent c); dsimp only; first | decide | omega))))
            catch _ =>
              -- with the room this code's own caller left it
              let [g'] ← runOn g (do evalTactic (← `(tactic| (unfold $(mkIdent c); dsimp only))))
                | throw e
              runOn (← withNeedFacts g') (do evalTactic (← `(tactic| omega)))
          | none => throw e
      else runOn g (do evalTactic (← `(tactic| first | rfl | decide)))
    unless left.isEmpty do throwError "left over"

/-- Shows what `callType` states. The parameters are those of this scope. -/
def solveCall (g : MVarId) (Φ : Expr) (c : CallInfo) (R0 : Expr)
    (paramsR paramsFn : Array Expr) (cs : List Sym.CondS) (atoms : Sym.Atoms) : TacticM Unit :=
    g.withContext do
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  let goals ← getGoals
  let tyE := atoms.ty.getD c.j (mkConst ``Ty.int)
  let RE ← Sym.denCtx atoms c.R
  let ΔE ← Sym.denCtx atoms c.Δ
  -- the type of the return address
  let A ← mkEq tyE (← mkAppM ``Ty.code #[RE])
  let P ← withLocalDeclD `X (mkConst ``Ctx) fun X => do
    mkLambdaFVars #[X] (← mkEq tyE (← mkAppM ``Ty.code #[X]))
  let h0 ← mkExpectedTypeHint (← mkEqRefl tyE) (mkApp P R0).headBeta
  let tabled := mkApp3 (mkConst ``Ctx.asTable) P R0 h0
  unless Kernel.isDefEqGuarded env lctx (← inferType tabled) A do
    throwError "the return point's context is not the one compared"
  let hA ← mkExpectedTypeHint tabled A
  -- the return point, and the function
  let (hR, premsR) ← labelProof Φ c.lRet c.kRet paramsR c.next c.R atoms
  let (hF, premsF) ← labelProof Φ c.lFn c.kFn paramsFn c.t c.Δ atoms
  for m in premsR ++ premsF do
    if ← m.isAssigned then continue
    let t ← instantiateMVars (← m.getType)
    if ← closeFromHyp m then continue
    if t.isAppOf ``FnSig.CallerOk then
      try closeCallerOk m
      catch e =>
        trace[TypedAsm.fast] "call: the caller's requirement is not shown: {t}"
        throw e
    else
      let left ← try
          runOn m do evalTactic (← `(tactic| first | assumption | omega | decide | ty_arith))
        catch _ => pure [m]
      unless left.isEmpty do
        trace[TypedAsm.fast] "call: a context's demand is not shown: {t}"
        throwError "left over"
  let mut hn := mkConst ``True.intro
  let mut allE := mkConst ``True
  arithLeft.set #[]
  for x in cs.reverse do
    let leaf ← Sym.denCond atoms x
    let h ← try closeNeeds env lctx kwhnf pure #[] leaf
      catch e =>
        trace[TypedAsm.fast] "call: the comparison leaves: {leaf}"
        throw e
    hn := mkApp4 (mkConst ``And.intro) leaf allE h hn
    allE := mkApp2 (mkConst ``And) leaf allE
  try closeArithLeft
  catch e =>
    trace[TypedAsm.fast] "call: the comparison leaves arithmetic: {(← arithLeft.get).map mkMVar}"
    throw e
  let tR := mkAppN Φ #[toExpr (BitVec.ofNat 64 c.next), RE]
  let tF := mkAppN Φ #[toExpr (BitVec.ofNat 64 c.t), ΔE]
  let inner := mkApp4 (mkConst ``And.intro) tF allE hF (← instantiateMVars hn)
  let mid := mkApp4 (mkConst ``And.intro) tR (mkApp2 (mkConst ``And) tF allE) hR inner
  g.assign (mkApp4 (mkConst ``And.intro) A
    (mkApp2 (mkConst ``And) tR (mkApp2 (mkConst ``And) tF allE)) hA mid)
  setGoals goals

/-- Looks at a call to a labelled function that returns to a label. The
function's label says its signature; the registers the function preserves,
the caller's stack and its room are the caller's own; what the argument
registers hold settles which of a family of signatures is meant; and the
return point is the context at the next label that what the function
returns with may stand for. The comparison of the context the call makes
with the function's is then the checker's. -/
def findCall (Φ : Expr) (atoms : Sym.Atoms) (named : Array (Nat × Reg))
    (cur : Sym.CtxS) (at' t next : Nat) : TacticM (Option (CallInfo × Sym.Atoms)) := do
  let some (_, _, T, labels) ← labelInfo Φ | return none
  let some (_, lFn) := labels.find? (·.1 == t) | return none
  let some (_, lRet) := labels.find? (·.1 == next) | return none
  let .const tn _ := T.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? tn | return none
  let bv := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let decls := named.map fun (_, r) => (Name.mkSimple s!"{r.name64}₀", bv)
  let s ← saveState
  let r ← withLocalDeclsDND decls fun temps => do
    let mut atoms' := atoms
    for ((k, _), v) in named.zip temps do
      let pad := atoms'.val ++ Array.replicate (k + 1 - atoms'.val.size) (toExpr (0 : BitVec 64))
      atoms' := { atoms' with val := pad.set! k v }
    let j := atoms'.ty.size
    let some (pushed, rc) := Sym.afterCall cur j | return none
    -- the caller's registers, stack, room and blocks as the function finds them
    let preE ← Sym.denCtx atoms' { pushed with stack := cur.stack }
    let pre := preE.getAppArgs
    let regsE := pre[1]!
    let stackE := pre[2]!
    let roomE := pre[3]!
    let ownedE := pre[5]!
    let aboveE := pre[6]!
    for kFn in info.ctors do
      for kRet in info.ctors do
        let st ← saveState
        let found ← try (do
            let kTy ← inferType (mkConst kFn)
            let (ms, _, body) ← forallMetaTelescope kTy
            let bargs := body.getAppArgs
            if bargs.size < 2 then return none
            unless bargs[bargs.size - 2]!.isConstOf lFn do return none
            let pat0 := bargs[bargs.size - 1]!
            unless pat0.isAppOfArity ``FnSig.entry 5 do return none
            let a := pat0.getAppArgs
            unless ← isDefEq a[1]! regsE do return none
            unless ← isDefEq a[3]! stackE do return none
            unless ← isDefEq a[4]! roomE do return none
            -- what the argument registers hold says which signature
            if regsE.isAppOfArity ``RegMap.get 2 && regsE.appArg!.isAppOfArity ``RegMap.mk 17 then
              let tbl := regsE.appArg!.getAppArgs
              -- first as the facts given to the checker say what they hold:
              -- a value written by a fact is the one a signature speaks of
              if ← hasUserFacts then
                for r in allRegs do
                  if r == .rsp then continue
                  let want ← whnf (← mkAppM ``FnSig.regsIn #[a[0]!, regsE, toExpr r])
                  if (← instantiateMVars want).hasExprMVar then
                    let e := tbl[1 + regIdx r]!
                    let e' ← simpFacts e
                    unless e' == e do matchPart want e'
              for r in allRegs do
                if r == .rsp then continue
                let want ← whnf (← mkAppM ``FnSig.regsIn #[a[0]!, regsE, toExpr r])
                matchPart want tbl[1 + regIdx r]!
            let sig ← instantiateMVars a[0]!
            if sig.hasExprMVar then
              trace[TypedAsm.fast] "call ({kFn}): nothing settles which signature: {sig}"
              return none
            -- the return point: what the function returns with stands for it
            let ownedBack ← mkAppM ``HAppend.hAppend #[← mkAppM ``FnSig.gives #[sig],
              ← mkAppM ``List.drop #[← mkAppM ``List.length #[← mkAppM ``FnSig.takes #[sig]], ownedE]]
            let returned ← mkAppM ``FnSig.returned #[sig, regsE, stackE, roomE, ownedBack, aboveE]
            let some retN ← normalCtx returned | return none
            let some (paramsR, R0) ← matchCtor kRet lRet retN
              | do trace[TypedAsm.fast] "call ({kFn}, {kRet}): the return point's context is not found"
                   return none
            unless ← isDefEq a[2]! R0 do return none
            let Δ0 ← instantiateMVars pat0
            if Δ0.hasExprMVar then return none
            let mut paramsFn : Array Expr := #[]
            for m in ms do
              if ← isProp (← inferType m) then continue
              let v ← instantiateMVars m
              if v.hasExprMVar then return none
              paramsFn := paramsFn.push v
            -- as terms: the return address's type is a variable of its own
            if temps.any fun v => R0.containsFVar v.fvarId! then return none
            let atoms₁ := { atoms' with ty := atoms'.ty.push (← mkAppM ``Ty.code #[R0]) }
            let some RN ← normalCtx R0 | return none
            let some ΔN ← normalCtx Δ0 | return none
            let ((R?, Δ?), atoms₂) ← (do
              let R? ← Sym.reifyCtx RN
              let Δ? ← Sym.reifyCtx ΔN
              return (R?, Δ?) : Sym.ReifyM _).run atoms₁
            let (some R, some Δ) := (R?, Δ?) | return none
            let fresh := atoms₂.val.extract atoms₁.val.size atoms₂.val.size ++
              atoms₂.num.extract atoms₁.num.size atoms₂.num.size ++
              atoms₂.ty.extract atoms₁.ty.size atoms₂.ty.size ++
              atoms₂.shape.extract atoms₁.shape.size atoms₂.shape.size ++
              atoms₂.flags.extract atoms₁.flags.size atoms₂.flags.size ++
              atoms₂.stack.extract atoms₁.stack.size atoms₂.stack.size ++
              atoms₂.owned.extract atoms₁.owned.size atoms₂.owned.size
            if fresh.any fun e => temps.any fun v => e.containsFVar v.fvarId! then return none
            let sameAtom (tbl : Array Expr) (i? j? : Option Nat) : MetaM (Option Nat) := do
              let (some i, some j) := (i?, j?) | return j?
              if i == j then return j?
              let (some a, some b) := (tbl[i]?, tbl[j]?) | return j?
              if ← withoutModifyingState (isDefEq a b) then return some i
              return j?
            let Δ := { Δ with
              stackRest := ← sameAtom atoms₂.stack pushed.stackRest Δ.stackRest
              ownedRest := ← sameAtom atoms₂.owned pushed.ownedRest Δ.ownedRest }
            let (pushed, rc) ← (do
              match (← castRef.get).bind (· cur Δ) with
              | some c =>
                castCtx.set (some c)
                pure ((Sym.afterCall c j).getD (pushed, rc))
              | none => pure (pushed, rc))
            let some cs := Sym.subCtx pushed Δ
              | do trace[TypedAsm.fast] "call: the contexts do not compare"; return none
            let info : CallInfo := ⟨at', t, next, j, R, Δ, R0, lRet, kRet, paramsR, lFn, kFn,
              paramsFn, (named.map (·.1)).zip temps⟩
            let g ← mkFreshExprSyntheticOpaqueMVar (← callType Φ atoms₂ info (rc ++ cs))
            trace[TypedAsm.fast] "call ({kFn}, {kRet}): contexts chosen, showing the rest"
            solveCall g.mvarId! Φ info R0 paramsR paramsFn (rc ++ cs) atoms₂
            keepLeaf named g
            let mut vals := atoms₂.val
            for (k, _) in named do
              if k < vals.size then vals := vals.set! k (toExpr (0 : BitVec 64))
            return some (info, { atoms₂ with val := vals }))
          catch e =>
            let what ← (match e with
              | .internal id _ => do
                pure m!"{(← id.getName)}"
              | _ => pure e.toMessageData)
            trace[TypedAsm.fast] "call ({kFn}, {kRet}): {what}"
            pure none
        st.restore
        if found.isSome then return found
    return none
  s.restore
  return r

/-- Shows the requirement a function that chooses a value has of its
caller: for each value, what an ordinary function would need; and that what
the caller owns besides, and what is detached from its stack, do not depend
on the value. -/
def closeCallerOkEx (m : MVarId) : TacticM Unit := do
  let gs ← runOn m do
    evalTactic (← `(tactic| refine ⟨fun _ => ?each, fun _ => ?frame, fun _ => ?detached⟩))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``FnSig.CallerOk then closeCallerOk g
    else
      let left ← runOn g (do evalTactic (← `(tactic| first | rfl | decide | (simp; done))))
      unless left.isEmpty do throwError "left over"

/-- A call to a function that chooses a value as it returns, found typed
within a walk: the function's label context at parameters, the label the
call returns to, whose contexts are a family over the value, and the
variable that is the return address's type. -/
structure CallAll where
  at' : Nat
  t : Nat
  next : Nat
  j : Nat
  Δ : Sym.CtxS
  lFn : Name
  kFn : Name
  paramsFn : Array Expr
  lRet : Name
  kRet : Name
  ι : Expr
  temps : Array (Nat × Expr)

/-- What is to be shown where a block calls such a function. -/
def callAllType (Φ : Expr) (atoms : Sym.Atoms) (c : CallAll) (cs : List Sym.CondS) :
    MetaM Expr := do
  let mut allE := mkConst ``True
  for x in cs.reverse do
    allE := mkApp2 (mkConst ``And) (← Sym.denCond atoms x) allE
  let tyE := atoms.ty.getD c.j (mkConst ``Ty.int)
  let seqTy ← mkArrow (mkConst ``Nat) (mkApp (mkConst ``BitVec) (mkNatLit 64))
  let preTy ← mkArrow seqTy (mkConst ``Ctx)
  let nextE := toExpr (BitVec.ofNat 64 c.next)
  let p ← withLocalDeclD `pre preTy fun pre => do
    let fam ← withLocalDeclD `x seqTy fun x => do
      mkForallFVars #[x] (mkAppN Φ #[nextE, mkApp pre x])
    mkLambdaFVars #[pre] (mkApp2 (mkConst ``And) (← mkEq tyE (← mkAppM ``Ty.codeAll #[pre])) fam)
  return mkApp2 (mkConst ``And) (mkApp2 (mkConst ``Exists [Level.one]) preTy p)
    (mkApp2 (mkConst ``And) (mkAppN Φ #[toExpr (BitVec.ofNat 64 c.t), ← Sym.denCtx atoms c.Δ]) allE)

/-- Shows what `callAllType` states. The parameters are those of this scope. -/
def solveCallAll (g : MVarId) (Φ : Expr) (c : CallAll) (paramsFn : Array Expr)
    (cs : List Sym.CondS) (atoms : Sym.Atoms) : TacticM Unit := g.withContext do
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  let goals ← getGoals
  let goalTy ← callAllType Φ atoms c cs
  let tyE := atoms.ty.getD c.j (mkConst ``Ty.int)
  unless tyE.isAppOfArity ``Ty.codeAll 1 do
    throwError "the return address is not typed for a family of contexts"
  let pre0 := tyE.appArg!
  let seqTy ← mkArrow (mkConst ``Nat) (mkApp (mkConst ``BitVec) (mkNatLit 64))
  let nextE := toExpr (BitVec.ofNat 64 c.next)
  -- each context of the family is allowed at the return point
  let fam ← withLocalDeclD `x seqTy fun x => do
    let v ← mkAppOptM ``Chosen.dec #[some c.ι, none, some x]
    let (pf, _, prems) ← labelProofRaw Φ c.lRet c.kRet #[v] c.next
    unless prems.isEmpty do throwError "the return point's contexts demand something"
    let want := mkAppN Φ #[nextE, mkApp pre0 x]
    unless ← isDefEq (← inferType pf) want do
      throwError "the return point's contexts are not the family the function returns into"
    mkLambdaFVars #[x] (← mkExpectedTypeHint pf want)
  let ex := goalTy.appFn!.appArg!
  let p := ex.appArg!
  let hEx := mkApp4 (mkConst ``Exists.intro [Level.one]) ex.appFn!.appArg! p pre0
    (← mkAppM ``And.intro #[← mkEqRefl tyE, fam])
  -- the function
  let (hF, premsF) ← labelProof Φ c.lFn c.kFn paramsFn c.t c.Δ atoms
  for m in premsF do
    if ← m.isAssigned then continue
    let t ← instantiateMVars (← m.getType)
    if t.isAppOf ``FnSigEx.CallerOk then closeCallerOkEx m
    else
      let left ← runOn m do
        evalTactic (← `(tactic| first | assumption | omega | decide | ty_arith))
      unless left.isEmpty do throwError "left over"
  let mut hn := mkConst ``True.intro
  let mut allE := mkConst ``True
  arithLeft.set #[]
  for x in cs.reverse do
    let leaf ← Sym.denCond atoms x
    let h ← closeNeeds env lctx kwhnf pure #[] leaf
    hn := mkApp4 (mkConst ``And.intro) leaf allE h hn
    allE := mkApp2 (mkConst ``And) leaf allE
  closeArithLeft
  let tF := mkAppN Φ #[toExpr (BitVec.ofNat 64 c.t), ← Sym.denCtx atoms c.Δ]
  let inner := mkApp4 (mkConst ``And.intro) tF allE hF (← instantiateMVars hn)
  g.assign (mkApp4 (mkConst ``And.intro) ex (mkApp2 (mkConst ``And) tF allE) hEx inner)
  setGoals goals

/-- Looks at a call to a labelled function that chooses a value as it
returns. The function's label says its signature, with nothing left open;
the label after the call has one context for each value; the registers the
function preserves, the caller's stack, its room and what it owns besides
are the caller's own. -/
def findCallAll (Φ : Expr) (atoms : Sym.Atoms) (named : Array (Nat × Reg))
    (cur : Sym.CtxS) (at' t next : Nat) : TacticM (Option (CallAll × Sym.Atoms)) := do
  let some (_, _, T, labels) ← labelInfo Φ | return none
  let some (_, lFn) := labels.find? (·.1 == t) | return none
  let some (_, lRet) := labels.find? (·.1 == next) | return none
  let .const tn _ := T.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? tn | return none
  let bv := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let decls := named.map fun (_, r) => (Name.mkSimple s!"{r.name64}₀", bv)
  let s ← saveState
  let r ← withLocalDeclsDND decls fun temps => do
    let mut atoms' := atoms
    for ((k, _), v) in named.zip temps do
      let pad := atoms'.val ++ Array.replicate (k + 1 - atoms'.val.size) (toExpr (0 : BitVec 64))
      atoms' := { atoms' with val := pad.set! k v }
    let j := atoms'.ty.size
    let some (pushed, rc) := Sym.afterCall cur j | return none
    let preE ← Sym.denCtx atoms' { pushed with stack := cur.stack }
    let pre := preE.getAppArgs
    let regsE := pre[1]!
    let stackE := pre[2]!
    let roomE := pre[3]!
    let ownedE := pre[5]!
    let aboveE := pre[6]!
    for kFn in info.ctors do
      for kRet in info.ctors do
        let st ← saveState
        let found ← try (do
            -- the return point: one context for each value
            let fam? ← forallTelescope (← inferType (mkConst kRet)) fun xs body => do
              let args := body.getAppArgs
              if args.size < 2 || xs.size != 1 then return none
              unless args[args.size - 2]!.isConstOf lRet do return none
              if ← isProp (← inferType xs[0]!) then return none
              return some (← mkLambdaFVars xs args[args.size - 1]!, ← inferType xs[0]!)
            let some (retFam, ι) := fam? | return none
            let kTy ← inferType (mkConst kFn)
            let (ms, _, body) ← forallMetaTelescope kTy
            let bargs := body.getAppArgs
            if bargs.size < 2 then return none
            unless bargs[bargs.size - 2]!.isConstOf lFn do return none
            let pat0 := bargs[bargs.size - 1]!
            unless pat0.isAppOfArity ``FnSigEx.entry 9 do return none
            let a := pat0.getAppArgs
            let sig ← instantiateMVars a[2]!
            if sig.hasExprMVar then return none
            unless ← isDefEq a[3]! regsE do return none
            unless ← isDefEq a[4]! retFam do return none
            unless ← isDefEq a[5]! stackE do return none
            unless ← isDefEq a[6]! roomE do return none
            let frame ← mkAppM ``List.drop
              #[← mkAppM ``List.length #[← mkAppM ``FnSigEx.takes #[sig]], ownedE]
            unless ← isDefEq a[7]! frame do return none
            unless ← isDefEq a[8]! aboveE do return none
            let Δ0 ← instantiateMVars pat0
            if Δ0.hasExprMVar then return none
            let mut paramsFn : Array Expr := #[]
            for m in ms do
              if ← isProp (← inferType m) then continue
              let v ← instantiateMVars m
              if v.hasExprMVar then return none
              paramsFn := paramsFn.push v
            let some ΔN ← normalCtx Δ0 | return none
            -- the return address's type, as the function's context has it,
            -- is a variable of its own
            let some codeAllE := ΔN.getAppArgs[2]!.find? (·.isAppOfArity ``Ty.codeAll 1)
              | return none
            let atoms₁ := { atoms' with ty := atoms'.ty.push codeAllE }
            let (Δ?, atoms₂) ← (Sym.reifyCtx ΔN).run atoms₁
            let some Δ := Δ? | return none
            let fresh := atoms₂.val.extract atoms₁.val.size atoms₂.val.size ++
              atoms₂.num.extract atoms₁.num.size atoms₂.num.size ++
              atoms₂.ty.extract atoms₁.ty.size atoms₂.ty.size ++
              atoms₂.shape.extract atoms₁.shape.size atoms₂.shape.size ++
              atoms₂.flags.extract atoms₁.flags.size atoms₂.flags.size ++
              atoms₂.stack.extract atoms₁.stack.size atoms₂.stack.size ++
              atoms₂.owned.extract atoms₁.owned.size atoms₂.owned.size
            if fresh.any fun e => temps.any fun v => e.containsFVar v.fvarId! then return none
            let sameAtom (tbl : Array Expr) (i? j? : Option Nat) : MetaM (Option Nat) := do
              let (some i, some j) := (i?, j?) | return j?
              if i == j then return j?
              let (some a, some b) := (tbl[i]?, tbl[j]?) | return j?
              if ← withoutModifyingState (isDefEq a b) then return some i
              return j?
            let Δ := { Δ with
              stackRest := ← sameAtom atoms₂.stack pushed.stackRest Δ.stackRest
              ownedRest := ← sameAtom atoms₂.owned pushed.ownedRest Δ.ownedRest }
            let some cs := Sym.subCtx pushed Δ
              | do trace[TypedAsm.fast] "call ({kFn}): the contexts do not compare"; return none
            let info : CallAll := ⟨at', t, next, j, Δ, lFn, kFn, paramsFn, lRet, kRet, ι,
              (named.map (·.1)).zip temps⟩
            let g ← mkFreshExprSyntheticOpaqueMVar (← callAllType Φ atoms₂ info (rc ++ cs))
            solveCallAll g.mvarId! Φ info paramsFn (rc ++ cs) atoms₂
            keepLeaf named g
            let mut vals := atoms₂.val
            for (k, _) in named do
              if k < vals.size then vals := vals.set! k (toExpr (0 : BitVec 64))
            return some (info, { atoms₂ with val := vals }))
          catch e =>
            trace[TypedAsm.fast] "call to a function that chooses ({kFn}, {kRet}): {e.toMessageData}"
            pure none
        st.restore
        if found.isSome then return found
    return none
  s.restore
  return r

/-- A call through a value found typed within a walk: a pointer to a
function, whose signature says what it is entered with and what it returns
with; the return point is a label's context at parameters. -/
structure ViaCall where
  at' : Nat
  next : Nat
  j : Nat
  R : Sym.CtxS
  Δ : Sym.CtxS
  τ : Sym.TyS
  R0 : Expr
  lRet : Name
  kRet : Name
  paramsR : Array Expr
  Δ0 : Expr
  temps : Array (Nat × Expr)

/-- What is to be shown where a block calls through a value. -/
def viaCallType (Φ : Expr) (atoms : Sym.Atoms) (c : ViaCall) (cs : List Sym.CondS) :
    MetaM Expr := do
  let mut allE := mkConst ``True
  for x in cs.reverse do
    allE := mkApp2 (mkConst ``And) (← Sym.denCond atoms x) allE
  let tyE := atoms.ty.getD c.j (mkConst ``Ty.int)
  let RE ← Sym.denCtx atoms c.R
  let ΔE ← Sym.denCtx atoms c.Δ
  let τE ← Sym.denTy atoms c.τ
  return mkApp2 (mkConst ``And) (mkApp2 (mkConst ``Ty.Enters) τE ΔE)
    (mkApp2 (mkConst ``And) (← mkEq tyE (← mkAppM ``Ty.code #[RE]))
      (mkApp2 (mkConst ``And) (mkAppN Φ #[toExpr (BitVec.ofNat 64 c.next), RE]) allE))

/-- That a type enters a context, for the context with its register types
as a table: from the proof for the context as it is written. -/
def entersTabled (τE Δ0 pf : Expr) (atoms : Sym.Atoms) (Δ : Sym.CtxS) : MetaM Expr := do
  let env ← getEnv
  let lctx ← getLCtx
  let P ← withLocalDeclD `X (mkConst ``Ctx) fun X => do
    mkLambdaFVars #[X] (mkApp2 (mkConst ``Ty.Enters) τE X)
  unless Kernel.isDefEqGuarded env lctx (← inferType pf) (mkApp2 (mkConst ``Ty.Enters) τE Δ0) do
    throwError "the value's type is not seen to enter the context chosen"
  let ΔE ← Sym.denCtx atoms Δ
  let want := mkApp2 (mkConst ``Ty.Enters) τE ΔE
  let tabled := mkApp3 (mkConst ``Ctx.asTable) P Δ0 pf
  unless Kernel.isDefEqGuarded env lctx (← inferType tabled) want do
    throwError "the context chosen is not the one compared"
  mkExpectedTypeHint tabled want

/-- Shows what `viaCallType` states. `Δ0` is the function's entry, written
with its signature, and the parameters are those of this scope. -/
def solveCallVia (g : MVarId) (Φ : Expr) (c : ViaCall) (R0 Δ0 : Expr)
    (paramsR : Array Expr) (cs : List Sym.CondS) (atoms : Sym.Atoms) : TacticM Unit :=
    g.withContext do
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  let goals ← getGoals
  let tyE := atoms.ty.getD c.j (mkConst ``Ty.int)
  let RE ← Sym.denCtx atoms c.R
  let ΔE ← Sym.denCtx atoms c.Δ
  let τE ← Sym.denTy atoms c.τ
  -- the type of the return address
  let A ← mkEq tyE (← mkAppM ``Ty.code #[RE])
  let P ← withLocalDeclD `X (mkConst ``Ctx) fun X => do
    mkLambdaFVars #[X] (← mkEq tyE (← mkAppM ``Ty.code #[X]))
  let h0 ← mkExpectedTypeHint (← mkEqRefl tyE) (mkApp P R0).headBeta
  let tabled := mkApp3 (mkConst ``Ctx.asTable) P R0 h0
  unless Kernel.isDefEqGuarded env lctx (← inferType tabled) A do
    throwError "the return point's context is not the one compared"
  let hA ← mkExpectedTypeHint tabled A
  -- the return point
  let (hR, premsR) ← labelProof Φ c.lRet c.kRet paramsR c.next c.R atoms
  for m in premsR do
    if ← m.isAssigned then continue
    let t ← instantiateMVars (← m.getType)
    if t.isAppOf ``FnSig.CallerOk then
      closeCallerOk m
    else
      let left ← runOn m do
        evalTactic (← `(tactic| first | assumption | omega | decide | ty_arith))
      unless left.isEmpty do throwError "left over"
  -- what is called: a function, whose requirement of its caller is met; or
  -- code wanting a context, which is that context
  let hEn ← (do
    if Δ0.isAppOfArity ``FnSig.entry 5 then
      let a := Δ0.getAppArgs
      let hK ← mkFreshExprSyntheticOpaqueMVar (mkAppN (mkConst ``FnSig.CallerOk) a)
      closeCallerOk hK.mvarId!
      entersTabled τE Δ0 (mkAppN (mkConst ``Ty.Enters.fn) (a.push (← instantiateMVars hK)))
        atoms c.Δ
    else entersTabled τE Δ0 (mkApp (mkConst ``Ty.Enters.code) Δ0) atoms c.Δ)
  let mut hn := mkConst ``True.intro
  let mut allE := mkConst ``True
  arithLeft.set #[]
  for x in cs.reverse do
    let leaf ← Sym.denCond atoms x
    let h ← closeNeeds env lctx kwhnf pure #[] leaf
    hn := mkApp4 (mkConst ``And.intro) leaf allE h hn
    allE := mkApp2 (mkConst ``And) leaf allE
  closeArithLeft
  let tR := mkAppN Φ #[toExpr (BitVec.ofNat 64 c.next), RE]
  let tE := mkApp2 (mkConst ``Ty.Enters) τE ΔE
  let inner := mkApp4 (mkConst ``And.intro) tR allE hR (← instantiateMVars hn)
  let mid := mkApp4 (mkConst ``And.intro) A (mkApp2 (mkConst ``And) tR allE) hA inner
  g.assign (mkApp4 (mkConst ``And.intro) tE
    (mkApp2 (mkConst ``And) A (mkApp2 (mkConst ``And) tR allE)) hEn mid)
  setGoals goals

/-- The signature of the function a type is that of a pointer to. -/
def fnSigOf (τE : Expr) : MetaM (Option Expr) := do
  if τE.isAppOfArity ``FnSig.ty 1 then return some τE.appArg!
  let w ← whnf τE
  if w.isAppOfArity ``Ty.fn 6 then return some (mkAppN (mkConst ``FnSig.mk) w.getAppArgs)
  return none

/-- Looks at a call through an operand that holds a pointer to a function,
returning to a label. The pointer's type says the signature; the registers
the function preserves, the caller's stack and its room are the caller's
own; and the return point is the context at the next label that what the
function returns with may stand for. -/
def findCallVia (Φ : Expr) (atoms : Sym.Atoms) (named : Array (Nat × Reg))
    (cur : Sym.CtxS) (at' next : Nat) (τ : Sym.TyS) (hc : List Sym.CondS) :
    TacticM (Option (ViaCall × Sym.Atoms)) := do
  let some (_, _, T, labels) ← labelInfo Φ | return none
  let some (_, lRet) := labels.find? (·.1 == next) | return none
  let .const tn _ := T.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? tn | return none
  let bv := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let decls := named.map fun (_, r) => (Name.mkSimple s!"{r.name64}₀", bv)
  let s ← saveState
  let r ← withLocalDeclsDND decls fun temps => do
    let mut atoms' := atoms
    for ((k, _), v) in named.zip temps do
      let pad := atoms'.val ++ Array.replicate (k + 1 - atoms'.val.size) (toExpr (0 : BitVec 64))
      atoms' := { atoms' with val := pad.set! k v }
    let τE ← Sym.denTy atoms' τ
    let sig? ← fnSigOf τE
    -- or a pointer to code wanting a context, which has the return address
    -- on its stack: that says where the code returns to
    let code? ← (do
      if sig?.isSome then return none
      let w ← if τE.isAppOfArity ``Ty.code 1 then pure τE else whnf τE
      unless w.isAppOfArity ``Ty.code 1 do return none
      let Δc := w.appArg!
      let some ΔcN ← normalCtx Δc | return none
      let stack ← whnf ΔcN.getAppArgs[2]!
      unless stack.isAppOfArity ``List.cons 3 do return none
      let some retTy := stack.getAppArgs[1]!.find? (·.isAppOfArity ``Ty.code 1) | return none
      return some (Δc, retTy) : TacticM (Option (Expr × Expr)))
    if sig?.isNone && code?.isNone then
      trace[TypedAsm.fast] "call through a value: its type is not that of a pointer to a \
        function, nor to code that returns"
      return none
    let j := atoms'.ty.size
    let some (pushed, rc) := Sym.afterCall cur j | return none
    let preE ← Sym.denCtx atoms' { pushed with stack := cur.stack }
    let pre := preE.getAppArgs
    let regsE := pre[1]!
    let stackE := pre[2]!
    let roomE := pre[3]!
    let ownedE := pre[5]!
    let aboveE := pre[6]!
    for kRet in info.ctors do
      let st ← saveState
      let found ← try (do
          let (paramsR, R0, Δ0, retTyE) ← (do
            match sig?, code? with
            | some sig, _ =>
              -- the return point: what the function returns with stands for it
              let ownedBack ← mkAppM ``HAppend.hAppend #[← mkAppM ``FnSig.gives #[sig],
                ← mkAppM ``List.drop
                  #[← mkAppM ``List.length #[← mkAppM ``FnSig.takes #[sig]], ownedE]]
              let returned ← mkAppM ``FnSig.returned
                #[sig, regsE, stackE, roomE, ownedBack, aboveE]
              let some retN ← normalCtx returned | throwError "not written out"
              let some (paramsR, R0) ← matchCtor kRet lRet retN | throwError "no such context"
              pure (paramsR, R0, mkAppN (mkConst ``FnSig.entry) #[sig, regsE, R0, stackE, roomE],
                ← mkAppM ``Ty.code #[R0])
            | none, some (Δc, retTy) =>
              -- the return point: the context the code's return address wants
              let R0 := retTy.appArg!
              let some RN ← normalCtx R0 | throwError "not written out"
              let some (paramsR, R1) ← matchCtor kRet lRet RN | throwError "no such context"
              unless ← isDefEq R1 R0 do throwError "the code returns into another context"
              pure (paramsR, R0, Δc, retTy)
            | none, none => throwError "not a pointer to code")
          if temps.any fun v => R0.containsFVar v.fvarId! then return none
          let atoms₁ := { atoms' with ty := atoms'.ty.push retTyE }
          let some RN ← normalCtx R0 | return none
          let some ΔN ← normalCtx Δ0 | return none
          let ((R?, Δ?), atoms₂) ← (do
            let R? ← Sym.reifyCtx RN
            let Δ? ← Sym.reifyCtx ΔN
            return (R?, Δ?) : Sym.ReifyM _).run atoms₁
          let (some R, some Δ) := (R?, Δ?) | return none
          let fresh := atoms₂.val.extract atoms₁.val.size atoms₂.val.size ++
            atoms₂.num.extract atoms₁.num.size atoms₂.num.size ++
            atoms₂.ty.extract atoms₁.ty.size atoms₂.ty.size ++
            atoms₂.shape.extract atoms₁.shape.size atoms₂.shape.size ++
            atoms₂.flags.extract atoms₁.flags.size atoms₂.flags.size ++
            atoms₂.stack.extract atoms₁.stack.size atoms₂.stack.size ++
            atoms₂.owned.extract atoms₁.owned.size atoms₂.owned.size
          if fresh.any fun e => temps.any fun v => e.containsFVar v.fvarId! then return none
          let sameAtom (tbl : Array Expr) (i? j? : Option Nat) : MetaM (Option Nat) := do
            let (some i, some j) := (i?, j?) | return j?
            if i == j then return j?
            let (some a, some b) := (tbl[i]?, tbl[j]?) | return j?
            if ← withoutModifyingState (isDefEq a b) then return some i
            return j?
          let Δ := { Δ with
            stackRest := ← sameAtom atoms₂.stack pushed.stackRest Δ.stackRest
            ownedRest := ← sameAtom atoms₂.owned pushed.ownedRest Δ.ownedRest }
          let some cs := Sym.subCtx pushed Δ
            | do trace[TypedAsm.fast] "call through a value: the contexts do not compare"
                 return none
          let all := hc ++ (rc ++ cs)
          let info : ViaCall := ⟨at', next, j, R, Δ, τ, R0, lRet, kRet, paramsR, Δ0,
            (named.map (·.1)).zip temps⟩
          let g ← mkFreshExprSyntheticOpaqueMVar (← viaCallType Φ atoms₂ info all)
          solveCallVia g.mvarId! Φ info R0 Δ0 paramsR all atoms₂
          keepLeaf named g
          let mut vals := atoms₂.val
          for (k, _) in named do
            if k < vals.size then vals := vals.set! k (toExpr (0 : BitVec 64))
          return some (info, { atoms₂ with val := vals }))
        catch e =>
          trace[TypedAsm.fast] "call through a value ({kRet}): {e.toMessageData}"
          pure none
      st.restore
      if found.isSome then return found
    return none
  s.restore
  return r

/-- A call through a value to a function that chooses a value as it
returns, found typed within a walk. -/
structure ViaCallAll where
  at' : Nat
  next : Nat
  j : Nat
  Δ : Sym.CtxS
  τ : Sym.TyS
  lRet : Name
  kRet : Name
  ι : Expr
  Δ0 : Expr
  temps : Array (Nat × Expr)

/-- What is to be shown where a block calls such a function through a value. -/
def viaCallAllType (Φ : Expr) (atoms : Sym.Atoms) (c : ViaCallAll) (cs : List Sym.CondS) :
    MetaM Expr := do
  let mut allE := mkConst ``True
  for x in cs.reverse do
    allE := mkApp2 (mkConst ``And) (← Sym.denCond atoms x) allE
  let tyE := atoms.ty.getD c.j (mkConst ``Ty.int)
  let seqTy ← mkArrow (mkConst ``Nat) (mkApp (mkConst ``BitVec) (mkNatLit 64))
  let preTy ← mkArrow seqTy (mkConst ``Ctx)
  let nextE := toExpr (BitVec.ofNat 64 c.next)
  let p ← withLocalDeclD `pre preTy fun pre => do
    let fam ← withLocalDeclD `x seqTy fun x => do
      mkForallFVars #[x] (mkAppN Φ #[nextE, mkApp pre x])
    mkLambdaFVars #[pre] (mkApp2 (mkConst ``And) (← mkEq tyE (← mkAppM ``Ty.codeAll #[pre])) fam)
  return mkApp2 (mkConst ``And)
    (mkApp2 (mkConst ``Ty.Enters) (← Sym.denTy atoms c.τ) (← Sym.denCtx atoms c.Δ))
    (mkApp2 (mkConst ``And) (mkApp2 (mkConst ``Exists [Level.one]) preTy p) allE)

/-- Shows what `viaCallAllType` states. `Δ0` is the function's entry, written
with its signature. -/
def solveCallViaAll (g : MVarId) (Φ : Expr) (c : ViaCallAll) (Δ0 : Expr)
    (cs : List Sym.CondS) (atoms : Sym.Atoms) : TacticM Unit := g.withContext do
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  let goals ← getGoals
  let goalTy ← viaCallAllType Φ atoms c cs
  let tyE := atoms.ty.getD c.j (mkConst ``Ty.int)
  unless tyE.isAppOfArity ``Ty.codeAll 1 do
    throwError "the return address is not typed for a family of contexts"
  let pre0 := tyE.appArg!
  let seqTy ← mkArrow (mkConst ``Nat) (mkApp (mkConst ``BitVec) (mkNatLit 64))
  let nextE := toExpr (BitVec.ofNat 64 c.next)
  let fam ← withLocalDeclD `x seqTy fun x => do
    let v ← mkAppOptM ``Chosen.dec #[some c.ι, none, some x]
    let (pf, _, prems) ← labelProofRaw Φ c.lRet c.kRet #[v] c.next
    unless prems.isEmpty do throwError "the return point's contexts demand something"
    let want := mkAppN Φ #[nextE, mkApp pre0 x]
    unless ← isDefEq (← inferType pf) want do
      throwError "the return point's contexts are not the family the function returns into"
    mkLambdaFVars #[x] (← mkExpectedTypeHint pf want)
  let ex := goalTy.appArg!.appFn!.appArg!
  let p := ex.appArg!
  let hEx := mkApp4 (mkConst ``Exists.intro [Level.one]) ex.appFn!.appArg! p pre0
    (← mkAppM ``And.intro #[← mkEqRefl tyE, fam])
  -- the function: its requirement of its caller is met
  unless Δ0.isAppOfArity ``FnSigEx.entry 9 do throwError "the function's entry is not written out"
  let a := Δ0.getAppArgs
  let hK ← mkFreshExprSyntheticOpaqueMVar
    (mkAppN (mkConst ``FnSigEx.CallerOk) #[a[0]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!, a[8]!])
  closeCallerOkEx hK.mvarId!
  let τE ← Sym.denTy atoms c.τ
  let hEn ← entersTabled τE Δ0
    (mkAppN (mkConst ``Ty.Enters.fnEx) (a.push (← instantiateMVars hK))) atoms c.Δ
  let mut hn := mkConst ``True.intro
  let mut allE := mkConst ``True
  arithLeft.set #[]
  for x in cs.reverse do
    let leaf ← Sym.denCond atoms x
    let h ← closeNeeds env lctx kwhnf pure #[] leaf
    hn := mkApp4 (mkConst ``And.intro) leaf allE h hn
    allE := mkApp2 (mkConst ``And) leaf allE
  closeArithLeft
  let tE := goalTy.appFn!.appArg!
  let inner := mkApp4 (mkConst ``And.intro) ex allE hEx (← instantiateMVars hn)
  g.assign (mkApp4 (mkConst ``And.intro) tE (mkApp2 (mkConst ``And) ex allE) hEn inner)
  setGoals goals

/-- Looks at a call through an operand that holds a pointer to a function
that chooses a value as it returns: the pointer's type says the signature,
and the label after the call has one context for each value. -/
def findCallViaAll (Φ : Expr) (atoms : Sym.Atoms) (named : Array (Nat × Reg))
    (cur : Sym.CtxS) (at' next : Nat) (τ : Sym.TyS) (hc : List Sym.CondS) :
    TacticM (Option (ViaCallAll × Sym.Atoms)) := do
  let some (_, _, T, labels) ← labelInfo Φ | return none
  let some (_, lRet) := labels.find? (·.1 == next) | return none
  let .const tn _ := T.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? tn | return none
  let bv := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let decls := named.map fun (_, r) => (Name.mkSimple s!"{r.name64}₀", bv)
  let s ← saveState
  let r ← withLocalDeclsDND decls fun temps => do
    let mut atoms' := atoms
    for ((k, _), v) in named.zip temps do
      let pad := atoms'.val ++ Array.replicate (k + 1 - atoms'.val.size) (toExpr (0 : BitVec 64))
      atoms' := { atoms' with val := pad.set! k v }
    let τE ← Sym.denTy atoms' τ
    unless τE.isAppOfArity ``FnSigEx.ty 3 do return none
    let ι := τE.getAppArgs[0]!
    let inst := τE.getAppArgs[1]!
    let sig := τE.getAppArgs[2]!
    let j := atoms'.ty.size
    let some (pushed, rc) := Sym.afterCall cur j | return none
    let preE ← Sym.denCtx atoms' { pushed with stack := cur.stack }
    let pre := preE.getAppArgs
    let regsE := pre[1]!
    let stackE := pre[2]!
    let roomE := pre[3]!
    let ownedE := pre[5]!
    let aboveE := pre[6]!
    for kRet in info.ctors do
      let st ← saveState
      let found ← try (do
          let fam? ← forallTelescope (← inferType (mkConst kRet)) fun xs body => do
            let args := body.getAppArgs
            if args.size < 2 || xs.size != 1 then return none
            unless args[args.size - 2]!.isConstOf lRet do return none
            unless ← isDefEq (← inferType xs[0]!) ι do return none
            return some (← mkLambdaFVars xs args[args.size - 1]!)
          let some retFam := fam? | return none
          let frame ← mkAppM ``List.drop
            #[← mkAppM ``List.length #[← mkAppM ``FnSigEx.takes #[sig]], ownedE]
          let Δ0 := mkAppN (mkConst ``FnSigEx.entry)
            #[ι, inst, sig, regsE, retFam, stackE, roomE, frame, aboveE]
          let some ΔN ← normalCtx Δ0 | return none
          let some codeAllE := ΔN.getAppArgs[2]!.find? (·.isAppOfArity ``Ty.codeAll 1)
            | return none
          let atoms₁ := { atoms' with ty := atoms'.ty.push codeAllE }
          let (Δ?, atoms₂) ← (Sym.reifyCtx ΔN).run atoms₁
          let some Δ := Δ? | return none
          let fresh := atoms₂.val.extract atoms₁.val.size atoms₂.val.size ++
            atoms₂.num.extract atoms₁.num.size atoms₂.num.size ++
            atoms₂.ty.extract atoms₁.ty.size atoms₂.ty.size ++
            atoms₂.shape.extract atoms₁.shape.size atoms₂.shape.size ++
            atoms₂.flags.extract atoms₁.flags.size atoms₂.flags.size ++
            atoms₂.stack.extract atoms₁.stack.size atoms₂.stack.size ++
            atoms₂.owned.extract atoms₁.owned.size atoms₂.owned.size
          if fresh.any fun e => temps.any fun v => e.containsFVar v.fvarId! then return none
          let sameAtom (tbl : Array Expr) (i? j? : Option Nat) : MetaM (Option Nat) := do
            let (some i, some j) := (i?, j?) | return j?
            if i == j then return j?
            let (some a, some b) := (tbl[i]?, tbl[j]?) | return j?
            if ← withoutModifyingState (isDefEq a b) then return some i
            return j?
          let Δ := { Δ with
            stackRest := ← sameAtom atoms₂.stack pushed.stackRest Δ.stackRest
            ownedRest := ← sameAtom atoms₂.owned pushed.ownedRest Δ.ownedRest }
          let some cs := Sym.subCtx pushed Δ
            | do trace[TypedAsm.fast] "call through a value: the contexts do not compare"
                 return none
          let all := hc ++ (rc ++ cs)
          let info : ViaCallAll := ⟨at', next, j, Δ, τ, lRet, kRet, ι, Δ0,
            (named.map (·.1)).zip temps⟩
          let g ← mkFreshExprSyntheticOpaqueMVar (← viaCallAllType Φ atoms₂ info all)
          solveCallViaAll g.mvarId! Φ info Δ0 all atoms₂
          keepLeaf named g
          let mut vals := atoms₂.val
          for (k, _) in named do
            if k < vals.size then vals := vals.set! k (toExpr (0 : BitVec 64))
          return some (info, { atoms₂ with val := vals }))
        catch e =>
          trace[TypedAsm.fast] "call through a value to a function that chooses ({kRet}): {e.toMessageData}"
          pure none
      st.restore
      if found.isSome then return found
    return none
  s.restore
  return r

/-- A jump through a value found typed within a walk: a pointer to code
wanting a context the one reached may stand for. -/
structure ViaJump where
  at' : Nat
  Δ : Sym.CtxS
  τ : Sym.TyS
  Δ0 : Expr
  /-- That the value's type enters `Δ0`, as that is written. -/
  pf : Expr

/-- What is to be shown where a block jumps through a value. -/
def viaJumpType (atoms : Sym.Atoms) (c : ViaJump) (cs : List Sym.CondS) : MetaM Expr := do
  let mut allE := mkConst ``True
  for x in cs.reverse do
    allE := mkApp2 (mkConst ``And) (← Sym.denCond atoms x) allE
  return mkApp2 (mkConst ``And)
    (mkApp2 (mkConst ``Ty.Enters) (← Sym.denTy atoms c.τ) (← Sym.denCtx atoms c.Δ)) allE

/-- Shows what `viaJumpType` states. -/
def solveJumpVia (g : MVarId) (c : ViaJump) (cs : List Sym.CondS) (atoms : Sym.Atoms) :
    TacticM Unit := g.withContext do
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  let goals ← getGoals
  let τE ← Sym.denTy atoms c.τ
  let hEn ← entersTabled τE c.Δ0 c.pf atoms c.Δ
  let mut hn := mkConst ``True.intro
  let mut allE := mkConst ``True
  arithLeft.set #[]
  for x in cs.reverse do
    let leaf ← Sym.denCond atoms x
    let h ← closeNeeds env lctx kwhnf pure #[] leaf
    hn := mkApp4 (mkConst ``And.intro) leaf allE h hn
    allE := mkApp2 (mkConst ``And) leaf allE
  closeArithLeft
  g.assign (mkApp4 (mkConst ``And.intro)
    (mkApp2 (mkConst ``Ty.Enters) τE (← Sym.denCtx atoms c.Δ)) allE hEn (← instantiateMVars hn))
  setGoals goals

/-- Looks at a jump through an operand that holds a pointer to code: the
context the code wants is the one the context reached is compared with. -/
def findJumpVia (atoms : Sym.Atoms) (named : Array (Nat × Reg)) (cur : Sym.CtxS) (at' : Nat)
    (τ : Sym.TyS) (hc : List Sym.CondS) (notCode? : Option (IO.Ref Bool) := none) :
    TacticM (Option (ViaJump × Sym.Atoms)) := do
  let bv := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let decls := named.map fun (_, r) => (Name.mkSimple s!"{r.name64}₀", bv)
  let s ← saveState
  let r ← withLocalDeclsDND decls fun temps => do
    let mut atoms' := atoms
    for ((k, _), v) in named.zip temps do
      let pad := atoms'.val ++ Array.replicate (k + 1 - atoms'.val.size) (toExpr (0 : BitVec 64))
      atoms' := { atoms' with val := pad.set! k v }
    try
      let τE ← Sym.denTy atoms' τ
      let w ← if τE.isAppOfArity ``Ty.code 1 then pure τE else whnf τE
      -- a pointer to code wanting a context; or a pointer to a function,
      -- jumped to on behalf of this code's own caller: a tail call, where
      -- the function asks no more of that caller than this code does
      let cands : Array (Expr × Expr) ← (do
        if w.isAppOfArity ``Ty.code 1 then
          return #[(w.appArg!, mkApp (mkConst ``Ty.Enters.code) w.appArg!)]
        let some sig ← fnSigOf τE | return #[]
        let mut out := #[]
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let t ← instantiateMVars d.type
          unless t.isAppOfArity ``FnSig.CallerOk 5 do continue
          let a := t.getAppArgs
          let args := #[sig, a[1]!, a[2]!, a[3]!, a[4]!]
          let want := mkAppN (mkConst ``FnSig.CallerOk) args
          let h := d.toExpr
          let hK? ← (do
            if ← isDefEq t want then return some h
            -- another signature that asks the same of the caller: what this
            -- code's caller was required to meet is what that one requires
            try
              let built := mkAppN (mkConst ``FnSig.CallerOk.mk) (args ++
                #[← mkAppM ``FnSig.CallerOk.gives #[h], ← mkAppM ``FnSig.CallerOk.ret #[h],
                  ← mkAppM ``FnSig.CallerOk.room #[h]])
              Meta.check built
              return some built
            catch _ => return none : MetaM (Option Expr))
          if let some hK := hK? then
            out := out.push (mkAppN (mkConst ``FnSig.entry) args,
              mkAppN (mkConst ``Ty.Enters.fn) (args.push hK))
        return out : TacticM (Array (Expr × Expr)))
      if cands.isEmpty then
        trace[TypedAsm.fast] "jump through a value: its type is not that of a pointer to code, \
          nor of a function this code's caller is ready for"
        if let some r := notCode? then r.set true
        return none
      let mut found : Option (ViaJump × Sym.Atoms) := none
      for (Δ0, pf) in cands do
        if found.isSome then break
        found ← (do
          let some ΔN ← normalCtx Δ0 | return none
          let (Δ?, atoms'') ← (Sym.reifyCtx ΔN).run atoms'
          let some Δ := Δ? | return none
          let sameAtom (tbl : Array Expr) (i? j? : Option Nat) : MetaM (Option Nat) := do
            let (some i, some j) := (i?, j?) | return j?
            if i == j then return j?
            let (some a, some b) := (tbl[i]?, tbl[j]?) | return j?
            if ← withoutModifyingState (isDefEq a b) then return some i
            return j?
          let Δ := { Δ with
            stackRest := ← sameAtom atoms''.stack cur.stackRest Δ.stackRest
            ownedRest := ← sameAtom atoms''.owned cur.ownedRest Δ.ownedRest }
          let some cs := Sym.subCtx cur Δ
            | do trace[TypedAsm.fast] "jump through a value: the contexts do not compare"
                 return none
          let info : ViaJump := ⟨at', Δ, τ, Δ0, pf⟩
          let g ← mkFreshExprSyntheticOpaqueMVar (← viaJumpType atoms'' info (hc ++ cs))
          solveJumpVia g.mvarId! info (hc ++ cs) atoms''
          keepLeaf named g
          let mut vals := atoms''.val
          for (k, _) in named do
            if k < vals.size then vals := vals.set! k (toExpr (0 : BitVec 64))
          return some (info, { atoms'' with val := vals }) : TacticM (Option (ViaJump × Sym.Atoms)))
      return found
    catch e =>
      trace[TypedAsm.fast] "jump through a value: {e.toMessageData}"
      pure none
  s.restore
  return r

/-- That what was read of the program's blocks is so: each by looking. -/
def blocksProof (Ψ ρ : Expr) (blocks : List (BitVec 64 × Sym.ShapeS × Bool))
    (lays : Array Expr) : MetaM Expr := do
  let mut hB := mkApp2 (mkConst ``Sym.BlocksOk.nil) Ψ ρ
  let mut restL : List (BitVec 64 × Sym.ShapeS × Bool) := []
  for ((base, Sb, w), lay) in (blocks.zip lays.toList).reverse do
    let h₁ ← mkEqRefl (← mkAppM ``Option.some #[lay])
    let h₂ ← mkEqRefl (← mkAppM ``Layout.shape #[lay])
    let h₃ ← mkEqRefl (toExpr w)
    hB := mkAppN (mkConst ``Sym.BlocksOk.cons)
      #[Ψ, ρ, toExpr base, toExpr Sb, toExpr w, toExpr restL, lay, h₁, h₂, h₃, hB]
    restL := (base, Sb, w) :: restL
  return hB

/-- Types the instruction in a `Straight Ψ next Γ i ?Γ'` goal by the checker:
the context is read as data, the checker gives the context after and what
is left to be shown, and that is shown. Where the checker has no answer, or
something left cannot be shown, the error says why, of the program. -/
def typeStraight : TacticM Unit := deep <| withMainContext do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``Straight 5 do
    throwError "ty_straight: the goal is not of the form `Straight Ψ next Γ i Γ'`"
  let args := ty.getAppArgs
  let Ψ := args[0]!
  let next := args[1]!
  let Γ := args[2]!
  let Γ' := args[4]!
  let some instr ← knownInstr args[3]!
    | throwError "ty_straight: the instruction is not written out: {args[3]!}"
  let shown := m!"`{instr.toAsm}`"
  let nextN ← try evalAddr next catch _ =>
    throwError "ty_straight: the address of the next instruction is not a number: {next}"
  let nextB := BitVec.ofNat 64 nextN
  let some ΓN ← normalCtx Γ | throwError "ty_straight: the context is not written out"
  let mut Ψ' := Ψ
  for _ in [0:4] do
    if Ψ'.isAppOfArity ``MemTy.ofList 2 then break
    let some u ← unfoldDefinition? Ψ' | break
    Ψ' := u.headBeta
  let listed := Ψ'.isAppOfArity ``MemTy.ofList 2
  let (read, atoms) ← (do
    let some S₀ ← Sym.reifyCtx ΓN | return none
    let blocks? ← if listed then Sym.reifyBlocks Ψ'.appFn!.appArg! else pure none
    return some (S₀, blocks?) : Sym.ReifyM _).run {}
  let some (S₀, blocks?) := read | throwError "ty_straight: the context could not be read"
  let (blocks, lays) := blocks?.getD ([], #[])
  let S : Sym.CtxS := { S₀ with blocks := blocks }
  let refuse (msg : MessageData) : TacticM Unit :=
    throwError "cannot type {shown} in the current context\n• {msg}"
  let some (S', cs) := Sym.step nextB S instr
    | match Sym.why nextB S instr with
      | .noForm => throwError "the type system has no rule for {shown}"
      | r => refuse (← explainReject atoms instr.onStack r)
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  let ρ := atoms.env
  let SE := toExpr S
  unless Kernel.isDefEqGuarded env lctx ΓN (mkApp2 (mkConst ``Sym.CtxS.den) ρ SE) do
    throwError "ty_straight: the term read from the context does not mean it"
  -- what is left to be shown, each by itself so that the one that fails is known
  let mut hn := mkConst ``True.intro
  let mut allE := mkConst ``True
  for c in cs.reverse do
    let leaf ← Sym.denCond atoms c
    let before ← saveState
    let h ← try
        arithLeft.set #[]
        let h ← closeNeeds env lctx kwhnf pure #[] leaf
        closeArithLeft
        pure h
      catch _ =>
        before.restore
        refuse (← explainCond atoms instr c)
        unreachable!
    hn := mkApp4 (mkConst ``And.intro) leaf allE (← instantiateMVars h) hn
    allE := mkApp2 (mkConst ``And) leaf allE
  let hB ← blocksProof Ψ ρ blocks lays
  let iE := toExpr instr
  let nextE := toExpr nextB
  let x := toExpr (S', cs)
  let stepE := mkAppN (mkConst ``Sym.step) #[nextE, SE, iE]
  let h ← mkExpectedTypeHint (← mkEqRefl stepE) (← mkEq stepE (← mkAppM ``Option.some #[x]))
  let Γ'E ← Sym.denCtx atoms S'
  let pf ← mkExpectedTypeHint
    (mkAppN (mkConst ``Sym.step_sound) #[Ψ, nextE, ρ, SE, hB, iE, x, h, hn])
    (mkAppN (mkConst ``Straight) #[Ψ, next, ΓN, args[3]!, Γ'E])
  let others := (← getGoals).drop 1
  if Γ'.isMVar then
    -- the context after is the checker's answer
    Γ'.mvarId!.assign Γ'E
    goal.assign (mkAppN (mkConst ``Straight.regsEta) #[Ψ, next, Γ, Γ'E, args[3]!, pf])
  else
    -- a context after that is stated must be the checker's answer
    let same ← (do
      let some Γ'N ← normalCtx Γ' | return false
      return Kernel.isDefEqGuarded env lctx Γ'N Γ'E)
    unless same do
      throwError "ty_straight: `{instr.toAsm}` leaves the context{indentExpr Γ'E}\nand not the \
        one stated"
    goal.assign (mkAppN (mkConst ``Straight.regsEta) #[Ψ, next, Γ, Γ', args[3]!,
      mkAppN (mkConst ``Straight.regsEtaAfter) #[Ψ, next, ΓN, Γ', args[3]!, pf]])
  setGoals others

/-- Types the instruction in a `Straight` goal by the checker. When it is
refused, the error names the instruction and says why. -/
elab "ty_straight" : tactic => typeStraight

set_option maxHeartbeats 1000000 in
/-- One instruction that goes on to the next, typed without the tactic
framework where the checker covers it: the instruction is read from the
program's table, the checker is run by the kernel's evaluator, and of the
context it gives only what changed is tidied. The proof is put together
directly and checked by the kernel with the rest. Returns the goal for the
rest of the block, or nothing where this does not apply, and then the step is
taken the long way. -/
partial def fastStep (goal : MVarId) (ty : Expr) (named : Bool) :
    TacticM (Option (List MVarId)) :=
    goal.withContext do
  unless ty.isAppOfArity ``BlockOk 6 do return none
  if ty.hasExprMVar then return none
  let args := ty.getAppArgs
  let Φ := args[0]!
  let fetch := args[1]!
  let sys := args[2]!
  let Ψ := args[3]!
  let a := args[4]!
  let Γ := args[5]!
  unless isAddrLit a do return none
  let some n := a.appArg!.nat? | return none
  unless Γ.isAppOfArity ``CtxOf.mk 7 do return none
  let cargs := Γ.getAppArgs
  let regs := cargs[1]!
  unless regs.isAppOfArity ``RegMap.get 2 && regs.appArg!.isAppOfArity ``RegMap.mk 17 do
    return none
  let tbl := regs.appArg!.getAppArgs
  let some instrs ← instrsOf fetch | return none
  let some (instr, len) := instrs[n]? | return none
  -- an instruction that ends a block is one the walk may end at
  if instr.endsBlock && !(instr matches .jmp _) && !(instr matches .jcc _ _) &&
      !(instr matches .ret) && !(instr matches .call _) && !(instr matches .syscall) then
    return none
  let typeOf (r : Reg) : MetaM Expr := whnf tbl[1 + regIdx r]!
  let iE := toExpr instr
  let lenE := toExpr len
  let next ← mkAppM ``HAdd.hAdd #[a, lenE]
  let nextLit := toExpr (BitVec.ofNat 64 (n + len.toNat))
  -- with the program's blocks at hand where the memory typing is a list of them
  let mut Ψ' := Ψ
  for _ in [0:4] do
    if Ψ'.isAppOfArity ``MemTy.ofList 2 then break
    let some u ← unfoldDefinition? Ψ' | break
    Ψ' := u.headBeta
  let listed := Ψ'.isAppOfArity ``MemTy.ofList 2
  let env ← getEnv
  let lctx ← getLCtx
  let kwhnf (e : Expr) : MetaM Expr := ofExceptKernelException (Kernel.whnf env lctx e)
  -- First the checker that works on the context as data. It is run here, on
  -- the term read from the context, and what it gives is what the kernel is
  -- asked to confirm: that the term means this context, and that the checker
  -- comes to that answer.
  let symStep : TacticM (Option (List MVarId)) := do
    -- The context the last run left is the one this one starts from, as a
    -- rule: its term is kept, with what its variables stand for, and is not
    -- read again. It is used only if all it mentions is still in scope.
    leafProofs.set #[]
    let kept? : Option (Sym.CtxS × Sym.Atoms) ← (do
      let some (Γc, Sc, ac) ← symKept.get | return none
      unless Γc == Γ do return none
      let inScope (e : Expr) : Bool :=
        !e.hasFVar || (e.find? fun x => x.isFVar && !lctx.contains x.fvarId!).isNone
      unless (ac.val ++ ac.num ++ ac.ty ++ ac.shape ++ ac.flags ++ ac.stack ++ ac.owned).all inScope
        && ac.tyNames.all (inScope ·.2) && ac.shapeNames.all (inScope ·.2) do return none
      return some (Sc, ac))
    -- Where the block is being walked to its end, the checker is run on from
    -- instruction to instruction for as long as it has an answer and nothing
    -- else is to be done first: a label to hand over to, a value to name, a
    -- pointer to open. The kernel then confirms the whole run at once.
    let stops? ← runStops.get
    let needsBlocks (i : Instr) : Bool := listed && (match i.memOperand? with
      | some (.rip _) | some (.sib none _ _) => true
      | _ => false)
    -- whether something is to be done before an instruction that is not the first
    let waits (S : Sym.CtxS) (i : Instr) (at' next' : Nat) : Bool :=
      i.endsBlock || (stops?.getD #[]).contains next' || (stops?.getD #[]).contains at' ||
      (match i with
        | .movzx _ _ .w8 (.mem (.sib (some b) none _)) =>
          (match S.regs.get b with
            | .str _ => true
            | _ => false)
        | _ => false)
    -- an operating system that returns from the calls Linux returns from, as
    -- Linux does: system calls that return are then stepped over in the walk
    let linux? : Option Expr ← (do
      try pure (some (← synthInstance (mkApp (mkConst ``LikeLinux) sys)))
      catch _ => pure none)
    -- the same but for `write`: the other calls are stepped over then too
    let linuxNW? : Option Expr ← (do
      try pure (some (← synthInstance (mkApp (mkConst ``LikeLinuxNW) sys)))
      catch _ => pure none)
    -- Where what the program writes is being shown: the system underneath,
    -- that it is like Linux, and the condition.
    let offers? : Option (Expr × Expr × Expr) ← (do
      let sysE := sys.consumeMData
      unless sysE.isAppOfArity ``Syscall.writesOnly 2 do return none
      let sys₀ := sysE.getAppArgs[0]!
      try
        let inst ← synthInstance (mkApp (mkConst ``LikeLinux) sys₀)
        return some (sys₀, inst, sysE.getAppArgs[1]!)
      catch _ => return none)
    -- addresses of code a register was made a pointer to, each with the
    -- variable that is the pointer's type
    let codesRef : IO.Ref (Array (BitVec 64 × Nat)) ← IO.mkRef #[]
    -- where each `write` typed for what it offers is, in the order met
    let offerAts : IO.Ref (Array Nat) ← IO.mkRef #[]
    let offersSeen : IO.Ref Nat ← IO.mkRef 0
    let ((result, prog?), atoms) ← (do
      let some S₀ ← (match kept? with
        | some (Sc, _) => pure (some Sc)
        | none => Sym.reifyCtx Γ) | return (Sum.inl (none, none), none)
      -- The program's blocks and kinds are read where the walk may need
      -- them: a pointer to a block of a kind is held, or an instruction ahead
      -- reaches data by where it is or takes its address.
      let ahead : Bool := Id.run do
        let mut at' := n
        for _ in [0:256] do
          let some (i, len') := instrs[at']? | return false
          if needsBlocks i || (i matches .lea .w64 _ (.rip _)) then return true
          if i.endsBlock then return false
          at' := at' + len'.toNat
        return false
      -- a pointer to a block of a kind, or what may be a block's address
      -- kept as a number, which is made a pointer where it is reached through
      let held := allRegs.any fun r =>
        (match S₀.regs.get r with
          | .ref .. => true
          | .eq (.lit v) => decide (0x1000 ≤ v.toNat)
          | _ => false)
      let kind? ← mmapKindRef.get
      let prog? ← if listed && (ahead || held || kind?.isSome) then
          Sym.reifyProg Ψ'.appFn!.appArg! Ψ'.appArg!
        else pure none
      let prog? := prog?.map fun (Pr, lays, tagLays) => ({ Pr with mmapKind := kind? }, lays, tagLays)
      -- Where what the program writes is being shown, the address of a block
      -- that says its bytes is kept as the number it is: that is what says
      -- which bytes a `write` from there offers.
      let prog? ← match prog? with
        | some (Pr, lays, tagLays) =>
          if sys.isAppOf ``Syscall.writesOnly then
            let mut keep : List (BitVec 64) := []
            for ((base, _, _), lay) in Pr.blocks.zip lays.toList do
              let l ← whnf lay
              if l.isAppOfArity ``Layout.mk 5 then
                if (← whnf l.getAppArgs[4]!).isAppOf ``Option.some then keep := keep ++ [base]
            pure (some ({ Pr with keep := keep }, lays, tagLays))
          else pure (some (Pr, lays, tagLays))
        | none => pure none
      let P : Sym.Prog := (prog?.map (·.1)).getD {}
      let mut cur := S₀
      let mut at' := n
      let mut moves : Array WalkMove := #[]
      -- the context each instruction of the walk was come to with
      let mut arrived := S₀
      let mut steps := 0
      let mut refused : Option (Nat × Instr × Array WalkMove × Sym.Reject) := none
      -- whether the walk has gone past the instruction it started at
      let mut advanced := false
      let mut k := (← get).val.size
      -- The instruction before a label with contexts of its own is gone
      -- through, to see whether the block can be handed over there: how the
      -- walk stood before it, and then also the context it left.
      let mut tailMark : Option (Nat × Nat × Sym.CtxS) := none
      let mut tail? : Option (Nat × Nat × Sym.CtxS × Sym.CtxS) := none
      let known ← labelsKnown.get
      let limit := (← stepLimit.get).getD (if stops?.isSome then 4096 else 1)
      for _ in [0:8192] do
        if steps ≥ limit then break
        let some (i, len') := instrs[at']? | break
        let next' := at' + len'.toNat
        -- a forward jump to an address with no context of its own is
        -- followed: what it jumps to is typed in the context it is made in
        if let .jmp (.rel d) := i then
          let t := (BitVec.ofNat 64 at' + len' + d.signExtend 64).toNat
          let some stops := stops? | break
          unless ← labelsKnown.get do break
          if advanced && stops.contains at' then break
          unless at' < t && !stops.contains t do
            -- back to a label with no context of its own: refused, since
            -- what is jumped back to must say what holds each time round
            if !stops.contains t && moves.isEmpty then
              if let some (_, _, _, labels) ← labelInfo Φ then
                let name := match labels.find? (·.1 == t) with
                  | some (_, l) => m!"label `{l.components.getLast!}`"
                  | none => m!"address {t}"
                refusal.set (some m!"no context is declared at {name}: a label that is jumped \
                  back to, called, or returned to must say what holds there")
            break
          moves := moves.push (.jump at' i len')
          at' := t
          advanced := true
          continue
        -- a conditional jump forward to an address with no context of its
        -- own: both sides are typed where they are, and the walk ends in them
        if let .jcc _ d := i then
          let t := (BitVec.ofNat 64 at' + len' + d.signExtend 64).toNat
          let some stops := stops? | break
          unless ← labelsKnown.get do break
          if advanced && stops.contains at' then break
          unless at' < t && !stops.contains t do break
          moves := moves.push (.split at' i len')
          break
        -- a system call that returns is a step like any other
        if let .syscall := i then
          if linuxNW?.isNone then break
          if advanced && (stops?.getD #[]).contains at' then break
          -- an `mmap` for memory the program is to own: the walk ends in what
          -- follows it, twice
          if (Sym.mmapAt { P with linux := true } k (BitVec.ofNat 64 next') cur i).isSome then
            if stops?.isNone then break
            moves := moves.push (.split at' i len')
            break
          -- a `write` where what the program writes is being shown: typed
          -- for what it offers
          if offers?.isSome &&
              (Sym.offerAt { P with offers := true } cur i).isSome then
            moves := moves.push (.jump at' i len')
            offerAts.modify (·.push at')
            advanced := true
            cur := cur.afterSyscall
            arrived := cur
            at' := next'
            continue
          -- a `munmap` of part of an owned block: the block is regarded as
          -- two first
          if let some Γs := Sym.unmapSplit cur i then
            moves := moves.push .opened
            cur := Γs
            continue
          -- an `mmap` being tried as a new block of a declared kind
          if let some tag := P.mmapKind then
            if let some (S', cs) := Sym.sysMmapKind P cur tag then
              moves := moves.push (.step at' i len' arrived cs)
              steps := steps + 1
              advanced := true
              cur := S'
              arrived := cur
              at' := next'
              continue
          let some (S', cs) := Sym.stepSys cur linux?.isSome | do
            if (Sym.exitAt cur i).isSome then break
            -- refused: why, where it is the first thing asked of the walk
            -- (a `write` where what the program writes is being shown is
            -- spoken of where its offer is looked for)
            let nr? := match cur.regs.get .rax with
              | .eq (.lit nr) => some nr.toNat
              | _ => none
            let name := ((bufferCalls.find? (some ·.1 == nr?)).map (·.2.1)).getD "syscall"
            if moves.isEmpty && !(nr? == some 1 && linux?.isNone) then
              refusal.set (some (← explainSys (← get) name (Sym.whySys cur)))
            trace[TypedAsm.fast] "system call not stepped: rax {toExpr (cur.regs.get .rax)}, rsi {
              toExpr (cur.regs.get .rsi)}, rdx {toExpr (cur.regs.get .rdx)}, owned {toExpr cur.owned}"
            break
          moves := moves.push (.step at' i len' arrived cs)
          steps := steps + 1
          advanced := true
          cur := S'
          arrived := cur
          at' := next'
          continue
        let into := known && stops?.isSome && (stops?.getD #[]).contains next' &&
          !i.endsBlock && !(advanced && (stops?.getD #[]).contains at') &&
          !(Sym.toByte cur i).isSome &&
          (match tailMark with
            | none => true
            | some (_, a, _) => a == at')
        if advanced && waits cur i at' next' && !into then break
        if into && tailMark.isNone then tailMark := some (moves.size, at', arrived)
        -- a value that may be null, or what a system call handed back, is
        -- about to be tested: the block goes on once for each thing it may be
        if let some (_, _, isErr) := Sym.toSplit cur i then
          if stops?.isNone then break
          if isErr && !cur.under k then break
          moves := moves.push (.split at' i len')
          break
        -- a byte of text is loaded: zero, or not, and the text goes on
        if (Sym.toByte cur i).isSome then
          if stops?.isNone then break
          unless cur.under k do break
          moves := moves.push (.split at' i len')
          break
        -- a pointer to a block of a kind that is reached through is opened
        if let some (r, tag, w, off) := Sym.toOpen cur i then
          let some Sk := Sym.lookupNat P.kinds tag | break
          if r == .rsp then break
          moves := moves.push .opened
          cur := cur.setReg r (.ptr Sk w off)
          continue
        -- a value the instruction needs to speak of is named
        if let some r := Sym.toName cur i then
          unless cur.under k && Sym.blocksUnder k P.blocks && Sym.kindsUnder k P.kinds do break
          moves := moves.push (.name k r)
          cur := cur.setReg r (.eq (.var k))
          k := k + 1
          continue
        -- the address of a label where code is typed makes the register a
        -- pointer to that code, or to the function there; the address of
        -- anything else that is not data is left to the long way
        let mut codeH? : Option (Reg × Nat) := none
        if let .lea .w64 d (.rip disp) := i then
          let v := BitVec.ofNat 64 at' + len' + disp.signExtend 64
          if (Sym.blockAt P.blocks v).isNone then
            if d == .rsp then break
            let some τE ← codeTypeAt Φ v.toNat | break
            let st ← get
            let h ← match st.ty.findIdx? (· == τE) with
              | some h => pure h
              | none => do set { st with ty := st.ty.push τE }; pure st.ty.size
            codesRef.modify fun cs => if cs.any (·.1 == v) then cs else cs.push (v, h)
            codeH? := some (d, h)
        let some (S', cs) :=
          Sym.step (BitVec.ofNat 64 at' + len') { cur with blocks := P.blocks } i | do
            -- refused, and the first instruction asked of the walk: why
            -- (an instruction that ends the block is no step: its ending is
            -- looked for instead)
            unless advanced || i.endsBlock do
              refused := some (at', i, moves,
                Sym.why (BitVec.ofNat 64 at' + len') { cur with blocks := P.blocks } i)
            break
        moves := moves.push (.step at' i len' arrived cs)
        steps := steps + 1
        advanced := true
        cur := match codeH? with
          | some (d, h) => S'.setReg d (.atom h)
          | none => Sym.castData P S' i
        if let some (ms, a, before) := tailMark then
          if a == at' then
            tail? := some (ms, a, before, S')
            arrived := cur
            at' := next'
            break
        arrived := cur
        at' := next'
      -- what was done toward an instruction not then stepped over is not done
      for _ in [0:moves.size] do
        match moves.back? with
        | some (.step ..) => break
        | some (.split ..) => break
        | some (.jump ..) => break
        | some _ => moves := moves.pop
        | none => break
      if moves.isEmpty then return (Sum.inl (refused, some S₀), prog?)
      return (Sum.inr (S₀, moves, at', arrived, tail?), prog?) : Sym.ReifyM _).run ((kept?.map (·.2)).getD {})
    -- values the walk would have named are spoken of by the names they would have had
    let withNames (atoms : Sym.Atoms) (moves : Array WalkMove) : Sym.Atoms := Id.run do
      let mut a := atoms
      for mv in moves do
        if let .name k r := mv then
          let pad := a.val ++ Array.replicate (k + 1 - a.val.size) (toExpr (0 : BitVec 64))
          a := { a with val := pad.set! k (mkConst (Name.mkSimple s!"{r.name64}₀")) }
      return a
    -- How a context reached is made ready to be compared with one wanted,
    -- as the checker makes it: an exactly known block address a pointer
    -- where a pointer is wanted, and the blocks owned in the order wanted.
    let ready (Γc Δc : Sym.CtxS) : Option Sym.CtxS :=
      let cast? := Sym.castWanted ((prog?.map (·.1)).getD {}) Δc Sym.regList Γc false
      match Sym.reorder Δc (cast?.getD Γc) with
      | some Γr => some Γr
      | none => cast?
    -- A jump to a label with contexts of its own, where a walk would end:
    -- the block is handed over there within the walk, if a context allowed
    -- there is found that the one reached may stand for.
    let jumpEnter (atoms : Sym.Atoms) (moves : Array WalkMove) (at' : Nat) (cur : Sym.CtxS) :
        TacticM (Option (EnterInfo × Sym.Atoms × WalkMove)) := do
      let some stops := stops? | return none
      unless ← labelsKnown.get do return none
      let some (i, len') := instrs[at']? | return none
      let .jmp (.rel d) := i | return none
      let t := (BitVec.ofNat 64 at' + len' + d.signExtend 64).toNat
      unless stops.contains t do return none
      let named := moves.filterMap fun
        | .name k r => some (k, r)
        | _ => none
      castRef.set (some ready)
      let why ← IO.mkRef #[]
      let found ← try findEnter Φ atoms named cur at' t (why? := some why)
        finally castRef.set none
      let some (info, atoms') := found
        | do
          -- no context declared there is one to hand over to: why not, of each
          let some (_, _, _, labels) ← labelInfo Φ | return none
          let some (_, lName) := labels.find? (·.1 == t) | return none
          let mut reasons : MessageData := m!""
          for r in ← why.get do reasons := reasons ++ m!"\n• {r}"
          refusal.set (some m!"no context allowed at label `{lName.components.getLast!}` \
            accepts the current one{reasons}")
          return none
      return some (info, atoms', .jump at' i len')
    -- A conditional jump to a label with contexts of its own: the side that
    -- jumps is handed over there, and the other is handed over at the next
    -- instruction if that is at such a label too, the block otherwise going on.
    let branchEnter (atoms : Sym.Atoms) (moves : Array WalkMove) (at' : Nat) (cur : Sym.CtxS) :
        TacticM (Option (Array EnterInfo × Sym.Atoms × WalkMove)) := do
      let some stops := stops? | return none
      unless ← labelsKnown.get do return none
      let some (i, len') := instrs[at']? | return none
      let .jcc c d := i | return none
      let t := (BitVec.ofNat 64 at' + len' + d.signExtend 64).toNat
      unless stops.contains t do
        trace[TypedAsm.fast] "`{i.toAsm}` at {at'}: not to a label with contexts of its own"
        return none
      let named := moves.filterMap fun
        | .name k r => some (k, r)
        | _ => none
      castRef.set (some ready)
      castCtx.set none
      let found ← try findEnter Φ atoms named cur at' t (some (cur.flags, c, true))
        finally castRef.set none
      let some (taken, atoms₁) := found | return none
      -- the other side is compared with the context as it was made ready
      let cur := (← castCtx.get).getD cur
      let next' := at' + len'.toNat
      if stops.contains next' && next' != t then
        if let some (fall, atoms₂) ← findEnter Φ atoms₁ named cur at' next'
            (some (cur.flags, c, false)) then
          return some (#[taken, fall], atoms₂, .split at' i len')
      return some (#[taken], atoms₁, .split at' i len')
    -- A return: typed within the walk where the context the code returned
    -- to wants is one the context the return leaves may stand for.
    let retLeave (atoms : Sym.Atoms) (moves : Array WalkMove) (at' : Nat) (cur : Sym.CtxS) :
        TacticM (Option (LeaveInfo × Sym.Atoms × WalkMove)) := do
      if stops?.isNone then return none
      let some (i, len') := instrs[at']? | return none
      unless i matches .ret do return none
      let named := moves.filterMap fun
        | .name k r => some (k, r)
        | _ => none
      castRef.set (some ready)
      let why ← IO.mkRef none
      let found ← try findLeave atoms named cur at' (some why) finally castRef.set none
      if found.isNone then
        if let some m ← why.get then refusal.set (some m)
      let some (info, atoms') := found | return none
      return some (info, atoms', .jump at' i len')
    -- A call to a labelled function, returning to a label.
    let callEnter (atoms : Sym.Atoms) (moves : Array WalkMove) (at' : Nat) (cur : Sym.CtxS) :
        TacticM (Option (CallInfo × Sym.Atoms × WalkMove)) := do
      let some stops := stops? | return none
      unless ← labelsKnown.get do return none
      let some (i, len') := instrs[at']? | return none
      let .call (.rel d) := i | return none
      let t := (BitVec.ofNat 64 at' + len' + d.signExtend 64).toNat
      let next' := at' + len'.toNat
      unless stops.contains t && stops.contains next' do return none
      let named := moves.filterMap fun
        | .name k r => some (k, r)
        | _ => none
      castRef.set (some ready)
      let found ← try findCall Φ atoms named cur at' t next' finally castRef.set none
      let some (info, atoms') := found | return none
      return some (info, atoms', .jump at' i len')
    -- A call to a labelled function that chooses a value as it returns.
    let callAllEnter (atoms : Sym.Atoms) (moves : Array WalkMove) (at' : Nat) (cur : Sym.CtxS) :
        TacticM (Option (CallAll × Sym.Atoms × WalkMove)) := do
      let some stops := stops? | return none
      unless ← labelsKnown.get do return none
      let some (i, len') := instrs[at']? | return none
      let .call (.rel d) := i | return none
      let t := (BitVec.ofNat 64 at' + len' + d.signExtend 64).toNat
      let next' := at' + len'.toNat
      unless stops.contains t && stops.contains next' do return none
      let named := moves.filterMap fun
        | .name k r => some (k, r)
        | _ => none
      let some (info, atoms') ← findCallAll Φ atoms named cur at' t next' | return none
      return some (info, atoms', .jump at' i len')
    -- A call or a jump through an operand that holds a pointer to a function
    -- or to code.
    let named' (moves : Array WalkMove) := moves.filterMap fun
      | .name k r => some (k, r)
      | _ => none
    let viaCall (atoms : Sym.Atoms) (moves : Array WalkMove) (at' : Nat) (cur : Sym.CtxS) :
        TacticM (Option (ViaCall × Sym.Atoms × WalkMove)) := do
      let some stops := stops? | return none
      unless ← labelsKnown.get do return none
      let some (i, len') := instrs[at']? | return none
      let .call (.ind rm) := i | return none
      let next' := at' + len'.toNat
      unless stops.contains next' do
        trace[TypedAsm.fast] "`{i.toAsm}`: it does not return to a label with contexts of its own"
        return none
      let some (τ, hc) := Sym.held (BitVec.ofNat 64 next')
          { cur with blocks := (prog?.map fun x => x.1.blocks).getD [] } rm
        | do trace[TypedAsm.fast] "`{i.toAsm}`: what the operand holds is not read"; return none
      let some (info, atoms') ← findCallVia Φ atoms (named' moves) cur at' next' τ hc
        | return none
      return some (info, atoms', .jump at' i len')
    let viaCallAll (atoms : Sym.Atoms) (moves : Array WalkMove) (at' : Nat) (cur : Sym.CtxS) :
        TacticM (Option (ViaCallAll × Sym.Atoms × WalkMove)) := do
      let some stops := stops? | return none
      unless ← labelsKnown.get do return none
      let some (i, len') := instrs[at']? | return none
      let .call (.ind rm) := i | return none
      let next' := at' + len'.toNat
      unless stops.contains next' do return none
      let some (τ, hc) := Sym.held (BitVec.ofNat 64 next')
          { cur with blocks := (prog?.map fun x => x.1.blocks).getD [] } rm | return none
      let some (info, atoms') ← findCallViaAll Φ atoms (named' moves) cur at' next' τ hc
        | return none
      return some (info, atoms', .jump at' i len')
    let viaJump (atoms : Sym.Atoms) (moves : Array WalkMove) (at' : Nat) (cur : Sym.CtxS) :
        TacticM (Option (ViaJump × Sym.Atoms × WalkMove)) := do
      if stops?.isNone then return none
      let some (i, len') := instrs[at']? | return none
      let .jmp (.ind rm) := i | return none
      let some (τ, hc) := Sym.held (BitVec.ofNat 64 (at' + len'.toNat))
          { cur with blocks := (prog?.map fun x => x.1.blocks).getD [] } rm
        | do trace[TypedAsm.fast] "`{i.toAsm}`: what the operand holds is not read"; return none
      let notCode ← IO.mkRef false
      let some (info, atoms') ← findJumpVia atoms (named' moves) cur at' τ hc (some notCode)
        | do
          if ← notCode.get then
            refusal.set (some m!"`{i.toAsm}`: the operand does not hold a pointer to code here. \
              Control would go to whatever number it holds: a general-protection fault where \
              the processor has no such address, a page fault where there is no code. A \
              register holding the exact address of a label becomes a pointer to code with \
              `ty_fn_ptr` (a function) or `ty_code_ptr` (any other label)")
          return none
      return some (info, atoms', .jump at' i len')
    -- When a call ends the program, for the system the block is typed
    -- against: any status, or one exactly known and as wanted.
    let sysE := sys.consumeMData
    let isLinux (e : Expr) := e.consumeMData.isConstOf ``linux
    let (endsE, hEnds, wantQ?) : Expr × Expr × Option Expr :=
      if isLinux sysE then (mkConst ``ExitAny, mkConst ``linux_endsWhen, none)
      else if sysE.isAppOfArity ``Syscall.exitsOnly 2 && isLinux sysE.getAppArgs[0]! then
        let Q := sysE.getAppArgs[1]!
        (mkApp (mkConst ``ExitAs) Q, mkApp (mkConst ``linux_endsWhen_only) Q, some Q)
      else if sysE.isAppOfArity ``Syscall.writesOnly 2 && isLinux sysE.getAppArgs[0]! then
        (mkConst ``ExitAny, mkApp (mkConst ``linux_endsWhen_writes) sysE.getAppArgs[1]!, none)
      else if sysE.isAppOfArity ``Syscall.writesOnly 2 &&
          sysE.getAppArgs[0]!.consumeMData.isAppOfArity ``Syscall.exitsOnly 2 &&
          isLinux sysE.getAppArgs[0]!.consumeMData.getAppArgs[0]! then
        let Q := sysE.getAppArgs[0]!.consumeMData.getAppArgs[1]!
        (mkApp (mkConst ``ExitAs) Q,
          mkApp2 (mkConst ``linux_endsWhen_only_writes) Q sysE.getAppArgs[1]!, some Q)
      else (mkConst ``ExitNever, mkApp (mkConst ``Syscall.endsWhen_never) sys, none)
    let endsKnown := !endsE.isConstOf ``ExitNever
    let (wrE, hWrE) : Expr × Expr := match offers? with
      | some (sys₀, inst, R) =>
        (mkApp2 (mkConst ``Sym.Offered.ok) Ψ R, mkApp4 (mkConst ``Sym.offersOk) sys₀ inst R Ψ)
      | none =>
        let wr := mkLambda `fd .default (mkApp (mkConst ``BitVec) (mkNatLit 64))
          (mkLambda `o .default (mkConst ``Sym.Offered) (mkConst ``False))
        (wr, mkApp3 (mkConst ``Sym.offersNone) sys Ψ wr)
    -- A call that ends the program: the walk ends there. Where the status
    -- is to be as wanted and is not exactly known, the call is refused.
    let exitEnd (at' : Nat) (cur : Sym.CtxS) : TacticM (Option WalkMove) := do
      unless endsKnown do return none
      let some (i, len') := instrs[at']? | return none
      let some (.exit v) := Sym.exitAt cur i | return none
      if wantQ?.isSome && v.isNone then
        -- refused: the status is to be as wanted, and is not exactly known
        let actual ← try ppTy (← Sym.denTy atoms (cur.regs.get .rdi)) catch _ => pure "not known"
        refusal.set (some m!"`syscall`: what the program ends with is being shown, so the \
          status in `rdi` must be exactly known here, but its type is `{actual}`")
        return none
      return some (.jump at' i len')
    -- the first variable a name may take: the table may grow past it later
    let k₀ := atoms.val.size
    let mut atoms := atoms
    let mut enters : Array EnterInfo := #[]
    let mut leave? : Option LeaveInfo := none
    let mut call? : Option CallInfo := none
    let mut via? : Option ViaCall := none
    let mut callAll? : Option CallAll := none
    let mut viaAll? : Option ViaCallAll := none
    let mut jvia? : Option ViaJump := none
    let (S₀, moves, atEnd, arrived) ← match result with
      | .inr (S₀, moves, atEnd, arrived, some (ms, ai, before, raw)) =>
        -- the walk ran into a label: handed over there if a context is found
        let named := moves.filterMap fun
          | .name k r => some (k, r)
          | _ => none
        match ← findEnter Φ atoms named raw ai atEnd with
        | some (info, atoms') =>
          atoms := atoms'
          enters := enters.push info
          pure (S₀, moves, atEnd, arrived)
        | none =>
          -- not handed over: the walk stops before that instruction, as it
          -- would have, unless it is all there is of it
          if ms == 0 then
            if ← intoOnly.get then return none
            pure (S₀, moves, atEnd, arrived)
          else pure (S₀, moves.extract 0 ms, ai, before)
      | .inr (S₀, moves, atEnd, arrived, none) =>
        match ← jumpEnter atoms moves atEnd arrived with
        | some (info, atoms', mv) =>
          atoms := atoms'
          enters := enters.push info
          pure (S₀, moves.push mv, atEnd, arrived)
        | none =>
          match ← branchEnter atoms moves atEnd arrived with
          | some (infos, atoms', mv) =>
            atoms := atoms'
            enters := enters ++ infos
            pure (S₀, moves.push mv, atEnd, arrived)
          | none =>
            match ← retLeave atoms moves atEnd arrived with
            | some (info, atoms', mv) =>
              atoms := atoms'
              leave? := some info
              pure (S₀, moves.push mv, atEnd, arrived)
            | none =>
              match ← callEnter atoms moves atEnd arrived with
              | some (info, atoms', mv) =>
                atoms := atoms'
                call? := some info
                pure (S₀, moves.push mv, atEnd, arrived)
              | none =>
                match ← callAllEnter atoms moves atEnd arrived with
                | some (info, atoms', mv) =>
                  atoms := atoms'
                  callAll? := some info
                  pure (S₀, moves.push mv, atEnd, arrived)
                | none =>
                match ← viaCall atoms moves atEnd arrived with
                | some (info, atoms', mv) =>
                  atoms := atoms'
                  via? := some info
                  pure (S₀, moves.push mv, atEnd, arrived)
                | none =>
                  match ← viaCallAll atoms moves atEnd arrived with
                  | some (info, atoms', mv) =>
                    atoms := atoms'
                    viaAll? := some info
                    pure (S₀, moves.push mv, atEnd, arrived)
                  | none =>
                  match ← viaJump atoms moves atEnd arrived with
                  | some (info, atoms', mv) =>
                    atoms := atoms'
                    jvia? := some info
                    pure (S₀, moves.push mv, atEnd, arrived)
                  | none =>
                    match ← exitEnd atEnd arrived with
                    | some mv => pure (S₀, moves.push mv, atEnd, arrived)
                    | none => pure (S₀, moves, atEnd, arrived)
      | .inl (none, none) => return none
      | .inl (none, some S₀) | .inl (some (_, _, _, .noForm), some S₀) =>
        -- the block may be nothing but its ending: a jump that hands it
        -- over, a return, a call, or a call that ends the program
        match ← jumpEnter atoms #[] n S₀ with
        | some (info, atoms', mv) =>
          atoms := atoms'
          enters := enters.push info
          pure (S₀, #[mv], n, S₀)
        | none =>
        match ← branchEnter atoms #[] n S₀ with
        | some (infos, atoms', mv) =>
          atoms := atoms'
          enters := enters ++ infos
          pure (S₀, #[mv], n, S₀)
        | none =>
        match ← retLeave atoms #[] n S₀ with
        | some (info, atoms', mv) =>
          atoms := atoms'
          leave? := some info
          pure (S₀, #[mv], n, S₀)
        | none =>
        match ← callEnter atoms #[] n S₀ with
        | some (info, atoms', mv) =>
          atoms := atoms'
          call? := some info
          pure (S₀, #[mv], n, S₀)
        | none =>
        match ← callAllEnter atoms #[] n S₀ with
        | some (info, atoms', mv) =>
          atoms := atoms'
          callAll? := some info
          pure (S₀, #[mv], n, S₀)
        | none =>
        match ← viaCall atoms #[] n S₀ with
        | some (info, atoms', mv) =>
          atoms := atoms'
          via? := some info
          pure (S₀, #[mv], n, S₀)
        | none =>
        match ← viaCallAll atoms #[] n S₀ with
        | some (info, atoms', mv) =>
          atoms := atoms'
          viaAll? := some info
          pure (S₀, #[mv], n, S₀)
        | none =>
        match ← viaJump atoms #[] n S₀ with
        | some (info, atoms', mv) =>
          atoms := atoms'
          jvia? := some info
          pure (S₀, #[mv], n, S₀)
        | none =>
        match ← exitEnd n S₀ with
        | some mv => pure (S₀, #[mv], n, S₀)
        | none => return none
      | .inl (some (_, _, _, .noForm), none) => return none
      | .inl (some (at', i, tried, why), _) =>
        let msg ← explainReject (withNames atoms tried) i.onStack why
        refusal.set (some m!"at address {at'}: cannot type `{i.toAsm}` in the current context\n• {msg}")
        throwError "refused"
    let P : Sym.Prog := { (prog?.map (·.1)).getD {} with
      labels := ((stops?.getD #[]).map (BitVec.ofNat 64)).toList
      enters := (enters.toList.map fun e => (BitVec.ofNat 64 e.at', BitVec.ofNat 64 e.t, e.Δ)) ++
        (jvia?.toList.map fun e => (BitVec.ofNat 64 e.at', 0, e.Δ))
      leaves := leave?.toList.map fun e => (BitVec.ofNat 64 e.at', e.Δ)
      calls := (call?.toList.map fun e => (BitVec.ofNat 64 e.at', e.j, e.R, e.Δ)) ++
        (via?.toList.map fun e => (BitVec.ofNat 64 e.at', e.j, e.R, e.Δ))
      linux := linuxNW?.isSome
      plainWrite := linux?.isSome
      offers := offers?.isSome
      codes := (← codesRef.get).toList
      callsAll := (callAll?.toList.map fun e => (BitVec.ofNat 64 e.at', e.j, e.Δ)) ++
        (viaAll?.toList.map fun e => (BitVec.ofNat 64 e.at', e.j, e.Δ)) }
    let S := { S₀ with blocks := [] }
    -- the context at the end: the walk again, as the checker makes it
    let code : List (BitVec 64 × Instr × BitVec 64) :=
      moves.toList.filterMap fun
        | .step at' i len' _ _ => some (BitVec.ofNat 64 at', i, len')
        | .split at' i len' => some (BitVec.ofNat 64 at', i, len')
        | .jump at' i len' => some (BitVec.ofNat 64 at', i, len')
        | _ => none
    let W := Sym.walk P code (Sym.walkFuel code.length) k₀ (BitVec.ofNat 64 n) S
    let rec final : Sym.Walk → Option Sym.CtxS
      | .stop _ Γ => some Γ
      | .conds _ rest => final rest
      | .name _ rest => final rest
      | .both _ _ => none
      | .err _ _ _ => none
      | .byte _ _ _ => none
      | .branch _ _ _ _ => none
      | .enter _ _ _ => none
      | .leave _ _ _ => none
      | .call .. => none
      | .exit _ => none
      | .fresh _ _ _ => none
      | .jumpVia .. => none
      | .callVia .. => none
      | .callAll .. => none
      | .callViaAll .. => none
      | .offer _ _ rest => final rest
      | .asCode _ _ rest => final rest
    let rec enters? : Sym.Walk → Bool
      | .enter _ _ _ => true
      | .leave _ _ _ => true
      | .call .. => true
      | .exit _ => false
      | .jumpVia .. => true
      | .callVia .. => true
      | .callAll .. => true
      | .callViaAll .. => true
      | .offer _ _ rest => enters? rest
      | .asCode _ _ rest => enters? rest
      | .fresh _ l r => enters? l || enters? r
      | .conds _ rest => enters? rest
      | .name _ rest => enters? rest
      | .both l r => enters? l || enters? r
      | .err _ l r => enters? l || enters? r
      | .byte _ l r => enters? l || enters? r
      | .branch _ _ l r => enters? l || enters? r
      | .stop _ _ => false
    -- a hand-over the checker did not make as it was found leaves the jump
    -- where it was, and is not tried again in this block
    if (!enters.isEmpty || leave?.isSome || call?.isSome || via?.isSome || jvia?.isSome ||
        callAll?.isSome || viaAll?.isSome) &&
        !enters? W then
      trace[TypedAsm.fast] "the checker did not hand the block over as found"
      refusal.set (some disagreement)
      throwError "the block was not handed over as found"
    let rec exits? : Sym.Walk → Bool
      | .exit _ => true
      | .conds _ rest => exits? rest
      | .name _ rest => exits? rest
      | .both l r => exits? l || exits? r
      | .err _ l r => exits? l || exits? r
      | .byte _ l r => exits? l || exits? r
      | .fresh _ l r => exits? l || exits? r
      | .asCode _ _ rest => exits? rest
      | .offer _ _ rest => exits? rest
      | .branch _ _ l r => exits? l || exits? r
      | _ => false
    let S'? := final W
    let ρ := atoms.env
    let SE := toExpr S
    -- that what was read of the program is so: each part by looking
    let mut hB := mkApp2 (mkConst ``Sym.BlocksOk.nil) Ψ ρ
    let mut hT := mkConst ``True.intro
    let mut hK := mkConst ``True.intro
    if let some (Pr, lays, tagLays) := prog? then
      let mut restL : List (BitVec 64 × Sym.ShapeS × Bool) := []
      for ((base, Sb, w), lay) in (Pr.blocks.zip lays.toList).reverse do
        let h₁ ← mkEqRefl (← mkAppM ``Option.some #[lay])
        let h₂ ← mkEqRefl (← mkAppM ``Layout.shape #[lay])
        let h₃ ← mkEqRefl (toExpr w)
        hB := mkAppN (mkConst ``Sym.BlocksOk.cons)
          #[Ψ, ρ, toExpr base, toExpr Sb, toExpr w, toExpr restL, lay, h₁, h₂, h₃, hB]
        restL := (base, Sb, w) :: restL
      let mut restT : List (BitVec 64 × Nat) := []
      for ((base, t), lay) in (Pr.tags.zip tagLays.toList).reverse do
        let h₁ ← mkEqRefl (← mkAppM ``Option.some #[lay])
        let h₂ ← mkEqRefl (← mkAppM ``Option.some #[mkNatLit t])
        hT := mkAppN (mkConst ``Sym.TagsOk.cons)
          #[Ψ, toExpr base, mkNatLit t, toExpr restT, lay, h₁, h₂, hT]
        restT := (base, t) :: restT
      let mut restK : List (Nat × Sym.ShapeS) := []
      for (t, Sk) in Pr.kinds.reverse do
        let lhs := mkApp2 (mkConst ``MemTy.kinds) Ψ (mkNatLit t)
        let rhs ← mkAppM ``Option.some #[mkApp2 (mkConst ``Sym.ShapeS.den) ρ (toExpr Sk)]
        let h ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs)
        hK := mkApp4 (mkConst ``And.intro) (← mkEq lhs rhs)
          (mkApp3 (mkConst ``Sym.KindsOk) Ψ ρ (toExpr restK)) h hK
        restK := (t, Sk) :: restK
    if kept?.isNone then
      unless Kernel.isDefEqGuarded env lctx Γ (mkApp2 (mkConst ``Sym.CtxS.den) ρ SE) do
        trace[TypedAsm.fast] "the term read from the context does not mean it"
        return none
    -- the instructions of the walk, and that they are the program's
    let codeE := toExpr code
    let mut hcode := mkConst ``True.intro
    let mut restCode : List (BitVec 64 × Instr × BitVec 64) := []
    for (at', i, len') in code.reverse do
      let lhs := mkApp fetch (toExpr at')
      let found := toExpr (some (i, len'))
      let hf ← fetchProof lhs found
      hcode := mkApp4 (mkConst ``And.intro) (← mkEq lhs found)
        (mkApp2 (mkConst ``Sym.Agrees) fetch (toExpr restCode)) hf hcode
      restCode := (at', i, len') :: restCode
    -- That the walk's conditions hold: the tree is gone down, each name a
    -- value brought in, each step's conditions shown where they stand, and at
    -- the end the block where the walk stopped, left as the goal.
    let aEnd := toExpr (BitVec.ofNat 64 atEnd)
    let bv := mkApp (mkConst ``BitVec) (mkNatLit 64)
    let outerInsts ← getLocalInstances
    let restRef : IO.Ref (Array (Expr × Array Name)) ← IO.mkRef #[]
    -- the instruction each group of conditions in the walk comes from: a
    -- step, or a conditional jump (whose condition the flags must decide)
    let condMoves := (moves.toList.zipIdx).filterMap fun (mv, idx) =>
      match mv with
      | .step at' i _ _ _ => some ((at', i), idx)
      | .split at' i _ => if i matches .jcc _ _ then some ((at', i), idx) else none
      | _ => none
    let condInstrs := (condMoves.map (·.1)).toArray
    let condMoveIdx := (condMoves.map (·.2)).toArray
    let condsSeen : IO.Ref Nat ← IO.mkRef 0
    -- where the block is handed over: what `sideType` states, shown
    let enterLeaf (atoms : Sym.Atoms) (t : BitVec 64) (Δ : Sym.CtxS) (cs : List Sym.CondS)
        (branch? : Option (Sym.FlagsS × Cond × Bool)) : TacticM Expr := do
      let some info := enters.find? (·.t == t.toNat)
        | throwError "the block is handed over where no context was chosen"
      -- the parameters, with the walk's names for the values they speak of
      let temps := info.temps.map (·.2)
      let reals := info.temps.map fun (k, _) => atoms.val.getD k (toExpr (0 : BitVec 64))
      let params := info.params.map (·.replaceFVars temps reals)
      let leafTy ← sideType Φ atoms t.toNat Δ cs branch?
      if let some pf ← keptLeaf? leafTy then return pf
      let m ← mkFreshExprSyntheticOpaqueMVar leafTy
      try solveSide m.mvarId! branch? Φ info.lName info.kName params t.toNat Δ cs atoms
      catch e =>
        trace[TypedAsm.fast] "handing over failed where it was found to succeed: {e.toMessageData}"
        refusal.set (some disagreement)
        throw e
      trace[TypedAsm.fast] "handed over within the walk at `{info.lName.components.getLast!}`"
      instantiateMVars m
    let rec down (W : Sym.Walk) (atoms : Sym.Atoms) (vs : Array Expr) (names : Array Name) :
        TacticM Expr := do
      match W with
      | .stop a' Γ' =>
        let Γ'E ← Sym.denCtx atoms Γ'
        let allTy ← mkForallFVars vs (mkAppN ty.getAppFn #[Φ, fetch, sys, Ψ, toExpr a', Γ'E])
        let m ← withLCtx lctx outerInsts <|
          mkFreshExprSyntheticOpaqueMVar allTy (← goal.getTag)
        restRef.modify (·.push (m, names))
        return mkAppN m vs
      | .conds cs rest =>
        let mut hn := mkConst ``True.intro
        let mut allE := mkConst ``True
        -- which instruction of the walk left these
        let nth ← condsSeen.modifyGet fun j => (j, j + 1)
        let before ← saveState
        try
          arithLeft.set #[]
          for c in cs.reverse do
            let leaf ← Sym.denCond atoms c
            let h ← closeNeeds (← getEnv) (← getLCtx) kwhnf pure #[] leaf
            hn := mkApp4 (mkConst ``And.intro) leaf allE h hn
            allE := mkApp2 (mkConst ``And) leaf allE
          closeArithLeft
        catch _ =>
          before.restore
          -- which of them could not be shown
          let some (at', i) := condInstrs[nth]? | throwError "left over"
          -- a system call is left to be told of the long way
          let sysCall := i matches .syscall
          let stepsBefore := (moves.toList.take (condMoveIdx[nth]?.getD 0)).countP
            fun | .step .. => true | _ => false
          if stepsBefore > 0 then
            -- the walk up to this instruction is taken first, by itself
            stepLimit.set (some stepsBefore)
            throwError "left over"
          if sysCall then throwError "left over"
          for c in cs do
            let ok ← (do
              let s ← saveState
              try
                arithLeft.set #[]
                discard <| closeNeeds (← getEnv) (← getLCtx) kwhnf pure #[] (← Sym.denCond atoms c)
                closeArithLeft
                s.restore
                pure true
              catch _ => s.restore; pure false)
            unless ok do
              let msg ← explainCond atoms i c
              refusal.set (some m!"at address {at'}: cannot type `{i.toAsm}` in the current context\n• {msg}")
              throwError "refused"
          throwError "left over"
        let hrest ← down rest atoms vs names
        mkAppM ``And.intro #[← instantiateMVars hn, hrest]
      | .name k rest =>
        let r := (moves.toList.findSome? fun
          | .name k' r => if k' == k then some r else none
          | _ => none).getD .rax
        let name := Name.mkSimple s!"{r.name64}₀"
        withLocalDeclD name bv fun v => do
          let pad := atoms.val ++ Array.replicate (k + 1 - atoms.val.size) (toExpr (0 : BitVec 64))
          let atoms' := { atoms with val := pad.set! k v }
          let body ← down rest atoms' (vs.push v) (names.push name)
          mkLambdaFVars #[v] (← instantiateMVars body)
      | .both l r =>
        mkAppM ``And.intro #[← down l atoms vs names, ← down r atoms vs names]
      | .err k l r =>
        let hl ← withLocalDeclD `e bv fun v => do
          withLocalDeclD `herr (mkApp (mkConst ``SysErr) v) fun hv => do
            let pad := atoms.val ++ Array.replicate (k + 1 - atoms.val.size) (toExpr (0 : BitVec 64))
            let atoms' := { atoms with val := pad.set! k v }
            let body ← down l atoms' ((vs.push v).push hv) ((names.push `e).push `herr)
            mkLambdaFVars #[v, hv] (← instantiateMVars body)
        mkAppM ``And.intro #[hl, ← down r atoms vs names]
      | .branch fl c taken fall =>
        -- each side is left as it stands, to be taken up with what the
        -- flags say of the condition as its first hypotheses
        let side (child : Sym.Walk) (b : Bool) : TacticM Expr := do
          -- a side on which the block is handed over is settled here
          if let .enter t Δ cs := child then return ← enterLeaf atoms t Δ cs (some (fl, c, b))
          let .stop a' Γ' := child | throwError "a branch's side is not where the walk stopped"
          let Γ'E ← Sym.denCtx atoms Γ'
          let P ← Sym.denFlags atoms fl
          let goalTy ← withLocalDeclD `f (mkConst ``Flags) fun f => do
            let hyp := (mkApp P f).headBeta
            let ev ← mkEq (← mkAppM ``Cond.eval #[f, toExpr c]) (← mkAppM ``Option.some #[toExpr b])
            mkForallFVars #[f] (← mkArrow hyp (← mkArrow ev
              (mkAppN ty.getAppFn #[Φ, fetch, sys, Ψ, toExpr a', Γ'E])))
          let m ← withLCtx lctx outerInsts <|
            mkFreshExprSyntheticOpaqueMVar (← mkForallFVars vs goalTy) (← goal.getTag)
          restRef.modify (·.push (m, names))
          return mkAppN m vs
        -- the side that carries on comes first among the goals
        let hFall ← side fall false
        let hTaken ← side taken true
        mkAppM ``And.intro #[hTaken, hFall]
      | .enter t Δ cs => enterLeaf atoms t Δ cs none
      | .call _ _ _ _ _ cs =>
        let some info := call? | throwError "the block calls where no contexts were chosen"
        let temps := info.temps.map (·.2)
        let reals := info.temps.map fun (k, _) => atoms.val.getD k (toExpr (0 : BitVec 64))
        let inst (e : Expr) := e.replaceFVars temps reals
        let leafTy ← callType Φ atoms info cs
        if let some pf ← keptLeaf? leafTy then return pf
        let m ← mkFreshExprSyntheticOpaqueMVar leafTy
        try
          solveCall m.mvarId! Φ info (inst info.R0) (info.paramsR.map inst)
            (info.paramsFn.map inst) cs atoms
        catch e =>
          trace[TypedAsm.fast] "calling failed where it was found to succeed: {e.toMessageData}"
          refusal.set (some disagreement)
          throw e
        trace[TypedAsm.fast] "called within the walk"
        instantiateMVars m
      | .fresh k l r =>
        let pad := atoms.val ++ Array.replicate (k + 1 - atoms.val.size) (toExpr (0 : BitVec 64))
        let hl ← withLocalDeclD `e bv fun v => do
          withLocalDeclD `herr (mkApp (mkConst ``SysErr) v) fun hv => do
            let atoms' := { atoms with val := pad.set! k v }
            let body ← down l atoms' ((vs.push v).push hv) ((names.push `e).push `herr)
            mkLambdaFVars #[v, hv] (← instantiateMVars body)
        let hr ← withLocalDeclD `p bv fun v => do
          let page ← mkEq (← mkAppM ``HMod.hMod #[← mkAppM ``BitVec.toNat #[v], mkNatLit 4096])
            (mkNatLit 0)
          withLocalDeclD `hpage page fun h₁ => do
            withLocalDeclD `hlow (← mkAppM ``LT.lt #[v, toExpr (0x800000000000 : BitVec 64)])
                fun h₂ => do
              let atoms' := { atoms with val := pad.set! k v }
              let body ← down r atoms' (((vs.push v).push h₁).push h₂)
                (((names.push `p).push `hpage).push `hlow)
              mkLambdaFVars #[v, h₁, h₂] (← instantiateMVars body)
        mkAppM ``And.intro #[hl, hr]
      | .asCode v h rest =>
        let some τE := atoms.ty[h]? | throwError "the pointer's type is not known"
        let m ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Sym.CodeAt) Φ (toExpr v) τE)
        let left ← try runOn m.mvarId! (do evalTactic (← `(tactic| ty_code_at)))
          catch e =>
            trace[TypedAsm.fast] "the address {v} is not shown to be that of the code: {e.toMessageData}"
            refusal.set (some disagreement)
            throw e
        unless left.isEmpty do
          refusal.set (some disagreement)
          throwError "the address is not shown to be that of the code"
        mkAppM ``And.intro #[← instantiateMVars m, ← down rest atoms vs names]
      | .offer fd o rest =>
        let some (_, _, R) := offers? | throwError "a `write` is typed for what it offers \
          where what the program writes is not being shown"
        let fdE ← Sym.denVal atoms fd
        let oE ← match o with
          | .said base off n =>
            pure (mkApp3 (mkConst ``Sym.Offered.said) (toExpr base) (mkNatLit off) (mkNatLit n))
          | .fields vs n => do
            let vsE ← mkListLit bv (← vs.mapM fun v => (Sym.denVal atoms v : MetaM Expr))
            pure (mkApp2 (mkConst ``Sym.Offered.fields) vsE (mkNatLit n))
        let m ← mkFreshExprSyntheticOpaqueMVar (mkApp4 (mkConst ``Sym.Offered.ok) Ψ R fdE oE)
        let closeR : TSyntax `tactic ← `(tactic| first
          | decide | decide +kernel | rfl | (simp; done) | (simp [asm_fact, *]; done))
        let left ← try
            runOn m.mvarId! (do
              match o with
              | .said .. =>
                evalTactic (← `(tactic|
                  refine ⟨_, _, by first | exact rfl | decide, by first | exact rfl | decide,
                    by decide, ?_⟩))
              | .fields .. => evalTactic (← `(tactic| dsimp only [Sym.Offered.ok]))
              evalTactic closeR)
          catch e =>
            trace[TypedAsm.fast] "write: what is offered is not shown to be as wanted: {e.toMessageData}"
            pure [m.mvarId!]
        let nth ← offersSeen.modifyGet fun j => (j, j + 1)
        unless left.isEmpty do
          -- what was offered, and what of it could not be shown
          let where' := ((← offerAts.get)[nth]?).getD 0
          let fdS ← (match fd with
            | .lit v => pure (toString v.toNat)
            | _ => ppClean fdE)
          let (what, cond?) ← (do
            match o with
            | .said base off n =>
              -- that part of what the block says, written out
              let cond? ← (do
                try
                  let lay ← whnf (mkApp2 (mkConst ``MemTy.blocks) Ψ (toExpr base))
                  unless lay.isAppOfArity ``Option.some 2 do return none
                  let said ← whnf (← mkAppM ``Layout.said #[lay.appArg!])
                  unless said.isAppOfArity ``Option.some 2 do return none
                  -- the bytes one by one, each as it is written
                  let mut l ← whnf said.appArg!
                  let mut elems : Array Expr := #[]
                  for _ in [0:65536] do
                    unless l.isAppOfArity ``List.cons 3 do break
                    elems := elems.push l.getAppArgs[1]!
                    l ← whnf l.getAppArgs[2]!
                  let part ← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 8))
                    (elems.extract off (off + n)).toList
                  return some (mkApp2 R fdE part).headBeta
                catch _ => return none : TacticM (Option Expr))
              pure (m!"{n} bytes from byte {off} of the block that says its bytes at address {base.toNat}",
                cond?)
            | .fields vs n =>
              let lits := vs.filterMap fun | .lit v => some v | _ => none
              if lits.length == vs.length then
                let bytes := (lits.flatMap le64).take n
                pure (m!"the {n} bytes {bytes.map (·.toNat)}, of values it stored",
                  some (mkApp2 R fdE (toExpr bytes)).headBeta)
              else pure (m!"the first {n} bytes of values it stored", none))
          let condS ← match cond? with
            | some c => pure m!"\n• what is wanted of them does not hold, or is not shown to: {← ppClean c}"
            | none => pure m!""
          refusal.set (some m!"at address {where'}: `write`: what the program offers is not shown \
            to be what is wanted\n• it offers descriptor {fdS} {what}{condS}")
          throwError "refused"
        trace[TypedAsm.fast] "a `write` typed for what it offers, within the walk"
        mkAppM ``And.intro #[← instantiateMVars m, ← down rest atoms vs names]
      | .callViaAll _ _ _ _ cs =>
        let some info := viaAll? | throwError "the block calls where no contexts were chosen"
        let temps := info.temps.map (·.2)
        let reals := info.temps.map fun (k, _) => atoms.val.getD k (toExpr (0 : BitVec 64))
        let inst (e : Expr) := e.replaceFVars temps reals
        let leafTy ← viaCallAllType Φ atoms info cs
        if let some pf ← keptLeaf? leafTy then return pf
        let m ← mkFreshExprSyntheticOpaqueMVar leafTy
        try solveCallViaAll m.mvarId! Φ info (inst info.Δ0) cs atoms
        catch e =>
          trace[TypedAsm.fast] "calling failed where it was found to succeed: {e.toMessageData}"
          refusal.set (some disagreement)
          throw e
        trace[TypedAsm.fast] "called a function that chooses through a value, within the walk"
        instantiateMVars m
      | .callAll _ _ _ _ cs =>
        let some info := callAll? | throwError "the block calls where no contexts were chosen"
        let temps := info.temps.map (·.2)
        let reals := info.temps.map fun (k, _) => atoms.val.getD k (toExpr (0 : BitVec 64))
        let inst (e : Expr) := e.replaceFVars temps reals
        let leafTy ← callAllType Φ atoms info cs
        if let some pf ← keptLeaf? leafTy then return pf
        let m ← mkFreshExprSyntheticOpaqueMVar leafTy
        try solveCallAll m.mvarId! Φ info (info.paramsFn.map inst) cs atoms
        catch e =>
          trace[TypedAsm.fast] "calling failed where it was found to succeed: {e.toMessageData}"
          refusal.set (some disagreement)
          throw e
        trace[TypedAsm.fast] "called a function that chooses within the walk"
        instantiateMVars m
      | .jumpVia _ _ cs =>
        let some info := jvia? | throwError "the block jumps where no context was read"
        let leafTy ← viaJumpType atoms info cs
        if let some pf ← keptLeaf? leafTy then return pf
        let m ← mkFreshExprSyntheticOpaqueMVar leafTy
        try solveJumpVia m.mvarId! info cs atoms
        catch e =>
          trace[TypedAsm.fast] "jumping failed where it was found to succeed: {e.toMessageData}"
          refusal.set (some disagreement)
          throw e
        trace[TypedAsm.fast] "jumped through a value within the walk"
        instantiateMVars m
      | .callVia _ _ _ _ _ cs =>
        let some info := via? | throwError "the block calls where no contexts were chosen"
        let temps := info.temps.map (·.2)
        let reals := info.temps.map fun (k, _) => atoms.val.getD k (toExpr (0 : BitVec 64))
        let inst (e : Expr) := e.replaceFVars temps reals
        let leafTy ← viaCallType Φ atoms info cs
        if let some pf ← keptLeaf? leafTy then return pf
        let m ← mkFreshExprSyntheticOpaqueMVar leafTy
        try
          solveCallVia m.mvarId! Φ info (inst info.R0) (inst info.Δ0) (info.paramsR.map inst) cs
            atoms
        catch e =>
          trace[TypedAsm.fast] "calling failed where it was found to succeed: {e.toMessageData}"
          refusal.set (some disagreement)
          throw e
        trace[TypedAsm.fast] "called through a value within the walk"
        instantiateMVars m
      | .exit v =>
        match wantQ?, v with
        | none, _ => pure (mkConst ``True.intro)
        | some _, none => throwError "the status the program ends with is not exactly known"
        | some Q, some V =>
          -- the status as the walk's names have it, and that it is as wanted
          let val ← Sym.denVal atoms V
          let want := (mkApp Q (← mkAppM ``BitVec.setWidth #[mkNatLit 32, val])).headBeta
          let m ← mkFreshExprSyntheticOpaqueMVar want
          let left ← try
              runOn m.mvarId! (do evalTactic (← `(tactic|
                first | (dsimp only; decide) | decide | rfl | (dsimp only; ty_arith) | ty_arith)))
            catch _ => pure [m.mvarId!]
          unless left.isEmpty do
            trace[TypedAsm.fast] "the status is not shown to be as wanted within the walk"
            refusal.set (some m!"`syscall`: the program would end here with a status that is \
              not shown to be as wanted: `{← ppClean want}` is needed")
            throwError "the status is not shown to be as wanted"
          trace[TypedAsm.fast] "ended within the walk"
          let some' ← mkAppM ``Option.some #[val]
          let pred ← withLocalDeclD `v bv fun x => do
            mkLambdaFVars #[x] (mkAnd (← mkEq some' (← mkAppM ``Option.some #[x]))
              (mkApp Q (← mkAppM ``BitVec.setWidth #[mkNatLit 32, x])))
          return mkApp4 (mkConst ``Exists.intro [1]) bv pred val
            (← mkAppM ``And.intro #[← mkEqRefl some', ← instantiateMVars m])
      | .leave i Δ cs =>
        let some info := leave? | throwError "the block returns where no context was read"
        let leafTy ← leaveType atoms i Δ cs
        if let some pf ← keptLeaf? leafTy then return pf
        let m ← mkFreshExprSyntheticOpaqueMVar leafTy
        let temps := info.temps.map (·.2)
        let reals := info.temps.map fun (k, _) => atoms.val.getD k (toExpr (0 : BitVec 64))
        let inst (e : Expr) := e.replaceFVars temps reals
        try
          solveLeave m.mvarId! i (inst info.Δ0) (inst info.mid) (inst info.hmid) Δ cs atoms
            (info.hsub.map inst)
        catch e =>
          trace[TypedAsm.fast] "returning failed where it was found to succeed: {e.toMessageData}"
          refusal.set (some disagreement)
          throw e
        trace[TypedAsm.fast] "returned within the walk"
        instantiateMVars m
      | .byte k zero more =>
        let hz ← down zero atoms vs names
        let hm ← withLocalDeclD `b bv fun v => do
          withLocalDeclD `hbyte (← mkAppM ``Ne #[v, toExpr (0 : BitVec 64)]) fun h₁ => do
            withLocalDeclD `hsmall (← mkAppM ``LT.lt #[v, toExpr (256 : BitVec 64)]) fun h₂ => do
              let pad := atoms.val ++
                Array.replicate (k + 1 - atoms.val.size) (toExpr (0 : BitVec 64))
              let atoms' := { atoms with val := pad.set! k v }
              let body ← down more atoms' (((vs.push v).push h₁).push h₂)
                (((names.push `b).push `hbyte).push `hsmall)
              mkLambdaFVars #[v, h₁, h₂] (← instantiateMVars body)
        mkAppM ``And.intro #[hz, hm]
    let hW ← down W atoms #[] #[]
    let rests ← restRef.get
    if rests.isEmpty && enters.isEmpty && leave?.isNone && call?.isNone && via?.isNone &&
        jvia?.isNone && callAll?.isNone && viaAll?.isNone && !exits? W then
      return none
    -- moves enough for these instructions, as the checker counts them
    let fuelE := mkNatLit (Sym.walkFuel code.length)
    let PE := toExpr P
    let WE := toExpr W
    let hP := mkAppN (mkConst ``Sym.Prog.Ok.mk) #[Ψ, ρ, PE, hB, hT, hK]
    let hsys := match linuxNW? with
      | some inst => mkApp2 (mkConst ``Sym.likeLinuxNW) sys inst
      | none => mkApp (mkConst ``Sym.anySystemNW) sys
    let hwr := match linux? with
      | some inst => mkApp2 (mkConst ``Sym.likeLinux) sys inst
      | none => mkApp (mkConst ``Sym.anySystem) sys
    let walkE := mkAppN (mkConst ``Sym.walk) #[PE, codeE, fuelE, mkNatLit k₀, a, SE]
    let hwalk ← mkExpectedTypeHint (← mkEqRefl walkE) (← mkEq walkE WE)
    goal.assign (mkAppN (mkConst ``Sym.walk_sound')
      #[Φ, fetch, sys, Ψ, ρ, PE, codeE, endsE, wrE, hP, hcode, hsys, hwr, hEnds, hWrE, fuelE, mkNatLit k₀, a, SE,
        WE, hwalk, hW])
    -- the values named are in the goals for the rest of the block
    let mut goals : List MVarId := []
    let mut newVals : Array Expr := #[]
    for (m, names) in rests do
      let mut g := m.mvarId!
      newVals := #[]
      for name in names do
        let (fv, g') ← g.intro name
        newVals := newVals.push (mkFVar fv)
        g := g'
      goals := goals ++ [g]
    -- where the walk came to one end, the context there as the goal has it
    -- is kept for the next walk
    match S'?, goals with
    | some S', [g] =>
      let gty := (← instantiateMVars (← g.getType)).consumeMData
      let mut atoms' := atoms
      let mut j := 0
      for mv in moves do
        if let .name k _ := mv then
          if j < newVals.size then
            let pad := atoms'.val ++ Array.replicate (k + 1 - atoms'.val.size) (toExpr (0 : BitVec 64))
            atoms' := { atoms' with val := pad.set! k newVals[j]! }
            j := j + 1
      symKept.set (some (gty.getAppArgs[5]!, { S' with blocks := [] }, atoms'))
    | _, _ => symKept.set none
    -- which instruction of the walk gave each register, and the flags, what
    -- the context says of them at its end
    let stepsL := moves.toList.filterMap fun
      | .step at' i len' before cs => some (at', i, len', before, cs)
      | _ => none
    if stepsL.length > 1 then
      let key₀ := (fetch.hash, n)
      let mut t := (← trailRef.get)[key₀]?.getD {}
      let afters := (stepsL.drop 1).map (·.2.2.2.1) ++ [arrived]
      for ((at', i, _, before, _), after) in stepsL.zip afters do
        for r in allRegs do
          unless before.regs.get r == after.regs.get r do
            -- a register only given a name holds what it held
            let onlyNamed := (match before.regs.get r, after.regs.get r with
              | .int, .eq (.var k) => moves.any fun
                | .name k' r' => k' == k && r' == r
                | _ => false
              | _, _ => false)
            unless onlyNamed do t := t.insert r.name64 (at', i.toAsm)
        unless before.flags == after.flags do t := t.insert "flags" (at', i.toAsm)
        unless before.stack == after.stack && before.stackRest == after.stackRest do
          t := t.insert "stack" (at', i.toAsm)
        unless before.owned == after.owned && before.ownedRest == after.ownedRest do
          t := t.insert "owned" (at', i.toAsm)
      trailRef.modify (·.insert (fetch.hash, atEnd) t)
      trailDone.set true
    return some goals
  let s ← saveState
  stepLimit.set none
  try symStep
  catch e =>
    -- an instruction past the first was refused: the walk up to it is taken
    match ← stepLimit.get with
    | some _ =>
      s.restore
      try symStep finally stepLimit.set none
    | none => throw e

/-- What a register holding the address `v` may be made a pointer to, where
`v` is the address of a label with one declared context: a function, where
that context is a signature's entry, and otherwise the code there, where the
context has nothing left open. The tactic that makes it so, if there is one. -/
def codePtrTactic (Φ : Expr) (v : Nat) (reg : Ident) :
    TacticM (Option (TSyntax `tactic)) := do
  let mut f := Φ
  for _ in [0:4] do
    if f.isAppOf ``CodeTy.ofLabels then break
    let some f' ← unfoldDefinition? f | return none
    f := f'.headBeta
  unless f.isAppOf ``CodeTy.ofLabels && f.getAppNumArgs ≥ 3 do return none
  let args := f.getAppArgs
  let T := args[args.size - 1]!
  let base := args[args.size - 2]!
  let prog := args[args.size - 3]!
  let .const tn _ := T.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? tn | return none
  -- the contexts declared at the label whose address this is
  let mut found : Array (Option Expr × Option Expr) := #[]
  for c in info.ctors do
    let some ci := (← getEnv).find? c | continue
    let r ← forallTelescope ci.type fun xs body => do
      let bs := body.getAppArgs
      unless bs.size ≥ 2 do return none
      let some l := bs[bs.size - 2]!.getAppFn.constName? | return none
      let some n ← addrNat (← mkAppM ``Asm.addr #[prog, base, mkConst l]) | return none
      unless n == v do return none
      let ctx := bs[bs.size - 1]!
      let sig? : Option Expr :=
        if ctx.isAppOf ``FnSig.entry && ctx.getAppNumArgs ≥ 1 then some ctx.getAppArgs[0]!
        else if ctx.isAppOf ``FnSigEx.entry && ctx.getAppNumArgs ≥ 3 then some ctx.getAppArgs[2]!
        else none
      let sig? := sig?.filter (!·.hasFVar)
      let code? := if xs.size == 0 && !ctx.hasFVar then some ctx else none
      return some (sig?, code?)
    if let some x := r then found := found.push x
  let #[(sig?, code?)] := found | return none
  if let some sig := sig? then
    return some (← `(tactic| ty_fn_ptr_fwd $reg to $(← Term.exprToSyntax sig)))
  if let some ctx := code? then
    return some (← `(tactic| ty_code_ptr_fwd $reg to $(← Term.exprToSyntax ctx)))
  return none

/-- A block goal's program and address, and what its context says of each
register and of the flags, where the context is written out as a table. -/
def trailKey (g : MVarId) :
    MetaM (Option ((UInt64 × Nat) × Expr × Array (String × Expr))) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``BlockOk 6 do return none
  let args := ty.getAppArgs
  let some n ← addrNat args[4]! | return none
  let Γ := args[5]!
  let mut parts : Array (String × Expr) := #[]
  if Γ.isAppOfArity ``CtxOf.mk 7 then
    let c := Γ.getAppArgs
    if c[1]!.isAppOfArity ``RegMap.get 2 && c[1]!.appArg!.isAppOfArity ``RegMap.mk 17 then
      let tbl := c[1]!.appArg!.getAppArgs
      for r in allRegs do
        parts := parts.push (r.name64, tbl[1 + regIdx r]!)
    parts := parts.push ("flags", c[4]!)
    -- the whole context, for telling whether the stack or the blocks owned changed
    parts := parts.push ("ctx", Γ)
  return some ((args[1]!.hash, n), args[1]!, parts)

/-- Which of the stack and the blocks owned differ between two contexts,
told on the terms read from them: written differently they may be the same.
Nothing is said to differ where a context cannot be read. -/
def storeChanges (old new : Array (String × Expr)) : MetaM (List String) := do
  let (some (_, Γ), some (_, Γ')) := (old.find? (·.1 == "ctx"), new.find? (·.1 == "ctx"))
    | return []
  if Γ == Γ' then return []
  let (r, _) ← (do
    let some a ← Sym.reifyCtx Γ | return none
    let some b ← Sym.reifyCtx Γ' | return none
    return some ((if a.stack == b.stack && a.stackRest == b.stackRest then [] else ["stack"]) ++
      (if a.owned == b.owned && a.ownedRest == b.ownedRest then [] else ["owned"]))
      : Sym.ReifyM _).run {}
  return r.getD []

/-- What to add to a rejection at an address: for each register the message
speaks of, and for the flags, the stack or the blocks owned if it speaks of
them, the earlier instruction of the block that gave it what it has. Nothing is added for what the block was
entered with. -/
def trailNote (key : UInt64 × Nat) (msg : String) : IO String := do
  let t := (← trailRef.get)[key]?.getD {}
  let has (s : String) : Bool := (msg.splitOn s).length > 1
  let mut note := ""
  for r in allRegs do
    let some (m, asm) := t[r.name64]? | continue
    if has s!"`{r.name64}₀`" then
      note := note ++ s!"\n`{r.name64}₀` is what `{asm}` at address {m} left in `{r.name64}`"
    else if has s!"`{r.name64}`" then
      note := note ++ s!"\n`{r.name64}` was given its type by `{asm}` at address {m}"
  if has "flags" then
    if let some (m, asm) := t["flags"]? then
      note := note ++ s!"\nthe flags were last set by `{asm}` at address {m}"
  if has "piece of the stack" then
    if let some (m, asm) := t["stack"]? then
      note := note ++ s!"\nthe stack was last changed by `{asm}` at address {m}"
  if has "block the context owns" then
    if let some (m, asm) := t["owned"]? then
      note := note ++ s!"\nthe blocks owned were last changed by `{asm}` at address {m}"
  -- said once, however many layers the rejection passes through
  if note != "" && has note then return ""
  return note

/-- Runs a tactic that the user gives to say what cannot be read off the
program, and records what it changed of the context: so that a later
rejection can say that the stack or the blocks owned were last changed here.
It is recorded as the instruction stepped over, or as the tactic where none was. -/
def withTrail (what : String) (tac : TacticM Unit) : TacticM Unit := do
  let pre ← getGoals
  let before ← try trailKey (← getMainGoal) catch _ => pure none
  tac
  let some (key, fetch, old) := before | return
  try
    for g in ← getGoals do
      if pre.contains g then continue
      let some (key', _, new) ← trailKey g | continue
      let by' ← if key' == key then pure s!"{what}" else
        pure ((((← instrsOf fetch).bind (·[key.2]?)).map (·.1.toAsm)).getD what)
      let mut t := (← trailRef.get)[key]?.getD {}
      for (name, e') in new do
        if name == "ctx" then continue
        let some (_, e) := old.find? (·.1 == name) | continue
        if e' == e then continue
        t := t.insert name (key.2, by')
      for name in ← g.withContext (storeChanges old new) do
        t := t.insert name (key.2, by')
      trailRef.modify (·.insert key' t)
  catch _ => pure ()

/-- Types the first instruction of a block goal if it is a straight-line
instruction, leaving the rest of the block as the main goal. -/
partial def typeStepCore (named : Bool := false) : TacticM StepResult :=
    deep <| withMainContext do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOf ``BlockOk do return .notABlock
  let others := (← getGoals).drop 1
  -- The address of the block is written out as a number. Left as the walk
  -- through the program that finds a label, it would be walked again by
  -- every step that so much as compares it with something.
  let addr0 := ty.getAppArgs[4]!
  let (goal, ty) ← do
    if addr0.isAppOfArity ``BitVec.ofNat 2 || addr0.hasFVar || addr0.hasExprMVar then
      pure (goal, ty)
    else
      try
        let n ← evalAddr addr0
        let lit := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)
        let ty' := mkAppN ty.getAppFn (ty.getAppArgs.set! 4 lit)
        pure (← goal.replaceTargetDefEq ty', ty')
      catch _ => pure (goal, ty)
  -- what is saved, to go back to, is the block with its address written out
  setGoals (goal :: others)
  let saved ← saveState
  refusal.set none
  let fast? ← try fastStep goal ty named catch e => do
    saved.restore
    -- the checker's own reason for refusing the instruction is the one given
    if let some msg ← refusal.modifyGet fun r => (r, none) then throwError msg
    trace[TypedAsm.fast] "the checker's step failed: {e.toMessageData}"
    pure none
  if let some rests := fast? then
    setGoals (rests ++ others)
    -- nothing left of the block: it was handed over at a label
    return if rests.isEmpty then .done else .stepped
  -- An instruction that ends the block is known for one from the program's
  -- table, without a step being tried on it first.
  let ended? : Option Instr ← (do
    let a := ty.getAppArgs[4]!
    unless isAddrLit a do return none
    let some n := a.appArg!.nat? | return none
    let some m ← instrsOf ty.getAppArgs[1]! | return none
    let some (i, _) := m[n]? | return none
    return if i.endsBlock then some i else none) <|> pure none
  -- `set_option trace.TypedAsm.fast true` lists the steps the checker did not take
  if ended?.isNone then
    trace[TypedAsm.fast] "by the rules: {(← (do
      let a := ty.getAppArgs[4]!
      unless isAddrLit a do return none
      let some n := a.appArg!.nat? | return none
      let some m ← instrsOf ty.getAppArgs[1]! | return none
      return (m[n]?).map (·.1.toAsm)) <|> pure none).getD "?"}"
  if let some instr := ended? then
    if let .syscall := instr then
      if let some nr ← syscallNumber ty.getAppArgs[5]! then
        if isStepCall nr then
          if let some msg ← refusal.modifyGet fun r => (r, none) then throwError msg
          setGoals [goal]
          typeSyscallStep goal nr
          setGoals ((← getGoals) ++ others)
          return .stepped
    return .endOfBlock instr (← refusal.modifyGet fun r => (r, none))
  setGoals [goal]
  try
    evalTactic (← `(tactic| refine BlockOk.step (Γ' := ?_) (by ty_fetch) ?_ ?_))
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
          if isStepCall nr then
            if let some msg ← refusal.modifyGet fun r => (r, none) then throwError msg
            setGoals [goal]
            typeSyscallStep goal nr
            setGoals ((← getGoals) ++ others)
            return .stepped
      return .endOfBlock instr (← refusal.modifyGet fun r => (r, none))
    -- What a register holds is looked into where the instruction turns on
    -- it. A test of a register against itself, when it holds a pointer that
    -- may be null or what a system call handed back, is where a program
    -- tells the two apart: the block goes on once for each. A register that
    -- points to a block of a declared kind is opened to that kind's shape
    -- where something is reached through it.
    unless named do
      let ctx := ty.getAppArgs[5]!
      let typeOf (r : Reg) : TacticM Expr := goal.withContext do
        whnf (← mkAppM ``CtxOf.regs #[ctx, mkConst (Name.str ``Reg r.name64)])
      let regId (r : Reg) := mkIdent (Name.str ``Reg r.name64)
      -- A byte loaded through a pointer into text is zero or it is not, and
      -- which it is says whether the text goes on: the block goes on once
      -- for each, with the load typed.
      if let .movzx _ _ .w8 (.mem (.sib (some b) none _)) := instr then
        if (← typeOf b).isAppOf ``Ty.str then
          saved.restore
          setGoals [goal]
          evalTactic (← `(tactic| ty_byte as $(mkIdent `b)))
          setGoals ((← getGoals) ++ others)
          return .stepped
      let look? : Option (TSyntax `tactic) ← match instr with
        | .test _ (.reg r) (.reg r') =>
          if r == r' then do
            let τ ← typeOf r
            if τ.isAppOf ``Ty.nullable then pure (some (← `(tactic| ty_null $(regId r))))
            else if τ.isAppOf ``Ty.orErr then
              pure (some (← `(tactic| ty_err $(regId r) as $(mkIdent `e))))
            else pure none
          else pure none
        | i =>
          match i.memOperand? with
          | some (.sib (some b) _ _) => do
            if (← typeOf b).isAppOf ``Ty.ref then pure (some (← `(tactic| ty_open $(regId b))))
            else pure none
          | _ => pure none
      if let some tac := look? then
        saved.restore
        setGoals [goal]
        evalTactic tac
        setGoals ((← getGoals) ++ others)
        return ← typeStepCore (named := false)
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
        return ← typeStepCore (named := true)
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
  -- A register just loaded with the address of some of the program's data
  -- is a pointer to it from here on.
  if let some (.lea .w64 d (.rip _)) ← knownInstr instrTy.getAppArgs[3]! then
    let reg := mkIdent (Name.str ``Reg d.name64)
    let before ← saveState
    try
      Tactic.withoutRecover do
        -- a block of a declared kind gives a pointer to that kind; any other,
        -- a pointer to its shape
        evalTactic (← `(tactic|
          first
          | (refine BlockOk.castRef_of (r := $reg) (by decide) rfl (by first | rfl | decide)
               (by first | rfl | decide) (by first | rfl | decide) (by first | rfl | decide) ?_
             ty_normalize)
          | (refine BlockOk.castPtr_of (r := $reg) (by decide) rfl (by first | rfl | decide)
               (by first | rfl | decide) (by first | rfl | decide) ?_
             ty_normalize)))
        -- how far into the block: worked out as a number
        let g ← getMainGoal
        let ty ← instantiateMVars (← g.getType)
        let regE := mkConst (Name.str ``Reg d.name64)
        let regTy ← g.withContext (do whnf (← mkAppM ``CtxOf.regs #[ty.getAppArgs[5]!, regE]))
        if regTy.isAppOfArity ``Ty.ptr 3 || regTy.isAppOfArity ``Ty.ref 3 then
          let off := regTy.appArg!
          unless off.isRawNatLit || off.isAppOf ``OfNat.ofNat do
            let n ← g.withContext (evalNat off)
            let lit := mkNatLit n
            let ty' := ty.replace fun e => if e == off then some lit else none
            setGoals [← g.replaceTargetDefEq ty']
    catch _ => before.restore
    -- A register just loaded with the address of a label where code is
    -- typed is a pointer to that code from here on, or to the function there.
    let made ← saveState
    try
      let g ← getMainGoal
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      let regE := mkConst (Name.str ``Reg d.name64)
      let regTy ← g.withContext (do whnf (← mkAppM ``CtxOf.regs #[ty.getAppArgs[5]!, regE]))
      if regTy.isAppOfArity ``Ty.eq 1 then
        if let some v ← addrNat regTy.appArg! then
          if let some tac ← codePtrTactic ty.getAppArgs[0]! v reg then
            let rest := (← getGoals).drop 1
            setGoals [g]
            Tactic.withoutRecover (evalTactic tac)
            -- only where nothing is left to be said
            unless (← getGoals).length == 1 do throwError "left over"
            setGoals ((← getGoals) ++ rest)
    catch _ => made.restore
  setGoals ((← getGoals) ++ others)
  return .stepped

/-- Takes one step in a block, keeping the record of which instruction gave
each register its type, and adding to a rejection what that record says of
the registers it speaks of. -/
def typeStep (named : Bool := false) : TacticM StepResult := do
  let g ← getMainGoal
  let mut before ← try trailKey g catch _ => pure none
  -- a block whose address is still written as its label is one just begun
  if let some (key, _, _) := before then
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    unless isAddrLit ty.getAppArgs[4]! do trailRef.modify (·.insert key {})
  -- a context given by name is written out first, so that what the step
  -- changes can be seen
  if let some (_, _, parts) := before then
    if parts.size < 17 then
      try
        let others := (← getGoals).drop 1
        setGoals [g]
        evalTactic (← `(tactic| ty_normalize))
        setGoals ((← getGoals) ++ others)
        before ← trailKey (← getMainGoal)
      catch _ => pure ()
  let r ← try typeStepCore named
    catch e =>
      match before with
      | some (key, _, _) =>
        let note ← trailNote key (← e.toMessageData.toString)
        if note == "" then throw e else throwError "{e.toMessageData}{note}"
      | none => throw e
  if ← trailDone.get then
    trailDone.set false
    return r
  if let (.stepped, some (key, fetch, old)) := (r, before) then
    try
      let some (key', _, new) ← trailKey (← getMainGoal) | return r
      if key' == key then return r
      let instr? := ((← instrsOf fetch).bind (·[key.2]?)).map (·.1)
      let asm := (instr?.map (·.toAsm)).getD "the instruction"
      let named := (instr?.map (·.wantsNamed.map (·.name64))).getD []
      let mut t := (← trailRef.get)[key]?.getD {}
      for name in ← (← getMainGoal).withContext (storeChanges old new) do
        t := t.insert name (key.2, asm)
      for (name, e') in new do
        if name == "ctx" then continue
        let some (_, e) := old.find? (·.1 == name) | continue
        if e' == e then continue
        -- a register only given a name holds what it held
        if named.contains name && e.isConstOf ``Ty.int && e'.isAppOfArity ``Ty.eq 1
            && e'.appArg!.isFVar then continue
        t := t.insert name (key.2, asm)
      trailRef.modify (·.insert key' t)
    catch _ => pure ()
  return r

/-- Types one straight-line instruction at the start of a block. -/
elab "ty_step" : tactic => do
  match ← typeStep with
  | .stepped => pure ()
  | .done => pure ()
  | .endOfBlock instr _ =>
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

open Lean Meta Elab Tactic in
/-- Types the straight-line instructions before the one something is about to
be said of, so that a hint may be given for a call, a branch or a system
call without first stepping up to it. An instruction that does not type by
itself is where this stops, and so is the system call numbered `before`,
which would otherwise be stepped over. -/
def advance (before : Option Nat := none) : TacticM Unit := do
  -- whether the block is at the system call something is to be said of
  let there : TacticM Bool := do
    let some nr := before | return false
    try
      let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
      unless ty.isAppOf ``BlockOk do return false
      let a := ty.getAppArgs[4]!
      unless isAddrLit a do return false
      let some n := a.appArg!.nat? | return false
      let some m ← instrsOf ty.getAppArgs[1]! | return false
      let some (.syscall, _) := m[n]? | return false
      return (← syscallNumber ty.getAppArgs[5]!) == some nr
    catch _ => return false
  let mut go := true
  while go do
    if ← there then break
    let s ← saveState
    try
      match ← typeStep with
      | .stepped => pure ()
      | _ => go := false
    catch _ =>
      s.restore
      go := false

end TypedAsm
