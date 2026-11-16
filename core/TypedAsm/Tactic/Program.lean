import TypedAsm.Tactic.Block

/-!
# The tactics: program

What every typing declares: the commands that make a program's typing and its safety theorems.
-/

namespace TypedAsm

open Lean Meta Elab Tactic

/-! ## What every typing declares

The contexts at the labels and the layouts of the data are a program's
typing. The code typing, the memory typing, its well-formedness, the entry
contract and the safety theorems follow from those, and are the same few
declarations for every program. These commands make them. -/

/-- Whether none of the blocks holds a typed value. -/
def plainBlocks (bs : List (BitVec 64 × Layout)) : Bool :=
  bs.all fun x => x.2.shape.vals.isEmpty

theorem plain_of_check {bs : List (BitVec 64 × Layout)} (h : plainBlocks bs = true) :
    ∀ x ∈ bs, x.2.shape.vals = [] := fun x hx =>
  List.isEmpty_iff.mp (List.all_eq_true.mp h x hx)

/-- `asm_label name l`: defines `name` as the address of label `l` of the
program declared with `asm_program`, written out as a number, and proves in
`name_eq` that it is that label's address.

The address is where the layout of the program puts the label. Written out,
it costs nothing to use; left as the walk through the program that finds it,
every step of a proof that looked at it would make the walk again. -/
syntax "asm_label " ident term:max : command

open Lean Elab Command in
elab_rules : command
  | `(asm_label $name $l) => do
    let code := mkIdent `code
    let base := mkIdent `base
    let n ← liftTermElabM do
      let ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
      let e ← Term.elabTermEnsuringType (← `(Asm.addr $code $base $l)) ty
      Term.synthesizeSyntheticMVarsNoPostponing
      evalAddr (← instantiateMVars e)
    let lit := Syntax.mkNumLit (toString n)
    let eqName := mkIdent (name.getId.appendAfter "_eq")
    elabCommand (← `(/-- Where the label is loaded. -/
      def $name : BitVec 64 := $lit))
    elabCommand (← `(theorem $eqName : $name = Asm.addr $code $base $l := by decide +kernel))

unsafe def evalRunsUnsafe (e : Expr) : MetaM (List (Nat × Nat × Bool)) := do
  let ty ← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``Nat,
    ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Bool]]]
  evalExpr (List (Nat × Nat × Bool)) ty e

unsafe def evalNatsUnsafe (e : Expr) : MetaM (List Nat) := do
  evalExpr (List Nat) (← mkAppM ``List #[mkConst ``Nat]) e

/-- The value of a closed term for a list of numbers. -/
@[implemented_by evalNatsUnsafe]
opaque evalNats (e : Expr) : MetaM (List Nat)

/-- The value of a closed term for a list of runs of data: where each is,
how long, and whether it may be written. -/
@[implemented_by evalRunsUnsafe]
opaque evalRuns (e : Expr) : MetaM (List (Nat × Nat × Bool))

/-- How a program is entered, as the context of its entry label says: with
nothing at and above `rsp` it looks at (`entryCtx n`), with its arguments as
numbers (`argsCtx n c`, for every count `c`), or with their text
(`textsCtx n c`). -/
inductive EntryKind
  | plain | args | texts
  deriving DecidableEq, Inhabited

open Lean Meta Elab in
/-- The kind of entry and the stack room, in words, that the context of the
entry label asks for; nothing, if the context is of another form. -/
def entryKindOf (start : Term) : TermElabM (Option (EntryKind × Nat)) := do
  let e ← Term.elabTerm start none
  let (_, _, ty) ← forallMetaTelescopeReducing (← inferType e)
  let ctx := (← whnfR ty).appArg!
  let kind? :=
    if ctx.isAppOf ``entryCtx then some EntryKind.plain
    else if ctx.isAppOf ``argsCtx then some .args
    else if ctx.isAppOf ``textsCtx then some .texts
    else none
  let some kind := kind? | return none
  return some (kind, ← evalNat ctx.getAppArgs[0]!)

/-- `asm_typing At`: for the program declared with `asm_program`, whose
labels have the contexts `At`, defines in the current namespace

* `blocks`, the program's blocks of memory: each labelled run of data, as
  plain bytes, writable if its segment is. `blocks_eq` says these are the
  runs of data the program has;
* `Φ`, the code typing: those contexts at the addresses of their labels;
* `Ψ`, the memory typing: those blocks;
* `memOk`, that the memory typing is well formed;
* `Entry`, what the program needs of the state it starts in: its bytes in
  memory, executable where they are to be executed, each block readable or
  writable as its layout says, and its stack.

How much stack the program needs, and whether it looks at its arguments, is
read from the context of its entry label, `At.start`: `entryCtx n`; or, one
for every number of arguments `c`, `argsCtx n c` for a program that reads
them as numbers, `textsCtx n c` for one that reads their text. The contract
then asks for the stack as Linux leaves it for a new program.

With `data` at the end, each run of data that is never written also says
the bytes it holds, which is what lets a `write` from it be known for what
it writes (`asm_safety … writes R`).

Each of these may be said instead of worked out:
`asm_typing At blocks bs kinds ks room n`. The blocks are said when some of
the data is more than plain bytes: holds pointers, is of a declared kind, or
is text. The room is said when the entry label's context is of another form.

The proof that the program is well typed, `blocksOk`, comes after this if
some label needs something said, and `asm_safety` after that. -/
syntax "asm_typing " ident (&" blocks " term:max)? (&" kinds " term:max)? (&" room " term:max)?
  (&" data")? : command

open Lean Elab Command Meta in
elab_rules : command
  | `(asm_typing $ctxs $[blocks $bs?]? $[kinds $ks?]? $[room $n?]? $[data%$d?]?) => do
    let id (n : Name) := mkIdent n
    let code := id `code
    let base := id `base
    -- the blocks: as said, or the labelled runs of data, written out
    let bs ← match bs? with
      | some bs => pure bs
      | none => do
        let runs ← liftTermElabM do
          let e ← Term.elabTerm (← `((Asm.dataRuns $base $code).map
            fun r => (r.1, r.2.1, decide (r.2.2 = Perm.rw)))) none
          Term.synthesizeSyntheticMVarsNoPostponing
          evalRuns (← instantiateMVars e)
        let items ← runs.toArray.mapM fun (a, size, w) => do
          let wq := if w then mkIdent ``true else mkIdent ``false
          -- with `data`, a run that is never written says the bytes it holds
          if d?.isSome && !w then
            let bytes ← liftTermElabM do
              let e ← Term.elabTerm (← `((List.range $(Syntax.mkNumLit (toString size))).map
                fun k => ((partsByte (Asm.parts $base $code)
                  ($(Syntax.mkNumLit (toString a)) + k)).getD 0).toNat)) none
              Term.synthesizeSyntheticMVarsNoPostponing
              evalNats (← instantiateMVars e)
            let bq ← bytes.toArray.mapM fun b =>
              `((($(Syntax.mkNumLit (toString b)) : BitVec 8)))
            `(((($(Syntax.mkNumLit (toString a)) : BitVec 64)),
              (⟨ShapeOf.raw $(Syntax.mkNumLit (toString size)), $wq, none, 0, some [$bq,*]⟩ :
                Layout)))
          else
            `(((($(Syntax.mkNumLit (toString a)) : BitVec 64)),
              (⟨ShapeOf.raw $(Syntax.mkNumLit (toString size)), $wq, none, 0, none⟩ : Layout)))
        let blocks := id `blocks
        elabCommand (← `(
          /-- The program's blocks of memory: its labelled runs of data, as plain
          bytes, writable where their segment is. -/
          def $blocks : List (BitVec 64 × Layout) := [$items,*]))
        elabCommand (← `(
          theorem $(id `blocks_eq) :
              ($blocks).map (fun x => (x.1.toNat, x.2.shape.size, x.2.writable)) =
                (Asm.dataRuns $base $code).map
                  (fun r => (r.1, r.2.1, decide (r.2.2 = Perm.rw))) := by
            decide +kernel))
        `($blocks)
    -- the stack room: as said, or what the entry label's context asks
    let found ← liftTermElabM do entryKindOf (← `($(mkIdent (ctxs.getId ++ `start))))
    let kind := (found.map (·.1)).getD .plain
    let n ← match n?, found with
      | some n, _ => pure n
      | none, some (_, room) => pure (Syntax.mkNumLit (toString room))
      | none, none => throwError "asm_typing: the entry label's context is not `entryCtx n`, \
          `argsCtx n c` or `textsCtx n c`; say how much stack the program needs with `room n`"
    let ks ← match ks? with
      | some ks => pure ks
      | none => `([])
    elabCommand (← `(
      /-- The code typing: the contexts allowed at each label, at the addresses of
      the labels. -/
      def $(id `Φ) : CodeTy := .ofLabels $code $base $ctxs))
    elabCommand (← `(
      /-- The memory typing: the program's blocks. -/
      def $(id `Ψ) : MemTy := .ofList $bs $ks))
    elabCommand (← `(
      theorem $(id `memOk) : MemTy.WF $(id `Ψ) := MemTy.wf_of_check (by decide)))
    elabCommand (← `(
      /-- What the program needs of the state it starts in: its bytes in memory,
      executable where they are to be executed, each block with its permissions, and
      its stack. This is the contract with whatever loads the program; for the ELF file,
      with the Linux kernel. -/
      abbrev $(id `Entry) : State → Prop :=
        $(← match kind with
          | .plain => `(TypedAsm.Entry $(id `entry) $(id `parts) $bs $n 0)
          | .args => `(TypedAsm.EntryArgs $(id `entry) $(id `parts) $bs $n)
          | .texts => `(TypedAsm.EntryTexts $(id `entry) $(id `parts) $bs $n))))

open Lean Meta Elab Tactic in
/-- Shows that a value the program's bytes spell is of the type its block
gives it: a number; zero or an address, for a pointer that may be null; the
address of a block of the right kind or shape; the address of a function's
label. `bOk` is the proof that the program is well typed, which is what makes
a function's address a function pointer. -/
partial def typeValue (bOk : Ident) (g : MVarId) : TacticM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  unless t.isAppOf ``HasTy && args.size == 6 do
    throwError "ty_values: not a statement that a value has a type{indentExpr t}"
  let v := args[5]!
  let w ← evalNat (← mkAppM ``BitVec.toNat #[v])
  let run (tac : TacticM (TSyntax `tactic)) : TacticM (List MVarId) := do
    setGoals [g]
    Tactic.withoutRecover do evalTactic (← tac)
    getGoals
  let fail {α} (what : MessageData) : TacticM α :=
    throwError "the program's data does not have the type its block gives it: the eight bytes \
      spell {w}, which is not {what}"
  let τ0 ← whnfR args[4]!
  -- a pointer to a function: the address of a label where the function is typed
  if τ0.isAppOf ``FnSig.ty || τ0.isAppOf ``FnSigEx.ty then
    let ex := τ0.isAppOf ``FnSigEx.ty
    let gs ← run (if ex then `(tactic| refine BlocksOk.hasTy_fnAll $bOk ?_ _)
      else `(tactic| refine BlocksOk.hasTy_fn $bOk ?_ _))
    let [g'] := gs | throwError "ty_values: unexpected goals"
    let atArgs := (← instantiateMVars (← g'.getType)).getAppArgs
    let Φ := atArgs[atArgs.size - 2]!
    let some Φ' ← unfoldDefinition? Φ | throwError "ty_values: the code typing is not from labels"
    let .const L _ := Φ'.getAppArgs[0]! | throwError "ty_values: the labels are not a plain type"
    let .inductInfo info ← getConstInfo L | throwError "ty_values: the labels are not a plain type"
    for c in info.ctors do
      let s ← saveState
      try
        setGoals [g']
        let cq := mkIdent c
        Tactic.withoutRecover do evalTactic (← if ex then
          `(tactic| exact FnSigEx.at_label_eq (l := $cq) (by decide +kernel)
            (by intros; constructor; assumption))
          else `(tactic| exact FnSig.at_label_eq (l := $cq) (by decide +kernel)
            (by intros; constructor; assumption)))
        return
      catch _ => s.restore
    fail m!"the address of a label where a function of that signature is typed"
  let τ ← whnfD τ0
  if τ.isAppOf ``Ty.int then
    discard <| run `(tactic| first | exact trivial | simp only [HasTy])
  else if τ.isAppOf ``Ty.eq then
    try discard <| run `(tactic| exact hasTy_eq.mpr (by decide +kernel))
    catch _ => fail m!"the number the type says"
  else if τ.isAppOf ``Ty.nullable then
    if w == 0 then
      discard <| run `(tactic| exact hasTy_nullable.mpr (.inl (by decide +kernel)))
    else
      let [g'] ← run `(tactic| refine hasTy_nullable.mpr (.inr ?_))
        | throwError "ty_values: unexpected goals"
      typeValue bOk g'
  else if τ.isAppOf ``Ty.ref || τ.isAppOf ``Ty.ptr then
    let off ← evalNat τ.getAppArgs.back!
    let aq := Syntax.mkNumLit (toString (w - off))
    let isRef := τ.isAppOf ``Ty.ref
    try
      discard <| run (if isRef then
        `(tactic| exact hasTy_ref.mpr
          ⟨($aq : BitVec 64), _, rfl, rfl, by decide, by decide +kernel⟩)
        else `(tactic| exact hasTy_ptr.mpr
          ⟨($aq : BitVec 64), _, rfl, rfl, by decide, by decide +kernel⟩))
    catch _ =>
      fail (if isRef then m!"the address of a block of the kind pointed to, which may be \
          written if the pointer may write"
        else m!"the address of a block of the shape pointed to, which may be written if the \
          pointer may write")
  else
    throwError "ty_values: a value of type{indentExpr τ0}\nis not one that can be settled from \
      the program's bytes; show the data typed by hand and give it to `asm_safety` with `values`"

open Lean Meta Elab Tactic in
partial def typeFields (bOk : Ident) (g : MVarId) : TacticM Unit := do
  let t ← whnfD (← instantiateMVars (← g.getType))
  if t.isConstOf ``True then g.assign (mkConst ``True.intro); return
  let g ← g.replaceTargetDefEq t
  let [here, rest] ← g.apply (mkConst ``And.intro) | throwError "ty_values: unexpected goals"
  let [cover, val] ← here.apply (mkConst ``And.intro)
    | throwError "ty_values: unexpected goals"
  setGoals [cover]
  try Tactic.withoutRecover do evalTactic (← `(tactic| decide +kernel))
  catch _ => throwError "ty_values: a typed value of a block is where the program puts no \
    bytes: its type cannot be settled from the program"
  let val ← val.replaceTargetDefEq (← instantiateMVars (← val.getType)).headBeta
  typeValue bOk val
  typeFields bOk rest

open Lean Meta Elab Tactic in
partial def typeBlocks (bOk : Ident) (g : MVarId) : TacticM Unit := do
  let t ← whnfD (← instantiateMVars (← g.getType))
  if t.isConstOf ``True then g.assign (mkConst ``True.intro); return
  let g ← g.replaceTargetDefEq t
  let [here, rest] ← g.apply (mkConst ``And.intro) | throwError "ty_values: unexpected goals"
  typeFields bOk here
  typeBlocks bOk rest

/-- `ty_values blocksOk` proves that the typed values of a program's blocks
are, in the bytes the program puts there, of their types: `ValsOk P parts
blocks`, where `P` is having a type. Each value is read from the bytes and
shown to be what its type says: zero or an address for a pointer that may be
null, the address of a block of the right kind or shape for a pointer, the
address of a function's label for a function pointer; for that last,
`blocksOk` is the proof that the program is well typed. -/
syntax "ty_values " ident : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| ty_values $bOk) => do
    typeBlocks bOk (← getMainGoal)
    setGoals []

/-- `asm_safety At.start`: for a program declared with `asm_program` and
`asm_typing`, whose entry label has the context `At.start`, proves in the
current namespace

* `blocksOk`, that the program is well typed, by `ty_program`, unless it has
  been proved already: a program some of whose labels need something said is
  proved well typed first, by hand, under that name;

* `safeMem_of_entry`: **from any state meeting the entry contract, the
  program is safe** on the machine that fetches instructions by decoding
  memory. It never gets stuck and never faults;
* `start_entry`: the simulator's starting state meets the entry contract;
* `safeMem`: the simulator's run is safe;
* `safeMem_world`: and is whatever the outside world does: whatever there is
  to read, whatever the kernel answers and wherever it puts memory;

and checks that they rest on Lean's three standard axioms and nothing else.

Where blocks hold typed values to begin with (pointers to other blocks,
links that may be null, addresses of functions), that the program's bytes
are of those types is settled by reading them (`ty_values`). For a value
that cannot be settled so, say what shows the values are of their types with
`values h` after the label, where `h` is a proof for every state meeting
the contract. -/
syntax "asm_safety " term:max (&" values " term:max)? (&" exits " term:max)?
  (&" writes " term:max)? : command

open Lean Elab Command in
elab_rules : command
  | `(asm_safety $start $[values $v?]? $[exits $q?]? $[writes $r?]?) => do
    let id (n : Name) := mkIdent n
    -- The system the program is typed against: `linux`, or, where what the
    -- program ends with is to be shown, `linux` refusing any other status.
    -- Safety under `linux` follows from the typing either way.
    let os ← match q?, r? with
      | some q, some r => `(Syscall.writesOnly (Syscall.exitsOnly linux $q) $r)
      | some q, none => `(Syscall.exitsOnly linux $q)
      | none, some r => `(Syscall.writesOnly linux $r)
      | none, none => `(linux)
    let fields ← match v? with
      | some v => `($v)
      | none => `(by
          first
          | exact Entry.plain (plain_of_check (by decide))
          | exact fun n => Entry.valuesOk_of
              (P := HasTy $(id `fetch) $os $(id `Ψ) n) h (by ty_values $(id `blocksOk)))
    -- Where the program has not been proved well typed, it is proved here,
    -- which it can be if no label's block needs anything said.
    let ns ← getCurrNamespace
    unless (← getEnv).contains (ns ++ `blocksOk) do
      elabCommand (← `(
        /-- The program is well typed: the block at each label types, with nothing
        said. -/
        theorem $(id `blocksOk) : BlocksOk $(id `Φ) $(id `fetch) $os $(id `Ψ) := by
          ty_program))
    let kind := ((← liftTermElabM do entryKindOf start).map (·.1)).getD .plain
    let mut exits : Option Term := none
    let mut writes : Option Term := none
    if kind == .plain then
      elabCommand (← `(
        /-- **From any state meeting the entry contract, the program is safe on the
        machine that fetches instructions by decoding memory.** It never gets stuck and
        never faults. -/
        theorem $(id `safeMem_of_entry) {s : State} (h : $(id `Entry) s) : SafeMem linux s :=
          $(← match q?, r? with
            | some _, some _ =>
              `((h.safeMem_exits_writes $(id `blocksOk) $(id `memOk) $start $fields).1)
            | some _, none => `((h.safeMem_exits $(id `blocksOk) $(id `memOk) $start $fields).1)
            | none, some _ =>
              `((h.safeMem_writes $(id `blocksOk) $(id `memOk) $start $fields).1)
            | none, none => `(h.safeMem $(id `blocksOk) $(id `memOk) $start $fields))))
      if q?.isSome && r?.isSome then
        exits := some (← `((h.safeMem_exits_writes $(id `blocksOk) $(id `memOk) $start $fields).2.1))
        writes := some (← `((h.safeMem_exits_writes $(id `blocksOk) $(id `memOk) $start $fields).2.2))
      else if q?.isSome then
        exits := some (← `((h.safeMem_exits $(id `blocksOk) $(id `memOk) $start $fields).2))
      else if r?.isSome then
        writes := some (← `((h.safeMem_writes $(id `blocksOk) $(id `memOk) $start $fields).2))
      elabCommand (← `(
        /-- The starting state used by the simulator meets the entry contract. -/
        theorem $(id `start_entry) : $(id `Entry) $(id `start) := by ty_loaded))
      elabCommand (← `(
        /-- The simulator's run is safe, with instructions decoded from memory. -/
        theorem $(id `safeMem) : SafeMem linux $(id `start) :=
          $(id `safeMem_of_entry) $(id `start_entry)))
      elabCommand (← `(
        /-- It is safe whatever the outside world does: whatever there is to read,
        whatever the kernel answers, and wherever it puts memory. -/
        theorem $(id `safeMem_world) (w : World) :
            SafeMem linux { $(id `start) with world := w } :=
          $(id `safeMem_of_entry) (($(id `start_entry)).withWorld w)))
    else
      -- a program that looks at its arguments: for every number of them
      -- which theorem: safety alone, or with what the program ends with,
      -- what it writes, or both
      let thm := mkIdent (match q?, r? with
        | some _, some _ => `safeMem_exits_writes
        | some _, none => `safeMem_exits
        | none, some _ => `safeMem_writes
        | none, none => `safeMem)
      let all ← if kind == .args then
          `(h.$thm:ident $(id `blocksOk) $(id `memOk) $start (plain_of_check (by decide)))
        else `(h.$thm:ident $(id `blocksOk) rfl $start (plain_of_check (by decide)))
      let safe ← match q?, r? with
        | none, none => pure all
        | _, _ => `(($all).1)
      match q?, r? with
      | some _, some _ =>
        exits := some (← `(($all).2.1))
        writes := some (← `(($all).2.2))
      | some _, none => exits := some (← `(($all).2))
      | none, some _ => writes := some (← `(($all).2))
      | none, none => pure ()
      elabCommand (← `(
        /-- **From any state meeting the entry contract, however many arguments the
        program was given and whatever they are, it is safe on the machine that
        fetches instructions by decoding memory.** It never gets stuck and never
        faults. -/
        theorem $(id `safeMem_of_entry) {s : State} (h : $(id `Entry) s) : SafeMem linux s :=
          $safe))
      elabCommand (← `(
        /-- The starting state used by the simulator meets the entry contract, whatever
        the arguments. -/
        theorem $(id `start_entry) (args : List (List Byte)) :
            $(id `Entry) ($(id `startArgs) args) := by ty_loaded))
      elabCommand (← `(
        /-- The simulator's run is safe whatever arguments it is given. -/
        theorem $(id `safeMem) (args : List (List Byte)) :
            SafeMem linux ($(id `startArgs) args) :=
          $(id `safeMem_of_entry) ($(id `start_entry) args)))
      elabCommand (← `(
        /-- And whatever the outside world does: whatever there is to read, whatever
        files there are, whatever the kernel answers and wherever it puts memory. -/
        theorem $(id `safeMem_world) (args : List (List Byte)) (w : World) :
            SafeMem linux { $(id `startArgs) args with world := w } :=
          $(id `safeMem_of_entry) (($(id `start_entry) args).withWorld w)))
    let mut thms := [`safeMem_of_entry, `safeMem_world]
    if let (some q, some pf) := (q?, exits) then
      elabCommand (← `(
        /-- **From any state meeting the entry contract, the program ends only with
        a status that is as wanted**: wherever it reaches a system call that ends
        it. This is on the machine that looks instructions up in the program. -/
        theorem $(id `exits_of_entry) {s : State} (h : $(id `Entry) s) :
            ExitsOnly $(id `fetch) $q s :=
          $pf))
      thms := thms ++ [`exits_of_entry]
    if let (some r, some pf) := (r?, writes) then
      elabCommand (← `(
        /-- **From any state meeting the entry contract, the program writes only
        what is wanted**: wherever it reaches a `write`, the descriptor and the
        bytes it offers the kernel are as the condition says. This is on the
        machine that looks instructions up in the program. -/
        theorem $(id `writes_of_entry) {s : State} (h : $(id `Entry) s) :
            WritesOnly $(id `fetch) $r s :=
          $pf))
      thms := thms ++ [`writes_of_entry]
    -- the proofs rest on Lean's three standard axioms and nothing else
    for thm in thms do
      let axs ← Lean.collectAxioms (ns ++ thm)
      for a in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "`{ns ++ thm}` depends on the axiom `{a}`, which is not one of Lean's \
            three standard axioms"

end TypedAsm
