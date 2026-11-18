import TypedAsm.U.Say
import TypedAsm.U.Explain
import TypedAsm.Runs

/-!
# What every checked program states

A program declared with `asm_program`, its labels said, is checked by one
computation; and what the check shows is the same few theorems for every
program. `asm_checked` states them.
-/

namespace TypedAsm.U

attribute [local instance] IsLabel.dec

open Lean

variable {L : Type} [IsLabel L]

/-- The first of some things looked for that is not so, as what to say of it. -/
def firstNot : List (Bool × (Unit → String)) → Option String
  | [] => none
  | (true, _) :: rest => firstNot rest
  | (false, say) :: _ => some (say ())

/-- **Why the check of a whole program fails**, in words: the first thing
it looks for that is not so, and where that is the typing of the labels'
code, each refusal as `explainText` says it. Nothing where the check
passes. It is worked out from the parts the check is made of, and nothing
rests on it. -/
def wholeWhy (code : List (Asm L)) (l : L) (n : Nat) (ks : List (Nat × ShapeS))
    (bs : List (BitVec 64 × LayoutS)) (pg : Prog) (labels : List Label) (fuel : Nat) :
    Option String :=
  let base := Asm.base code
  let segs := Asm.imageFast base code l
  let blocks := denBlocks bs
  let entry := Asm.addr code base l
  firstNot [
    (decide (pg.code = progCode (Asm.table base code)), fun _ =>
      "the program given to the checker is not this program: its `code` is to be " ++
      "`progCode (Asm.table base code)`"),
    (labels.any (fun x => decide (x.addr = entry)), fun _ =>
      "no label is at " ++ addrSay entry ++ ", where the program starts: the labels are to " ++
      "have `⟨entry, inProgram " ++ toString n ++ "⟩`"),
    (labels.any (fun x => decide (x.addr = entry) && decide (x.pat = entryCtx (stackRoom n))),
      fun _ =>
      "the label at " ++ addrSay entry ++ ", where the program starts, does not say what a " ++
      "program with " ++ toString n ++ " slots of stack starts with: it is to be `inProgram " ++
      toString n ++ "`, with nothing more said"),
    (decide (8 * n ≤ 0x7fff0000), fun _ =>
      "the stack asked for, " ++ toString n ++ " slots, is more than there is room for"),
    (tableOk (Asm.table base code), fun _ =>
      "two instructions of the program are at one address, or one is at an address a machine " ++
      "word does not hold"),
    (blocks.all (fun x => blocksWf [x]), fun _ =>
      match blocks.find? (fun x => !blocksWf [x]) with
      | some x => "the block said at " ++ addrSay x.1 ++ " does not make sense: it is of no " ++
          "bytes or too many, or a value it says it holds is not within it, or it says its " ++
          "bytes and may be written, or says other than all of them"
      | none => ""),
    (blocksWf blocks, fun _ => "two of the blocks said overlap"),
    (decide (blocks.Pairwise fun x y => x.1 ≠ y.1), fun _ => "two blocks are said at one address"),
    (segsOk segs && segsFull segs, fun _ =>
      "the program's segments do not lie each on pages of its own, where a program can have " ++
      "memory, each with some bytes"),
    (segs.all (offStack (stackStretch n).1.toNat (stackStretch n).2.toNat) &&
      (Asm.partsExt base code).all (fun g => decide (g.1 + g.2.2 ≤ stackLow n)) &&
      segs.all (fun g => decide (g.1 + pageBytes g.2.2.length ≤ stackLow n)), fun _ =>
      "the program reaches into the memory its stack is given, which starts at " ++
      addrSay (BitVec.ofNat 64 (stackLow n))),
    (Loaded.holdsAllE (Asm.imageExt base code) (Asm.partsExt base code) && Asm.headOkE base code,
      fun _ => "the program's lines are not all in its segments as laid out"),
    (blocksIn segs blocks, fun _ =>
      match blocks.find? (fun x => !segs.any fun g => blockOf g x) with
      | some x => "the block said at " ++ addrSay x.1 ++ ", of " ++ toString x.2.size ++
          " bytes, is not of one of the program's segments: it does not lie within one; or it " ++
          "may be written and the segment may not; or the bytes or text it says are not what " ++
          "the segment has there, or the segment may be written"
      | none => ""),
    ((segStretches segs []).all (stretchIn (blocks.map fun x => (x.1, x.2.size))), fun _ =>
      "the blocks said do not cover the program's segments: every page of every segment is " ++
      "to be within the blocks, taken together"),
    (pg.statics.all (staticS bs), fun _ =>
      match pg.statics.find? (fun f => !staticS bs f) with
      | some f => "what the program says of its static data is not seen in its blocks: that " ++
          f.1.say ++ " is " ++ f.2.say
      | none => ""),
    (kindsCheck ks bs, fun _ =>
      "a kind of block mentions a value of some label's, or a block said to be of a kind has " ++
      "not that kind's shape"),
    (checkProgram pg labels fuel 0, fun _ => explainText pg labels fuel),
    (valsHold (codeJ pg labels fuel) segs bs, fun _ =>
      match bs.find? (fun x => !valsHold (codeJ pg labels fuel) segs [x]) with
      | some x => "the block said at " ++ addrSay x.1 ++ " does not hold what its shape says: " ++
          "a value in it is not, by the program's bytes there, of the type said"
      | none => "")]

/-- What `asm_checked` says where its check fails. -/
def wholeWhyText (code : List (Asm L)) (l : L) (n : Nat) (ks : List (Nat × ShapeS))
    (bs : List (BitVec 64 × LayoutS)) (pg : Prog) (labels : List Label) (fuel : Nat) : String :=
  match wholeWhy code l n ks bs pg labels fuel with
  | some why => "the program is refused:\n" ++ why
  | none => ""

/-- `asm_decide ok why`: the goal, that the check `ok` is true, by running
the type checker as compiled code (`native_decide`). Where it fails, the
text `why` is the error.

The type checker's soundness is proved in the ordinary way and rests on
Lean's three standard axioms. That a given program type-checks is a
computation, and it is Lean's compiled code that runs it: a theorem come by
so rests besides on an axiom of its own that says the run came out true,
which is to say on Lean's compiler and runtime computing what the
definitions say. `#print axioms` shows it. -/
syntax "asm_decide " term:max term:max : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| asm_decide $ok $why) => do
    let passes ← try
        unsafe Term.evalTerm Bool (mkConst ``Bool) ok
      catch _ => pure true
    unless passes do
      let msg ← try
          unsafe Term.evalTerm String (mkConst ``String) why
        catch _ => pure ""
      throwError (if msg.isEmpty then "the check fails" else msg)
    evalTactic (← `(tactic| native_decide))

/-- `asm_checked code start l stack n program pg labels ls`: for the program
`code` declared with `asm_program code start l stack n`, the checker's
program `pg` and the labels `ls`, states in the current namespace

* `checked`: the check, run as compiled code: the labels' code is typed,
  and whatever arguments the program is given, the state it is loaded into
  starts as its entry asks;
* `start_eq`: the state `asm_program` starts the program in with given
  arguments is the one the check is of;
* `safe_in`: the program is safe on the machine that decodes its
  instructions from memory, whatever its arguments and whatever the world
  outside it holds;
* `safe`: so as it is run, with any arguments.

With `exits q` after it, where `pg` asks at each `exit` that the status
satisfy `q`, it states instead of `safe_in` the theorem `safe_exits_in`,
that the program is safe and ends only with a status `q` holds of; and
with `safe`, the theorem `exits`.

With `writes r said sd` after that, where `pg` asks besides that each
`write` offer a descriptor and bytes `r` holds of, knowing the bytes `sd`
says the program's data holds (`pre := preOut sd q r`), it states
`said_ok`, that the data holds those bytes; `safe_exits_writes_in`; and
with `safe` and `exits`, the theorem `writes`.

`blocks bs` after the labels gives the blocks the program says its segments
are; where it is left out, each segment is one block of plain bytes.
`kinds ks` gives the program's kinds of block, which `pg` is to have too.
`laws h`, last, gives the proof that the laws `pg`
states of the functions its author defines are so (`LawsHold pg.fns
pg.laws`); it is needed only where `pg` states any.

How far the check goes from a label is worked out from the program: as far
as the program is long, which is as far as any way through it goes that
passes no instruction twice. A loop with no label that goes round a number
of times that is written out is gone round that many times, and may take
more: `steps n` allows `n` more.

Where the check fails, the error says why, in the program's terms
(`wholeWhy`): what of the program as a whole is not as the check asks, or
each instruction or label that is refused and what is not so there. -/
syntax "asm_checked " ident &" start " term:max &" stack " term:max &" program " term:max
  &" labels " term:max (&" blocks " term:max)? (&" kinds " term:max)?
  (&" steps " term:max)? (&" exits " term:max)? (&" writes " term:max &" said " term:max)?
  (&" laws " term:max)? : command

macro_rules
  | `(asm_checked $code start $l stack $n program $pg labels $ls $[blocks $bs?]? $[kinds $ks?]?
      $[steps $st?]? $[exits $q?]? $[writes $r? said $sd?]? $[laws $lw?]?) => do
    let checked := mkIdent `checked
    let startEq := mkIdent `start_eq
    let safeIn := mkIdent `safe_in
    let safeExitsIn := mkIdent `safe_exits_in
    let safe := mkIdent `safe
    let exits := mkIdent `exits
    let writes := mkIdent `writes
    let saidOk := mkIdent `said_ok
    let safeExitsWritesIn := mkIdent `safe_exits_writes_in
    let startArgs := mkIdent `startArgs
    let fetch := mkIdent `fetch
    let bs ← match bs? with
      | some bs => pure bs
      | none => `((blocksOf $code $l))
    let ks ← match ks? with
      | some ks => pure ks
      | none => `(([] : List (Nat × ShapeS)))
    let lw ← match lw? with
      | some lw => pure lw
      | none => `((LawsHold.nil _))
    let k ← match st? with
      | some st => `(($st + needFuel $pg $ls $ks))
      | none => `((needFuel $pg $ls $ks))
    let mut cmds : Array (TSyntax `command) := #[]
    cmds := cmds.push (← `(/-- **The check**: the labels' code is typed, and whatever the
      arguments, the state the program is loaded into starts as its entry asks. -/
      theorem $checked : wholeOkWith $code $l $n $ks $bs $pg $ls $k = true := by
        asm_decide (wholeOkWith $code $l $n $ks $bs $pg $ls $k)
          (wholeWhyText $code $l $n $ks $bs $pg $ls $k)))
    cmds := cmds.push (← `(/-- The state the program is started in with given arguments is the
      one the check is of, in the world it has. -/
      theorem $startEq (args : List (List Byte)) :
          $startArgs args = startIn $code $l $n args ($startArgs args).world :=
        startArgs_eq $code $l $n args))
    if let (some q, some r, some sd) := (q?, r?, sd?) then
      cmds := cmds.push (← `(/-- The bytes the program says its data holds are the bytes its
        blocks say. -/
        theorem $saidOk : saidCheck (denBlocks $bs) $sd = true := by native_decide))
      cmds := cmds.push (← `(/-- **The program is safe, on the machine that decodes its
        instructions from memory; it ends only with a status that is as said; and wherever it
        reaches a `write`, the descriptor and the bytes offered are as said: whatever its
        arguments and whatever the world outside it holds.** -/
        theorem $safeExitsWritesIn (args : List (List Byte)) (w : World) :
            SafeMem linux (startIn $code $l $n args w) ∧
              ExitsOnly $fetch (fun c => ($q : BitVec 32 → Bool) c = true) (startIn $code $l $n args w) ∧
              WritesOnly $fetch (fun fd bytes => $r fd bytes = true)
                (startIn $code $l $n args w) :=
          whole_outputs $checked (Q := fun c => ($q : BitVec 32 → Bool) c = true) (q := ($q : BitVec 32 → Bool)) (fun _ h => h)
            (R := fun fd bytes => $r fd bytes = true) (r := $r) (fun _ _ h => h) $saidOk rfl rfl
            $lw args w))
      cmds := cmds.push (← `(/-- So the program as it is run, with any arguments, is safe. -/
        theorem $safe (args : List (List Byte)) : SafeMem linux ($startArgs args) :=
          $startEq args ▸ ($safeExitsWritesIn args ($startArgs args).world).1))
      cmds := cmds.push (← `(/-- It ends only with a status that is as said. -/
        theorem $exits (args : List (List Byte)) :
            ExitsOnly $fetch (fun c => ($q : BitVec 32 → Bool) c = true) ($startArgs args) :=
          $startEq args ▸ ($safeExitsWritesIn args ($startArgs args).world).2.1))
      cmds := cmds.push (← `(/-- And at a `write` offers only what is as said. -/
        theorem $writes (args : List (List Byte)) :
            WritesOnly $fetch (fun fd bytes => $r fd bytes = true) ($startArgs args) :=
          $startEq args ▸ ($safeExitsWritesIn args ($startArgs args).world).2.2))
      return mkNullNode cmds
    if r?.isSome then
      Macro.throwError "`writes` is said with `exits`: what the program ends with, then what it writes"
    match q? with
    | none =>
      cmds := cmds.push (← `(/-- **The program is safe, on the machine that decodes its
        instructions from memory, whatever its arguments and whatever the world outside it
        holds.** -/
        theorem $safeIn (args : List (List Byte)) (w : World) :
            SafeMem linux (startIn $code $l $n args w) :=
          whole_safe $checked rfl $lw args w))
      cmds := cmds.push (← `(/-- So the program as it is run, with any arguments, is safe. -/
        theorem $safe (args : List (List Byte)) : SafeMem linux ($startArgs args) :=
          $startEq args ▸ $safeIn args ($startArgs args).world))
    | some q =>
      cmds := cmds.push (← `(/-- **The program is safe, on the machine that decodes its
        instructions from memory, and ends only with a status that is as said: whatever its
        arguments and whatever the world outside it holds.** -/
        theorem $safeExitsIn (args : List (List Byte)) (w : World) :
            SafeMem linux (startIn $code $l $n args w) ∧
              ExitsOnly $fetch (fun c => ($q : BitVec 32 → Bool) c = true) (startIn $code $l $n args w) :=
          whole_exits $checked (Q := fun c => ($q : BitVec 32 → Bool) c = true) (q := ($q : BitVec 32 → Bool)) (fun _ h => h) rfl rfl
            $lw args w))
      cmds := cmds.push (← `(/-- So the program as it is run, with any arguments, is safe. -/
        theorem $safe (args : List (List Byte)) : SafeMem linux ($startArgs args) :=
          $startEq args ▸ ($safeExitsIn args ($startArgs args).world).1))
      cmds := cmds.push (← `(/-- And it ends only with a status that is as said. -/
        theorem $exits (args : List (List Byte)) :
            ExitsOnly $fetch (fun c => ($q : BitVec 32 → Bool) c = true) ($startArgs args) :=
          $startEq args ▸ ($safeExitsIn args ($startArgs args).world).2))
    return mkNullNode cmds

end TypedAsm.U
