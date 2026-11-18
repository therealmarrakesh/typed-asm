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

open Lean

variable {L : Type} [DecidableEq L]

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
  let segs := Asm.image base code l
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

/-- `asm_decide why`: the goal by `decide +kernel`; and where that fails
and the text `why` has something to say, that said in place of it. -/
syntax "asm_decide " term:max : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| asm_decide $why) => do
    try
      evalTactic (← `(tactic| decide +kernel))
    catch e =>
      let msg ← try
          unsafe Term.evalTerm String (mkConst ``String) why
        catch _ => pure ""
      if msg.isEmpty then throw e else throwError msg

/-- `asm_checked code start l stack n program pg labels ls`: for the program
`code` declared with `asm_program code start l stack n`, the checker's
program `pg` and the labels `ls`, states in the current namespace

* `checked`: the check, run by Lean's kernel: the labels' code is typed,
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

`blocks bs` after the labels gives the blocks the program says its segments
are; where it is left out, each segment is one block of plain bytes.
`kinds ks` gives the program's kinds of block, which `pg` is to have too.
`laws h`, last, gives the proof that the laws `pg`
states of the functions its author defines are so (`LawsHold pg.fns
pg.laws`); it is needed only where `pg` states any.

Where the check fails, the error says why, in the program's terms
(`wholeWhy`): what of the program as a whole is not as the check asks, or
each instruction or label that is refused and what is not so there. -/
syntax "asm_checked " ident &" start " term:max &" stack " term:max &" program " term:max
  &" labels " term:max (&" blocks " term:max)? (&" kinds " term:max)?
  (&" exits " term:max)? (&" laws " term:max)? : command

macro_rules
  | `(asm_checked $code start $l stack $n program $pg labels $ls $[blocks $bs?]? $[kinds $ks?]?
      $[exits $q?]? $[laws $lw?]?) => do
    let checked := mkIdent `checked
    let startEq := mkIdent `start_eq
    let safeIn := mkIdent `safe_in
    let safeExitsIn := mkIdent `safe_exits_in
    let safe := mkIdent `safe
    let exits := mkIdent `exits
    let startArgs := mkIdent `startArgs
    let prepared := mkIdent `prepared
    let entry := mkIdent `entry
    let base := mkIdent `base
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
    let k ← `((needFuel $pg $ls $ks))
    let mut cmds : Array (TSyntax `command) := #[]
    cmds := cmds.push (← `(/-- **The check**: the labels' code is typed, and whatever the
      arguments, the state the program is loaded into starts as its entry asks. -/
      theorem $checked : wholeOkWith $code $l $n $ks $bs $pg $ls $k = true := by
        asm_decide (wholeWhyText $code $l $n $ks $bs $pg $ls $k)))
    cmds := cmds.push (← `(/-- The state the program is started in with given arguments is the
      one the check is of, in the world it has. -/
      theorem $startEq (args : List (List Byte)) :
          $startArgs args = startIn $code $l $n args ($startArgs args).world := by
        unfold $startArgs $prepared startIn startState $entry $base
        rfl))
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
              ExitsOnly $fetch (fun c => $q c = true) (startIn $code $l $n args w) :=
          whole_exits $checked (Q := fun c => $q c = true) (q := $q) (fun _ h => h) rfl rfl
            $lw args w))
      cmds := cmds.push (← `(/-- So the program as it is run, with any arguments, is safe. -/
        theorem $safe (args : List (List Byte)) : SafeMem linux ($startArgs args) :=
          $startEq args ▸ ($safeExitsIn args ($startArgs args).world).1))
      cmds := cmds.push (← `(/-- And it ends only with a status that is as said. -/
        theorem $exits (args : List (List Byte)) :
            ExitsOnly $fetch (fun c => $q c = true) ($startArgs args) :=
          $startEq args ▸ ($safeExitsIn args ($startArgs args).world).2))
    return mkNullNode cmds

end TypedAsm.U
