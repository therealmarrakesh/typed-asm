import TypedAsm.U.Say
import TypedAsm.Runs

/-!
# What every checked program states

A program declared with `asm_program`, its labels said, is checked by one
computation; and what the check shows is the same few theorems for every
program. `asm_checked` states them.
-/

namespace TypedAsm.U

open Lean

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
`fuel k` gives how many instructions a walk from a label may take; forty
where it is left out. `laws h`, last, gives the proof that the laws `pg`
states of the functions its author defines are so (`LawsHold pg.fns
pg.laws`); it is needed only where `pg` states any. -/
syntax "asm_checked " ident &" start " term:max &" stack " term:max &" program " term:max
  &" labels " term:max (&" blocks " term:max)? (&" kinds " term:max)? (&" fuel " term:max)?
  (&" exits " term:max)? (&" laws " term:max)? : command

macro_rules
  | `(asm_checked $code start $l stack $n program $pg labels $ls $[blocks $bs?]? $[kinds $ks?]?
      $[fuel $k?]? $[exits $q?]? $[laws $lw?]?) => do
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
    let k ← match k? with
      | some k => pure k
      | none => `(40)
    let bs ← match bs? with
      | some bs => pure bs
      | none => `((blocksOf $code $l))
    let ks ← match ks? with
      | some ks => pure ks
      | none => `(([] : List (Nat × ShapeS)))
    let lw ← match lw? with
      | some lw => pure lw
      | none => `((LawsHold.nil _))
    let mut cmds : Array (TSyntax `command) := #[]
    cmds := cmds.push (← `(/-- **The check**: the labels' code is typed, and whatever the
      arguments, the state the program is loaded into starts as its entry asks. -/
      theorem $checked : wholeOkWith $code $l $n $ks $bs $pg $ls $k = true := by decide +kernel))
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
