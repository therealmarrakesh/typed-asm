import TypedAsm.U.Say
import TypedAsm.U.ArgsWhole
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
  and the state the program is loaded into starts as its entry asks;
* `start_eq`: the state `asm_program` starts the program in is the one the
  check is of;
* `safe_in`: the program is safe on the machine that decodes its
  instructions from memory, whatever the world outside it holds;
* `safe`: so as it is run.

With `exits q` after it, where `pg` asks at each `exit` that the status
satisfy `q`, it states instead of `safe_in` the theorem `safe_exits_in`,
that the program is safe and ends only with a status `q` holds of; and
with `safe`, the theorem `exits`.

`blocks bs` after the labels gives the blocks the program says its segments
are; where it is left out, each segment is one block of plain bytes.
`kinds ks` gives the program's kinds of block, which `pg` is to have too.
`fuel k` gives how many instructions a walk from a label may take; forty
where it is left out. -/
syntax "asm_checked " ident &" start " term:max &" stack " term:max &" program " term:max
  &" labels " term:max (&" blocks " term:max)? (&" kinds " term:max)? (&" fuel " term:max)?
  (&" exits " term:max)? : command

macro_rules
  | `(asm_checked $code start $l stack $n program $pg labels $ls $[blocks $bs?]? $[kinds $ks?]?
      $[fuel $k?]?
      $[exits $q?]?) => do
    let checked := mkIdent `checked
    let startEq := mkIdent `start_eq
    let safeIn := mkIdent `safe_in
    let safeExitsIn := mkIdent `safe_exits_in
    let safe := mkIdent `safe
    let exits := mkIdent `exits
    let start := mkIdent `start
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
    let mut cmds : Array (TSyntax `command) := #[]
    cmds := cmds.push (← `(/-- **The check**: the labels' code is typed, and the state the
      program is loaded into starts as its entry asks. -/
      theorem $checked : wholeOkWith $code $l $n $ks $bs $pg $ls $k = true := by decide +kernel))
    cmds := cmds.push (← `(/-- The state the program is started in is the one the check is of,
      in the world it has. -/
      theorem $startEq : $start = startIn $code $l $n ($start).world := by
        have e : $start = startOf $code $l $n := by
          unfold $start $prepared startOf $entry $base stackStretch
          rfl
        rw [e]
        rfl))
    match q? with
    | none =>
      cmds := cmds.push (← `(/-- **The program is safe, on the machine that decodes its
        instructions from memory, whatever the world outside it holds.** -/
        theorem $safeIn (w : World) : SafeMem linux (startIn $code $l $n w) :=
          whole_safe $checked rfl w))
      cmds := cmds.push (← `(/-- So the program as it is run is safe. -/
        theorem $safe : SafeMem linux $start := $startEq ▸ $safeIn ($start).world))
    | some q =>
      cmds := cmds.push (← `(/-- **The program is safe, on the machine that decodes its
        instructions from memory, and ends only with a status that is as said: whatever the
        world outside it holds.** -/
        theorem $safeExitsIn (w : World) :
            SafeMem linux (startIn $code $l $n w) ∧
              ExitsOnly $fetch (fun c => $q c = true) (startIn $code $l $n w) :=
          whole_exits $checked (Q := fun c => $q c = true) (q := $q) (fun _ h => h) rfl
            rfl w))
      cmds := cmds.push (← `(/-- So the program as it is run is safe. -/
        theorem $safe : SafeMem linux $start := $startEq ▸ ($safeExitsIn ($start).world).1))
      cmds := cmds.push (← `(/-- And it ends only with a status that is as said. -/
        theorem $exits : ExitsOnly $fetch (fun c => $q c = true) $start :=
          $startEq ▸ ($safeExitsIn ($start).world).2))
    return mkNullNode cmds

/-- **A label in the code of a program started with arguments**, outside
any function and with nothing pushed: the count held at the stack pointer,
the row of pointers to the arguments' text after it; and the registers and
facts said. The count is the value `argCount`. -/
def inArgs (regs : List (Reg × Val) := []) (known : List (Val × TyS) := []) : CtxS :=
  { entryArgs with regs := regsWith entryArgs.regs regs, known := entryArgs.known ++ known }

/-- How many arguments the program was handed: the value held at the stack
pointer when it starts. -/
def argCountV : Val := .bvar 0 16

/-- `asm_checked_args code start l program pg labels ls`: as `asm_checked`,
for a program that is started with arguments: `startArgs args`, which the
program's file defines as the program loaded and given a stack with the
arguments on it. It states

* `checked`: the check, run by Lean's kernel;
* `start_eq`: the state the program is started in with given arguments is
  the one the check is of;
* `safe_in`: the program is safe whatever its arguments and whatever the
  world outside it holds;
* `safe`: so as it is run, with any arguments.

With `exits q` it states `safe_exits_in`, `safe` and `exits` instead, as
`asm_checked` does. `blocks`, `kinds` and `fuel` are as there. -/
syntax "asm_checked_args " ident &" start " term:max &" program " term:max &" labels " term:max
  (&" blocks " term:max)? (&" kinds " term:max)? (&" fuel " term:max)? (&" exits " term:max)? :
  command

macro_rules
  | `(asm_checked_args $code start $l program $pg labels $ls $[blocks $bs?]? $[kinds $ks?]?
      $[fuel $k?]? $[exits $q?]?) => do
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
    let mut cmds : Array (TSyntax `command) := #[]
    cmds := cmds.push (← `(/-- **The check**: the labels' code is typed, and whatever the
      arguments, the state the program is loaded into starts as its entry asks. -/
      theorem $checked : wholeArgsOk $code $l $ks $bs $pg $ls $k = true := by decide +kernel))
    cmds := cmds.push (← `(/-- The state the program is started in with given arguments is the
      one the check is of, in the world it has. -/
      theorem $startEq (args : List (List Byte)) :
          $startArgs args = TypedAsm.U.startArgs $code $l args ($startArgs args).world := by
        unfold $startArgs $prepared TypedAsm.U.startArgs TypedAsm.U.argsState $entry $base
        rfl))
    match q? with
    | none =>
      cmds := cmds.push (← `(/-- **The program is safe, on the machine that decodes its
        instructions from memory, whatever its arguments and whatever the world outside it
        holds.** -/
        theorem $safeIn (args : List (List Byte)) (w : World) :
            SafeMem linux (TypedAsm.U.startArgs $code $l args w) :=
          whole_args_safe $checked rfl args w))
      cmds := cmds.push (← `(/-- So the program as it is run, with any arguments, is safe. -/
        theorem $safe (args : List (List Byte)) : SafeMem linux ($startArgs args) :=
          $startEq args ▸ $safeIn args ($startArgs args).world))
    | some q =>
      cmds := cmds.push (← `(/-- **The program is safe, on the machine that decodes its
        instructions from memory, and ends only with a status that is as said: whatever its
        arguments and whatever the world outside it holds.** -/
        theorem $safeExitsIn (args : List (List Byte)) (w : World) :
            SafeMem linux (TypedAsm.U.startArgs $code $l args w) ∧
              ExitsOnly $fetch (fun c => $q c = true) (TypedAsm.U.startArgs $code $l args w) :=
          whole_args_exits $checked (Q := fun c => $q c = true) (q := $q) (fun _ h => h) rfl rfl
            args w))
      cmds := cmds.push (← `(/-- So the program as it is run, with any arguments, is safe. -/
        theorem $safe (args : List (List Byte)) : SafeMem linux ($startArgs args) :=
          $startEq args ▸ ($safeExitsIn args ($startArgs args).world).1))
      cmds := cmds.push (← `(/-- And it ends only with a status that is as said. -/
        theorem $exits (args : List (List Byte)) :
            ExitsOnly $fetch (fun c => $q c = true) ($startArgs args) :=
          $startEq args ▸ ($safeExitsIn args ($startArgs args).world).2))
    return mkNullNode cmds

end TypedAsm.U
