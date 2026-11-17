import TypedAsm.U.Say
import TypedAsm.EndToEnd

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
`fuel k` gives how many instructions a walk from a label may take; forty
where it is left out. -/
syntax "asm_checked " ident &" start " term:max &" stack " term:max &" program " term:max
  &" labels " term:max (&" blocks " term:max)? (&" fuel " term:max)? (&" exits " term:max)? :
  command

macro_rules
  | `(asm_checked $code start $l stack $n program $pg labels $ls $[blocks $bs?]? $[fuel $k?]?
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
    let mut cmds : Array (TSyntax `command) := #[]
    cmds := cmds.push (← `(/-- **The check**: the labels' code is typed, and the state the
      program is loaded into starts as its entry asks. -/
      theorem $checked : wholeOkWith $code $l $n $bs $pg $ls $k = true := by decide +kernel))
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
          whole_safe $checked (KindsOk.none _) w))
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
            (KindsOk.none _) w))
      cmds := cmds.push (← `(/-- So the program as it is run is safe. -/
        theorem $safe : SafeMem linux $start := $startEq ▸ ($safeExitsIn ($start).world).1))
      cmds := cmds.push (← `(/-- And it ends only with a status that is as said. -/
        theorem $exits : ExitsOnly $fetch (fun c => $q c = true) $start :=
          $startEq ▸ ($safeExitsIn ($start).world).2))
    return mkNullNode cmds

end TypedAsm.U
