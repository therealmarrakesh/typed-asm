import TypedAsm.Run
import TypedAsm.Segments
import TypedAsm.Data

/-!
# What every program declares

A program is a list of lines and the label it starts at. Where it is loaded,
what it puts in memory, where execution begins and the state it starts in
all follow from those two, and are the same few definitions for every
program. `asm_program` makes them.
-/

namespace TypedAsm

open Lean

/-- `asm_program code start l stack n`: for the program `code`, started at
label `l` with `n` eight-byte slots of stack (none where `stack n` is left
out), defines in the current namespace

* `base`, where the program is loaded;
* `fetch`, the instruction at each address;
* `parts`, what the program puts in memory, line by line;
* `entry`, the address execution starts at;
* `prepared`, a state with the program in memory as the kernel puts it
  there;
* `startArgs args`, the state the kernel starts the program in when it is
  given those arguments, its own name by custom the first: `prepared`, the
  arguments on the stack as the kernel lays them out, how many they are at
  `rsp`, `n` writable slots of stack below, and `rip` at the entry;
* `start`, that state with no arguments;

and checks that every instruction stands in an executable segment and that
every jump, call and reference to data reaches the label it names.

With `named "x"` after it, also defines `program`, the program with what
running it takes, under that name. -/
syntax "asm_program " ident &" start " term:max (&" stack " term:max)? (&" named " str)? : command

macro_rules
  | `(asm_program $code start $l $[stack $n?]? $[named $name?]?) => do
    let base := mkIdent `base
    let fetch := mkIdent `fetch
    let parts := mkIdent `parts
    let entry := mkIdent `entry
    let prepared := mkIdent `prepared
    let start := mkIdent `start
    let startArgs := mkIdent `startArgs
    let program := mkIdent `program
    let mut cmds : Array (TSyntax `command) := #[]
    cmds := cmds.push (← `(/-- Where the program is loaded. -/
      def $base : BitVec 64 := Asm.base $code))
    cmds := cmds.push (← `(/-- The instruction at each address. -/
      def $fetch : Fetch := Asm.fetch $base $code))
    cmds := cmds.push (← `(/-- What the program puts in memory, line by line. -/
      def $parts : List (Nat × Perm × List Byte) := Asm.parts $base $code))
    cmds := cmds.push (← `(/-- The address execution starts at. -/
      def $entry : BitVec 64 := Asm.addr $code $base $l))
    cmds := cmds.push (← `(#guard Asm.wellFormed $code && Asm.offsetsFit $base $code))
    let n ← match n? with
      | some n => pure n
      | none => `(0)
    cmds := cmds.push (← `(/-- The program in memory, as the kernel puts it there. -/
      def $prepared : State := Asm.load State.init $base $code $l))
    cmds := cmds.push (← `(/-- The state the program starts in, given these arguments: the
      program in memory, the arguments on the stack with how many they are at `rsp`, the
      stack it was declared with below, and `rip` at the entry. -/
      def $startArgs (args : List (List Byte)) : State :=
        { State.withArgs $prepared $n args with rip := $entry }))
    cmds := cmds.push (← `(/-- The state it starts in given no arguments. -/
      def $start : State := $startArgs []))
    if let some name := name? then
      cmds := cmds.push (← `(/-- The program, with what running it takes. -/
        def $program : Runnable where
          name := $name
          elf := Asm.elf $base $code $l
          startArgs := $startArgs))
    return mkNullNode cmds

end TypedAsm
