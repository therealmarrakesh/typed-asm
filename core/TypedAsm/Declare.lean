import TypedAsm.Run
import TypedAsm.Segments

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
label `l` with `n` eight-byte slots of stack, defines in the current
namespace

* `base`, where the program is loaded;
* `fetch`, the instruction at each address;
* `parts`, what the program puts in memory, line by line;
* `entry`, the address execution starts at;
* `prepared`, a state with the program in memory as the kernel puts it there
  and `n` writable slots of stack below `rsp`;
* `start`, that state with `rip` at the entry;

and checks that every instruction stands in an executable segment and that
every jump, call and reference to data reaches the label it names.

With `named "x"` after it, also defines `program`, the program with what
running it takes, under that name. Without `stack n` it leaves `prepared`
and `start` to be defined by hand, for a program that is started some other
way. -/
syntax "asm_program " ident &" start " term:max (&" stack " term:max)? (&" named " str)? : command

macro_rules
  | `(asm_program $code start $l $[stack $n?]? $[named $name?]?) => do
    let base := mkIdent `base
    let fetch := mkIdent `fetch
    let parts := mkIdent `parts
    let entry := mkIdent `entry
    let prepared := mkIdent `prepared
    let start := mkIdent `start
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
    if let some n := n? then
      cmds := cmds.push (← `(/-- The starting state but for `rip`: the program in memory, and
        the stack it was declared with, writable, below `rsp`. -/
        def $prepared : State :=
          ((Asm.load State.init $base $code $l).setPerm
            (0x80000000 - BitVec.ofNat 64 (8 * $n)) (BitVec.ofNat 64 (8 * $n)) .rw).setReg
              .rsp 0x80000000))
      cmds := cmds.push (← `(/-- A starting state: `prepared`, with `rip` at the entry. -/
        def $start : State := { $prepared with rip := $entry }))
      if let some name := name? then
        cmds := cmds.push (← `(/-- The program, with what running it takes. -/
          def $program : Runnable where
            name := $name
            elf := Asm.elf $base $code $l
            start := $start))
    return mkNullNode cmds

end TypedAsm
