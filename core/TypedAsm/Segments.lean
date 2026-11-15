import TypedAsm.Image
import TypedAsm.Elf
import TypedAsm.Entry

/-!
# Where a program is loaded, and the file made of it

A program is one list of lines, in segments. This module says where such a
program is loaded, what the executable file is, and what the state of a
machine that has loaded it is.

The file's layout follows from the program. What the program begins with
comes straight after the file's headers, whose size depends on how many
segments there are; every other segment starts on the next page boundary
after what comes before it, in the file and in memory alike, and is loaded
with the permission the program gave it.
-/

namespace TypedAsm

namespace Asm

variable {L : Type} [DecidableEq L]

/-- How many `segment` lines a program has: its segments after the first. -/
def segCount (prog : List (Asm L)) : Nat :=
  (prog.filter fun x => match x with
    | .segment _ => true
    | _ => false).length

/-- Where a program's first line is loaded: straight after the headers of
its executable file. -/
def base (prog : List (Asm L)) : BitVec 64 :=
  BitVec.ofNat 64 (Elf.codeBase (segCount prog))

/-- The program as a Linux executable that starts at the given label. -/
def elf (base : BitVec 64) (prog : List (Asm L)) (start : L) : List Byte :=
  match segments base prog with
  | [] => []
  | (_, _, first) :: rest => Elf.file (addr prog base start).toNat first rest

/-- A state with the program in memory: each segment's bytes where the
program puts them, with the segment's permission. -/
def load (s : State) (base : BitVec 64) (prog : List (Asm L)) : State :=
  (segments base prog).foldl (fun s g => s.loadData (BitVec.ofNat 64 g.1) g.2.2 g.2.1) s

/-- The `n` bytes a program puts in memory from a label on, whatever lines
they come from. Where it puts none, zero. -/
def dataAt (base : BitVec 64) (prog : List (Asm L)) (l : L) (n : Nat) : List Byte :=
  (List.range n).map fun k => (partsByte (parts base prog) ((addr prog base l).toNat + k)).getD 0

end Asm

end TypedAsm
