import TypedAsm.Step

/-!
# Programs with labels

A program written as a list of lines, where jumps and calls name a label
instead of giving a byte offset. The offsets are computed from the lengths
of the instructions in between.

Instruction lengths are still supplied by hand, since there is no encoder.
Jumps and calls to labels use the lengths of their 32-bit-offset encodings.
-/

namespace TypedAsm

/-- One line of a program. `L` is the type of labels. -/
inductive Asm (L : Type)
  /-- An instruction and its length in bytes. -/
  | ins (i : Instr) (len : Nat)
  /-- A label, naming the address of the next instruction. -/
  | label (l : L)
  | jmp (l : L)
  | jcc (c : Cond) (l : L)
  | call (l : L)

namespace Asm

variable {L : Type} [DecidableEq L]

/-- The number of bytes a line occupies. -/
def len : Asm L → Nat
  | .ins _ n => n
  | .label _ => 0
  | .jmp _ => 5
  | .jcc _ _ => 6
  | .call _ => 5

/-- The address of a label, in a program whose first line is at address `a`. -/
def find (l : L) : BitVec 64 → List (Asm L) → Option (BitVec 64)
  | _, [] => none
  | a, x :: rest =>
    match x with
    | .label l' => if l' = l then some a else find l a rest
    | x => find l (a + BitVec.ofNat 64 x.len) rest

/-- The address of a label in a program loaded at `base`. A label that does
not occur is given address 0. -/
def addr (prog : List (Asm L)) (base : BitVec 64) (l : L) : BitVec 64 :=
  (find l base prog).getD 0

/-- The offset from `next` to `target`. It must fit in 32 bits; this is not checked. -/
def offset (next target : BitVec 64) : BitVec 32 :=
  (target - next).setWidth 32

/-- The instructions of a program, with labels replaced by offsets. -/
def resolve (target : L → BitVec 64) : BitVec 64 → List (Asm L) → List (Instr × BitVec 64)
  | _, [] => []
  | a, x :: rest =>
    let next := a + BitVec.ofNat 64 x.len
    match x with
    | .ins i n => (i, BitVec.ofNat 64 n) :: resolve target next rest
    | .label _ => resolve target next rest
    | .jmp l => (.jmp (.rel (offset next (target l))), 5) :: resolve target next rest
    | .jcc c l => (.jcc c (offset next (target l)), 6) :: resolve target next rest
    | .call l => (.call (.rel (offset next (target l))), 5) :: resolve target next rest

/-- The instruction table of a program loaded at `base`. -/
def fetch (base : BitVec 64) (prog : List (Asm L)) : Fetch :=
  .layout base (resolve (addr prog base) base prog)

end Asm

end TypedAsm
