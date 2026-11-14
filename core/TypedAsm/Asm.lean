import TypedAsm.Step
import TypedAsm.Encode

/-!
# Programs with labels

A program written as a list of lines, where jumps and calls name a label
instead of giving a byte offset. Every length comes from the encoder, and
the offsets are computed from the lengths of the instructions in between.
-/

namespace TypedAsm

/-- One line of a program. `L` is the type of labels. -/
inductive Asm (L : Type)
  /-- An instruction. -/
  | ins (i : Instr)
  /-- A label, naming the address of the next instruction. -/
  | label (l : L)
  | jmp (l : L)
  | jcc (c : Cond) (l : L)
  | call (l : L)

namespace Asm

variable {L : Type} [DecidableEq L]

/-- The number of bytes a line occupies. A jump or call has the same length
whatever its offset, so the length is taken from one with offset zero. -/
def len : Asm L → Nat
  | .ins i => i.length
  | .label _ => 0
  | .jmp _ => (Instr.jmp (.rel 0)).length
  | .jcc c _ => (Instr.jcc c 0).length
  | .call _ => (Instr.call (.rel 0)).length

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

/-- The offset from `next` to `target`, truncated to 32 bits. `offsetsFit`
checks that nothing was lost. -/
def offset (next target : BitVec 64) : BitVec 32 :=
  (target - next).setWidth 32

/-- Whether the 32-bit offset from `next` really reaches `target`. -/
def reaches (next target : BitVec 64) : Bool :=
  next + (offset next target).signExtend 64 == target

/-- The instructions of a program, with labels replaced by offsets. -/
def resolve (target : L → BitVec 64) : BitVec 64 → List (Asm L) → List (Instr × BitVec 64)
  | _, [] => []
  | a, x :: rest =>
    let next := a + BitVec.ofNat 64 x.len
    match x with
    | .ins i => (i, BitVec.ofNat 64 x.len) :: resolve target next rest
    | .label _ => resolve target next rest
    | .jmp l => (.jmp (.rel (offset next (target l))), BitVec.ofNat 64 x.len) :: resolve target next rest
    | .jcc c l => (.jcc c (offset next (target l)), BitVec.ofNat 64 x.len) :: resolve target next rest
    | .call l =>
      (.call (.rel (offset next (target l))), BitVec.ofNat 64 x.len) :: resolve target next rest

/-- Whether every jump and call in the lines from address `a` reaches its target. -/
def offsetsFitFrom (target : L → BitVec 64) : BitVec 64 → List (Asm L) → Bool
  | _, [] => true
  | a, x :: rest =>
    let next := a + BitVec.ofNat 64 x.len
    (match x with
      | .jmp l | .jcc _ l | .call l => reaches next (target l)
      | _ => true) && offsetsFitFrom target next rest

/-- Whether every jump and call in a program loaded at `base` reaches its
target: that is, whether each offset fits in 32 bits. A program can check
this about itself with `#guard`. -/
def offsetsFit (base : BitVec 64) (prog : List (Asm L)) : Bool :=
  offsetsFitFrom (addr prog base) base prog

/-- The instruction table of a program loaded at `base`. -/
def fetch (base : BitVec 64) (prog : List (Asm L)) : Fetch :=
  .layout base (resolve (addr prog base) base prog)

end Asm

end TypedAsm
