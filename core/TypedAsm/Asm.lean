import TypedAsm.Step
import TypedAsm.Encode

/-!
# Programs with labels

A program written as a list of lines, where jumps and calls name a label
instead of giving a byte offset, and so do instructions that reach data.
Every length comes from the encoder, and the offsets are computed from the
lengths of what lies in between.

The instructions come first. After them come the program's data segments:
each begins with a `segment` line, is loaded from the next page boundary on,
readable and perhaps writable, and holds data lines. A label may stand
anywhere, and names the address of whatever follows it.
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
  /-- An instruction that reaches memory relative to `rip`, aimed at a label:
  `mov rax, [table]`, `lea rdi, [buffer]`. The distance is worked out from
  where the two end up. -/
  | ref (i : Instr) (l : L)
  /-- The start of a data segment, readable and writable or readable only.
  What follows is loaded from the next page boundary on. -/
  | segment (writable : Bool)
  /-- Data, byte for byte as written. -/
  | bytes (bs : List Byte)
  /-- Eight bytes holding the address of a label. -/
  | quad (l : L)
  /-- So many bytes, all zero. -/
  | space (n : Nat)

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
  | .ref i _ => i.length
  | .segment _ => 0
  | .bytes bs => bs.length
  | .quad _ => 8
  | .space n => n

/-- The first page boundary at or after an address. -/
def pageUp (a : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((a.toNat + 4095) / 4096 * 4096)

/-- Where the line after `x` starts, if `x` starts at `a`: past its bytes,
or for the start of a segment, at the next page boundary. -/
def next (a : BitVec 64) : Asm L → BitVec 64
  | .segment _ => pageUp a
  | x => a + BitVec.ofNat 64 x.len

/-- The address of a label, in a program whose first line is at address `a`. -/
def find (l : L) : BitVec 64 → List (Asm L) → Option (BitVec 64)
  | _, [] => none
  | a, x :: rest =>
    match x with
    | .label l' => if l' = l then some a else find l a rest
    | x => find l (next a x) rest

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

/-- The instructions of a program, with labels replaced by offsets. They are
the lines up to the first data segment: nothing after that is an instruction
the machine may be sent to. -/
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
    | .ref i l =>
      (i.aim (offset next (target l)), BitVec.ofNat 64 x.len) :: resolve target next rest
    | .segment _ | .bytes _ | .quad _ | .space _ => []

/-- Whether every jump, call and reference to data in the lines from address
`a` reaches its target. -/
def offsetsFitFrom (target : L → BitVec 64) : BitVec 64 → List (Asm L) → Bool
  | _, [] => true
  | a, x :: rest =>
    let nxt := next a x
    (match x with
      | .jmp l | .jcc _ l | .call l | .ref _ l => reaches nxt (target l)
      | _ => true) && offsetsFitFrom target nxt rest

/-- Whether every jump, call and reference to data in a program loaded at
`base` reaches its target: that is, whether each offset fits in 32 bits. A
program can check this about itself with `#guard`. -/
def offsetsFit (base : BitVec 64) (prog : List (Asm L)) : Bool :=
  offsetsFitFrom (addr prog base) base prog

/-- The instruction table of a program loaded at `base`. -/
def fetch (base : BitVec 64) (prog : List (Asm L)) : Fetch :=
  .layout base (resolve (addr prog base) base prog)

/-- Whether a line is one of the instructions' part of a program: an
instruction, a jump, a call or a label. -/
def isCode : Asm L → Bool
  | .ins _ | .label _ | .jmp _ | .jcc _ _ | .call _ | .ref _ _ => true
  | _ => false

/-- Whether a line may stand in a data segment: data, or a label. -/
def isData : Asm L → Bool
  | .label _ | .bytes _ | .quad _ | .space _ | .segment _ => true
  | _ => false

/-- Whether a program is laid out as it must be: its instructions first, and
from the first `segment` line on nothing but data, labels and further
segments. A program can check this about itself with `#guard`. -/
def wellFormed (prog : List (Asm L)) : Bool :=
  let data := prog.dropWhile isCode
  (match data with
    | [] => true
    | x :: _ => match x with
      | .segment _ => true
      | _ => false) && data.all isData

/-- The data segments of the lines from address `a`, when the lines so far
belong to the segment `cur`, if any: where each segment is loaded, whether it
is writable, and its bytes. -/
def segmentsFrom (target : L → BitVec 64) :
    BitVec 64 → Option (BitVec 64 × Bool × List Byte) → List (Asm L) →
      List (BitVec 64 × Bool × List Byte)
  | _, cur, [] => cur.toList
  | a, cur, x :: rest =>
    let nxt := next a x
    match x with
    | .segment w => cur.toList ++ segmentsFrom target nxt (some (nxt, w, [])) rest
    | x =>
      let more : List Byte := match x with
        | .bytes bs => bs
        | .quad l => le64 (target l)
        | .space n => List.replicate n 0
        | _ => []
      segmentsFrom target nxt (cur.map fun (b, w, bs) => (b, w, bs ++ more)) rest

/-- The data segments of a program loaded at `base`. -/
def segments (base : BitVec 64) (prog : List (Asm L)) : List (BitVec 64 × Bool × List Byte) :=
  segmentsFrom (addr prog base) base none prog

end Asm

end TypedAsm
