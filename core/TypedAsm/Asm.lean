import TypedAsm.Step
import TypedAsm.Encode
import TypedAsm.Lookup

/-!
# Programs with labels

A program written as a list of lines, where jumps and calls name a label
instead of giving a byte offset, and so do instructions that reach data.
Every length comes from the encoder, and the offsets are computed from the
lengths of what lies in between.

A program is made of segments. The lines before the first `segment` line are
a segment of their own, readable and executable. Every `segment` line begins
another, loaded from the next page boundary on with the permission it names.
There may be any number, in any order. Instructions stand in executable
segments; data may stand in any; a label may stand anywhere, and names the
address of whatever follows it.
-/

namespace TypedAsm

/-- One line of a program. `L` is the type of labels. -/
inductive Asm (L : Type)
  /-- An instruction. -/
  | ins (i : Instr)
  /-- A label, naming the address of the next line. -/
  | label (l : L)
  | jmp (l : L)
  | jcc (c : Cond) (l : L)
  | call (l : L)
  /-- An instruction that reaches memory relative to `rip`, aimed at a label
  or so many bytes past it: `mov rax, [table]`, `lea rdi, [buffer]`,
  `add dword ptr [record + 12], 1`. The distance is worked out from where the
  two end up. -/
  | ref (i : Instr) (l : L) (past : BitVec 64 := 0)
  /-- The start of a segment with the given permission: `.rx` for
  instructions, `.ro` for data that is only read, `.rw` for data that is
  written. What follows is loaded from the next page boundary on. -/
  | segment (p : Perm)
  /-- Zero bytes up to the next address that is a multiple of `n`. -/
  | align (n : Nat)
  /-- Data, byte for byte as written. -/
  | bytes (bs : List Byte)
  /-- Eight bytes holding the address of a label. -/
  | quad (l : L)
  /-- So many bytes, all zero. -/
  | space (n : Nat)

namespace Asm

variable {L : Type} [DecidableEq L]

/-- The number of bytes a line occupies, for a line whose size does not
depend on where it is. A jump or call has the same length whatever its
offset, so the length is taken from one with offset zero. -/
def len : Asm L → Nat
  | .ins i => i.length
  | .label _ => 0
  | .jmp _ => (Instr.jmp (.rel 0)).length
  | .jcc c _ => (Instr.jcc c 0).length
  | .call _ => (Instr.call (.rel 0)).length
  | .ref i _ _ => i.length
  | .segment _ => 0
  | .align _ => 0
  | .bytes bs => bs.length
  | .quad _ => 8
  | .space n => n

/-- The first page boundary at or after an address. -/
def pageUp (a : Nat) : Nat :=
  (a + 4095) / 4096 * 4096

/-- The first multiple of `n` at or after an address. -/
def alignUp (a n : Nat) : Nat :=
  if n = 0 then a else (a + (n - 1)) / n * n

/-- Where the line after `x` starts, if `x` starts at `a`: past its bytes;
for the start of a segment, at the next page boundary; for an alignment, at
the next multiple. Addresses are plain numbers while a program is laid out. -/
def next (a : Nat) : Asm L → Nat
  | .segment _ => pageUp a
  | .align n => alignUp a n
  | x => a + x.len

/-- The permission of the segment the line after `x` is in, if `x` is in a
segment with permission `p`. -/
def perm (p : Perm) : Asm L → Perm
  | .segment q => q
  | _ => p

/-- The address of a label, in a program whose first line is at address `a`. -/
def find (l : L) : Nat → List (Asm L) → Option Nat
  | _, [] => none
  | a, x :: rest =>
    match x with
    | .label l' => if l' = l then some a else find l a rest
    | x => find l (next a x) rest

/-- The address of a label in a program loaded at `base`. A label that does
not occur is given address 0. -/
def addr (prog : List (Asm L)) (base : BitVec 64) (l : L) : BitVec 64 :=
  BitVec.ofNat 64 ((find l base.toNat prog).getD 0)

/-- The offset from `next` to `target`, truncated to 32 bits. `offsetsFit`
checks that nothing was lost. -/
def offset (next target : BitVec 64) : BitVec 32 :=
  (target - next).setWidth 32

/-- Whether the 32-bit offset from `next` really reaches `target`. -/
def reaches (next target : BitVec 64) : Bool :=
  next + (offset next target).signExtend 64 == target

/-- The instruction a line stands for, if it is one, with its label replaced
by the offset from `nxt`, where the line after it starts. -/
def instr (target : L → BitVec 64) (nxt : BitVec 64) : Asm L → Option Instr
  | .ins i => some i
  | .jmp l => some (.jmp (.rel (offset nxt (target l))))
  | .jcc c l => some (.jcc c (offset nxt (target l)))
  | .call l => some (.call (.rel (offset nxt (target l))))
  | .ref i l past => some (i.aim (offset nxt (target l + past)))
  | _ => none

/-- The bytes a line starting at `a` comes to: an instruction's encoding,
data as written, a label's address, or zeros. -/
def lineBytes (target : L → BitVec 64) (a : Nat) (x : Asm L) : List Byte :=
  match x with
  | .bytes bs => bs
  | .quad l => le64 (target l)
  | .space n => List.replicate n 0
  | .align n => List.replicate (alignUp a n - a) 0
  | x =>
    match instr target (BitVec.ofNat 64 (next a x)) x with
    | some i => i.encode
    | none => []

/-- The instructions of the lines from address `a`, in a segment with
permission `p`: each with its address and its length. Only what stands in an
executable segment is an instruction the machine may be sent to. -/
def tableFrom (target : L → BitVec 64) : Nat → Perm → List (Asm L) → List (Nat × Instr × BitVec 64)
  | _, _, [] => []
  | a, p, x :: rest =>
    let more := tableFrom target (next a x) (perm p x) rest
    match instr target (BitVec.ofNat 64 (next a x)) x with
    | some i => if p = .rx then (a, i, BitVec.ofNat 64 i.length) :: more else more
    | none => more

/-- The instructions of a program loaded at `base`, each with its address
and its length. -/
def table (base : BitVec 64) (prog : List (Asm L)) : List (Nat × Instr × BitVec 64) :=
  tableFrom (addr prog base) base.toNat .rx prog

/-- The instruction table of a program loaded at `base`. -/
def fetch (base : BitVec 64) (prog : List (Asm L)) : Fetch :=
  fun a => Lookup.first (table base prog) a.toNat

/-- What the lines from address `a` put in memory, line by line: where, with
what permission, and which bytes. -/
def partsFrom (target : L → BitVec 64) : Nat → Perm → List (Asm L) → List (Nat × Perm × List Byte)
  | _, _, [] => []
  | a, p, x :: rest => (a, p, lineBytes target a x) :: partsFrom target (next a x) (perm p x) rest

/-- What a program loaded at `base` puts in memory, line by line: where,
with what permission, and which bytes. This is all that a program's being
loaded means, and it is stated for each line by itself: nothing is said
about the gaps between segments. -/
def parts (base : BitVec 64) (prog : List (Asm L)) : List (Nat × Perm × List Byte) :=
  partsFrom (addr prog base) base.toNat .rx prog

/-- Whether every jump, call and reference to data in the lines from address
`a` reaches its target. -/
def offsetsFitFrom (target : L → BitVec 64) : Nat → List (Asm L) → Bool
  | _, [] => true
  | a, x :: rest =>
    let nxt := next a x
    (match x with
      | .jmp l | .jcc _ l | .call l => reaches (BitVec.ofNat 64 nxt) (target l)
      | .ref _ l past => reaches (BitVec.ofNat 64 nxt) (target l + past)
      | _ => true) && offsetsFitFrom target nxt rest

/-- Whether every jump, call and reference to data in a program loaded at
`base` reaches its target: that is, whether each offset fits in 32 bits. A
program can check this about itself with `#guard`. -/
def offsetsFit (base : BitVec 64) (prog : List (Asm L)) : Bool :=
  offsetsFitFrom (addr prog base) base.toNat prog

/-- Whether the lines of a segment with permission `p`, and of those after
it, are laid out as they must be. -/
def wellFormedFrom : Perm → List (Asm L) → Bool
  | _, [] => true
  | p, x :: rest =>
    (match x with
      | .segment q => q != .none
      | .align n => n != 0
      | .ins _ | .jmp _ | .jcc _ _ | .call _ | .ref _ _ _ => p == .rx
      | _ => true) && wellFormedFrom (perm p x) rest

/-- Whether a program is laid out as it must be: every instruction stands in
an executable segment, every segment can at least be read, and nothing is
aligned to a multiple of zero. No segment is both writable and executable:
there is no such permission. A program can check this about itself with
`#guard`. -/
def wellFormed (prog : List (Asm L)) : Bool :=
  wellFormedFrom .rx prog

/-- The segments of the lines from address `a`, when the lines so far belong
to the segment `cur`: where each segment is loaded, its permission, and its
bytes. -/
def segmentsFrom (target : L → BitVec 64) :
    Nat → Nat × Perm × List Byte → List (Asm L) → List (Nat × Perm × List Byte)
  | _, cur, [] => [cur]
  | a, cur, x :: rest =>
    match x with
    | .segment q => cur :: segmentsFrom target (pageUp a) (pageUp a, q, []) rest
    | x => segmentsFrom target (next a x) (cur.1, cur.2.1, cur.2.2 ++ lineBytes target a x) rest

/-- The segments of a program loaded at `base`: where each is loaded, its
permission, and its bytes. The first is the one the program begins in,
readable and executable, which is there even if it is empty. -/
def segments (base : BitVec 64) (prog : List (Asm L)) : List (Nat × Perm × List Byte) :=
  segmentsFrom (addr prog base) base.toNat (base.toNat, .rx, []) prog

end Asm

end TypedAsm
