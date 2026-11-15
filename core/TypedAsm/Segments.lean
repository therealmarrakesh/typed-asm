import TypedAsm.Image
import TypedAsm.Elf
import TypedAsm.Entry

/-!
# A program's segments, and the file made of them

A program is one list of lines: its instructions, then its data segments.
This module says where such a program is loaded, what its data comes to byte
for byte, and what the executable file is: one loadable segment for the
instructions and one for each data segment, with the permissions the program
gave it.

The file's layout follows from the program. The instructions come straight
after the file's headers, whose size depends on how many segments there are;
each data segment starts on the next page boundary after what comes before
it, in the file and in memory alike.
-/

namespace TypedAsm

namespace Asm

variable {L : Type} [DecidableEq L]

/-- How many data segments a program has. -/
def segCount (prog : List (Asm L)) : Nat :=
  (prog.filter fun x => match x with
    | .segment _ => true
    | _ => false).length

/-- Where a program's first instruction is loaded: straight after the
headers of its executable file. -/
def base (prog : List (Asm L)) : BitVec 64 :=
  BitVec.ofNat 64 (Elf.codeBaseFor (segCount prog))

/-- Where a program's data begins: the start of its first data segment. -/
def dataBase (base : BitVec 64) (prog : List (Asm L)) : BitVec 64 :=
  match segments base prog with
  | [] => 0
  | (b, _, _) :: _ => b

/-- A program's data, byte for byte from where it begins to the end of its
last segment. Between one segment's end and the next one's start, on a page
boundary, the bytes are zero: that is what the file holds there, and so what
is in memory. -/
def dataImage (base : BitVec 64) (prog : List (Asm L)) : List Byte :=
  match segments base prog with
  | [] => []
  | (b, _, bs) :: rest =>
    rest.foldl (fun acc (b', _, bs') =>
      acc ++ List.replicate (b'.toNat - b.toNat - acc.length) 0 ++ bs') bs

/-- The program as a Linux executable. -/
def elf (base : BitVec 64) (prog : List (Asm L)) (entry : Nat) : List Byte :=
  Elf.fileOf entry (image base prog) ((segments base prog).map fun (b, w, bs) => (b.toNat, w, bs))

/-- A state with the program's data segments placed in memory, each readable
and writable or readable only, as the program says. -/
def loadSegments (s : State) (base : BitVec 64) (prog : List (Asm L)) : State :=
  (segments base prog).foldl (fun s (b, w, bs) => s.loadData b bs (if w then .rw else .ro)) s

end Asm

/-- Memory holds these bytes from an address on, as found by looking at each. -/
def State.dataCheck (s : State) (a : BitVec 64) (bytes : List Byte) : Bool :=
  (List.range bytes.length).all fun k => s.mem (a + BitVec.ofNat 64 k) == bytes.getD k 0

/-- A check of each byte shows that memory holds the data. This serves for a
starting state however it was made. -/
theorem State.hasData_of_check {s : State} {a : BitVec 64} {bytes : List Byte}
    (h : s.dataCheck a bytes = true) : s.HasData a bytes := by
  intro k hk
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [beq_iff_eq] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

end TypedAsm
