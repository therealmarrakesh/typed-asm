import TypedAsm.Encode
import TypedAsm.State

/-!
# A file Linux can run

A minimal static ELF executable made of loadable segments. The first is
readable and executable, and holds the file's headers followed by whatever
the program begins with; each of the others is loaded where the program
says, with the permission the program gave it. Nothing here is proved; it is
a container format.
-/

namespace TypedAsm.Elf

/-- Where the file is loaded. -/
def loadBase : Nat := 0x400000

def le16 (n : Nat) : List Byte := [byte (n % 256), byte (n / 256 % 256)]

def le32n (n : Nat) : List Byte := le32 (BitVec.ofNat 32 n)

def le64n (n : Nat) : List Byte := le64 (BitVec.ofNat 64 n)

/-- One loadable segment: its permission flags (4 = read, 2 = write, 1 =
execute), where it sits in the file, where it is loaded, and its size. -/
def programHeader (flags offset vaddr size : Nat) : List Byte :=
  le32n 1 ++ le32n flags ++ le64n offset ++ le64n vaddr ++ le64n vaddr ++ le64n size ++ le64n size
    ++ le64n 0x1000

/-- A permission as the flags of a segment. -/
def flags : Perm → Nat
  | .none => 0
  | .ro => 4
  | .rw => 6
  | .rx => 5

/-- The size of the ELF header and the program headers of a file with `n`
segments after the first: one program header for each segment. -/
def headerSize (n : Nat) : Nat := 64 + (n + 1) * 56

/-- The address of the first byte after the headers, where the program
begins, in a file with `n` segments after the first. -/
def codeBase (n : Nat) : Nat := loadBase + headerSize n

/-- The ELF header for a 64-bit x86-64 executable with `n` segments after
the first. -/
def header (entry n : Nat) : List Byte :=
  [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ++ le16 2 ++ le16 0x3E ++ le32n 1 ++ le64n entry ++ le64n 64 ++ le64n 0 ++ le32n 0
    ++ le16 64 ++ le16 56 ++ le16 (n + 1) ++ le16 64 ++ le16 0 ++ le16 0

/-- Everything in the file before the program: the ELF header and one
program header for each segment. The kernel maps whole pages of the file,
so these bytes are in memory too, in the page the program begins in. -/
def headers (entry firstLen : Nat) (segs : List (Nat × Perm × List Byte)) : List Byte :=
  header entry segs.length
    ++ programHeader 5 0 loadBase (headerSize segs.length + firstLen)
    ++ (segs.flatMap fun (va, p, bs) => programHeader (flags p) (va - loadBase) va bs.length)

theorem programHeader_length (f o v n : Nat) : (programHeader f o v n).length = 56 := by
  simp [programHeader, le32n, le64n, le32, le64]

theorem header_length (entry n : Nat) : (header entry n).length = 64 := by
  simp [header, le16, le32n, le64n, le32, le64]

/-- The headers are as long as `headerSize` says. -/
theorem headers_length (entry firstLen : Nat) (segs : List (Nat × Perm × List Byte)) :
    (headers entry firstLen segs).length = headerSize segs.length := by
  have hf : ∀ l : List (Nat × Perm × List Byte),
      (l.flatMap fun (va, p, bs) => programHeader (flags p) (va - loadBase) va bs.length).length
        = l.length * 56 := by
    intro l
    induction l with
    | nil => rfl
    | cons x rest ih =>
      rw [List.flatMap_cons, List.length_append, ih, programHeader_length, List.length_cons]
      omega
  unfold headers headerSize
  rw [List.length_append, List.length_append, header_length, programHeader_length, hf]
  omega

/-- The bytes of an executable file that begins with `first`, straight after
the headers, and whose other segments are `segs`: for each, where it is
loaded, its permission, and its bytes. Each of those sits in the file as far
from the start as it is loaded from `loadBase`, so it must be loaded on a
page boundary above everything before it. Execution starts at `entry`. -/
def file (entry : Nat) (first : List Byte) (segs : List (Nat × Perm × List Byte)) : List Byte :=
  segs.foldl (fun acc (va, _, bs) =>
    acc ++ List.replicate (va - loadBase - acc.length) 0 ++ bs)
    (headers entry first.length segs ++ first)

end TypedAsm.Elf
