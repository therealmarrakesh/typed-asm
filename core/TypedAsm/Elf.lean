import TypedAsm.Encode

/-!
# A file Linux can run

A minimal static ELF executable: one segment readable and executable,
holding the file's headers followed by the code, and then data segments,
each read-only or writable. Nothing here is proved; it is a container format.

`Elf.fileOf` writes a file with any number of data segments, each loaded
where the program says. `Elf.file` is the older form with exactly one, at
fixed addresses: code at `Elf.codeBase` and data at `Elf.dataBase`, one page
later.
-/

namespace TypedAsm.Elf

/-- Where the file is loaded. -/
def loadBase : Nat := 0x400000

/-- The size of the ELF header and the two program headers. -/
def headerSize : Nat := 64 + 2 * 56

/-- The address of the first byte of code. -/
def codeBase : Nat := loadBase + headerSize

/-- The address of the first byte of data. -/
def dataBase : Nat := loadBase + 0x1000

def le16 (n : Nat) : List Byte := [byte (n % 256), byte (n / 256 % 256)]

def le32n (n : Nat) : List Byte := le32 (BitVec.ofNat 32 n)

def le64n (n : Nat) : List Byte := le64 (BitVec.ofNat 64 n)

/-- One loadable segment: its permission flags (4 = read, 2 = write, 1 =
execute), where it sits in the file, where it is loaded, and its size. -/
def programHeader (flags offset vaddr size : Nat) : List Byte :=
  le32n 1 ++ le32n flags ++ le64n offset ++ le64n vaddr ++ le64n vaddr ++ le64n size ++ le64n size
    ++ le64n 0x1000

/-- The ELF header for a 64-bit x86-64 executable with two segments. -/
def header (entry : Nat) : List Byte :=
  [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ++ le16 2 ++ le16 0x3E ++ le32n 1 ++ le64n entry ++ le64n 64 ++ le64n 0 ++ le32n 0
    ++ le16 64 ++ le16 56 ++ le16 2 ++ le16 64 ++ le16 0 ++ le16 0

/-- The bytes of an executable file whose code and data are these. Execution
starts at `entry`. The code must fit in the first page after the headers. -/
def file (entry : Nat) (code data : List Byte) (writable : Bool := false) : List Byte :=
  let text := header entry
    ++ programHeader 5 0 loadBase (headerSize + code.length)
    ++ programHeader (if writable then 6 else 4) 0x1000 dataBase data.length
    ++ code
  text ++ List.replicate (0x1000 - text.length) 0 ++ data

/-- The size of the ELF header and the program headers of a file with `n`
data segments: one program header for the instructions and one for each. -/
def headerSizeFor (n : Nat) : Nat := 64 + (n + 1) * 56

/-- The address of the first byte of code in a file with `n` data segments. -/
def codeBaseFor (n : Nat) : Nat := loadBase + headerSizeFor n

/-- The ELF header for a 64-bit x86-64 executable with `n` data segments. -/
def headerFor (entry n : Nat) : List Byte :=
  [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ++ le16 2 ++ le16 0x3E ++ le32n 1 ++ le64n entry ++ le64n 64 ++ le64n 0 ++ le32n 0
    ++ le16 64 ++ le16 56 ++ le16 (n + 1) ++ le16 64 ++ le16 0 ++ le16 0

/-- The bytes of an executable file whose instructions are `code` and whose
data segments are `segs`: for each, where it is loaded, whether it is
writable, and its bytes. The instructions follow the headers; each data
segment sits in the file as far from the start as it is loaded from
`loadBase`, so it must be loaded on a page boundary above everything before
it. Execution starts at `entry`. -/
def fileOf (entry : Nat) (code : List Byte) (segs : List (Nat × Bool × List Byte)) : List Byte :=
  let n := segs.length
  let head := headerFor entry n
    ++ programHeader 5 0 loadBase (headerSizeFor n + code.length)
    ++ (segs.flatMap fun (va, w, bs) =>
        programHeader (if w then 6 else 4) (va - loadBase) va bs.length)
    ++ code
  segs.foldl (fun acc (va, _, bs) =>
    acc ++ List.replicate (va - loadBase - acc.length) 0 ++ bs) head

end TypedAsm.Elf
