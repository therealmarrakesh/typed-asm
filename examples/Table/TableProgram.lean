import TypedAsm

/-!
# A pointer in the data, proved safe

The data holds a record of two integers and, before it, a one-entry table
whose entry is the address of that record. The program loads the pointer
from the table and reads through it.

```asm
_start:
     mov   rdi, [rip + table]   ; the pointer the data starts with
     mov   rax, [rdi + 8]       ; the second field of what it points to
     mov   edi, eax
     mov   eax, 60              ; `exit`
     syscall

table:   dq record              ; one page after the load address
record:  dq 3, 5
```

Nothing in the code makes the table's entry a pointer: it is one because of
what the data segment contains. So the proof that the starting state is well
typed uses the entry contract's statement of the data, where the other
examples need only that their blocks hold integers.

The program is laid out for the addresses of the ELF file it can be written
to: code at `0x4000b0`, the data at `0x401000`. `lake exe table` runs it in
the model; `lake exe table --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Table

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w64 (.r_m .rdi (.rip 0xf49))),
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 8))),
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

/-- Where the code is loaded. -/
def base : BitVec 64 := BitVec.ofNat 64 Elf.codeBase

/-- Where the data is loaded: the table first, then the record. -/
def dataBase : BitVec 64 := BitVec.ofNat 64 Elf.dataBase

/-- Where the record is. -/
def recordAddr : BitVec 64 := dataBase + 8

def fetch : Fetch := Asm.fetch base code

/-- The program's bytes. -/
def image : List Byte := Asm.image base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- The load reaches the table.
#guard base + 7 + 0xf49 == dataBase

/-- The data's bytes: the address of the record, then its two fields. -/
def dataBytes : List Byte := le64 recordAddr ++ le64 3 ++ le64 5

/-- Everything in the starting state except the program itself: the data. -/
def prepared : State :=
  (State.init.loadData dataBase dataBytes .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with the program's bytes in executable
memory and `rip` at the entry. -/
def start : State :=
  { prepared.loadCode base image with rip := entry }

-- The second field of the record is 5.
#guard exitsWith 5 (runMem linux 100 start)

end Table

/-- With no arguments, runs the program on the machine with code in memory.
With `--elf FILE`, writes the program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  exeMain Table.entry.toNat Table.image Table.dataBytes Table.start args (writable := true)
