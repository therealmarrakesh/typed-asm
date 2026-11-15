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

segment readable writeable

table:   dq record
record:  dq 3, 5
```

Nothing in the code makes the table's entry a pointer: it is one because of
what the data segment contains. So the proof that the starting state is well
typed uses the entry contract's statement of the data, where the other
examples need only that their blocks hold integers.

The table and the record are named by labels, in the data segment as in
the code: the load's distance to the table, and the address the table holds,
are worked out from where the lines end up. The program is laid out for the
addresses of the ELF file it can be written to: its instructions straight
after the file's headers, its data segment on the page after them.
`lake exe table` runs it in the model; `lake exe table --elf FILE` writes an
executable that Linux can run.
-/

open TypedAsm

namespace Table

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere, and where the data is. -/
inductive Label
  | start | table | record
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ref (.mov .w64 (.r_m .rdi (.rip 0))) .table,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 8))),
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .segment .rw,
  .label .table, .quad .record,
  .label .record, .bytes (le64 3 ++ le64 5)]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

/-- Where the data is loaded: the table first, then the record. -/
def dataBase : BitVec 64 := Asm.addr code base .table

/-- Where the record is. -/
def recordAddr : BitVec 64 := Asm.addr code base .record

def fetch : Fetch := Asm.fetch base code

/-- What the program puts in memory, line by line. -/
def parts : List (Nat × Perm × List Byte) := Asm.parts base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every instruction stands in an executable segment, and the load reaches the table.
#guard Asm.wellFormed code && Asm.offsetsFit base code

/-- The data's bytes: the address of the record, then its two fields. -/
def dataBytes : List Byte := Asm.dataAt base code .table 24

/-- The starting state but for `rip`: the program in memory, and with it the
data. -/
def prepared : State :=
  (Asm.load State.init base code).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. -/
def start : State :=
  { prepared with rip := entry }

-- The second field of the record is 5.
#guard exitsWith 5 (runMem linux 100 start)

end Table

/-- The program, with what running it takes. -/
def Table.program : Runnable where
  name := "table"
  elf := Asm.elf Table.base Table.code .start
  start := Table.start
