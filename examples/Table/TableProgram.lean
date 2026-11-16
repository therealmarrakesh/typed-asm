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

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it the
-- data.
asm_program code start .start stack 0 named "table"

/-- The data's bytes: the address of the record, then its two fields. -/
def dataBytes : List Byte := Asm.dataAt base code .table 24

-- The second field of the record is 5.
#guard exitsWith 5 (runMem linux 100 start)

end Table

