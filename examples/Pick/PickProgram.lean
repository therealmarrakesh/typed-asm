import TypedAsm

/-!
# A table at a fixed address, proved safe

Exits with one of four numbers, chosen by how many arguments it is given.
The numbers are a table in the data, and the program reaches into it by the
table's address and an index, with no register holding a pointer to it:

```asm
_start:
     mov   rcx, [rsp]             ; how many arguments
     cmp   rcx, 4
     jae   out                    ; no such entry
     mov   rdi, [table + rcx*8]   ; the entry for that many
     mov   eax, 60                ; `exit`
     syscall
out:
     xor   edi, edi
     mov   eax, 60
     syscall

segment readable

table:   dq 10, 20, 30, 40
```

What makes the load safe is the comparison before it: where the load is
reached the count is below four, so the eight bytes it reads are inside the
table. Without the comparison the program is not typed.

The address of the table is part of the instruction, worked out from where
the table ends up. `lake exe pick -- ARG...` runs the program in the model;
`lake exe pick --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Pick

/-! ## The program -/

inductive Label
  | start | out | table
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w64 (.r_m .rcx (.sib (some .rsp) none 0))),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rcx) 4)),
  .jcc .ae .out,
  .ref (.mov .w64 (.r_m .rdi (.sib none (some (.rcx, .s8)) 0))) .table,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .out,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .segment .ro,
  .label .table, .bytes (le64 10 ++ le64 20 ++ le64 30 ++ le64 40)]

-- Where the program is loaded, what it puts in memory, where it starts,
-- all from the lines above.
asm_program code start .start

/-- A starting state but for the stack and `rip`: the program in memory, and
with it the table. -/
def prepared : State :=
  Asm.load State.init base code .start

/-- A starting state: `prepared`, given a stack that holds the arguments, with
`rip` at the entry. The first argument is by custom the program's own name. -/
def startArgs (args : List (List Byte)) : State :=
  { prepared.withArgs 0 args with rip := entry }

/-- That state for arguments given as strings. -/
def startWith (args : List String) : State :=
  startArgs (args.map bytesOf)

/-! ## Running it -/

-- The entry for as many arguments as there are, the program's name among them.
#guard exitsWith 20 (runMem linux 100 (startWith ["pick"]))
#guard exitsWith 40 (runMem linux 100 (startWith ["pick", "a", "b"]))

-- With four or more there is no entry, and it exits with zero.
#guard exitsWith 0 (runMem linux 100 (startWith ["pick", "a", "b", "c"]))

-- Started with no arguments at all, as a program may be, it takes the first.
#guard exitsWith 10 (runMem linux 100 (startWith []))

end Pick

/-- The program, with what running it takes. -/
def Pick.program : Runnable where
  name := "pick"
  elf := Asm.elf Pick.base Pick.code .start
  start := Pick.startArgs []
  startArgs := some Pick.startArgs
