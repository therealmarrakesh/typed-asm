import TypedAsm

/-!
# Swapping two fields, proved safe

A complete program that is type-checked and then proved safe by the soundness
theorem. A function that swaps the two fields of a record is typed once and
called from two places whose stacks differ. The caller keeps its pointer in
`rbx` across both calls, relying on `swap` to preserve that register.

```asm
_start:
   0  lea   rdi, [rip + record]  ; the record is in the segment before the code
   7  mov   rbx, rdi             ; keep the pointer in a callee-saved register
  10  call  swap                 ; called with an empty stack
  15  push  rbx
  16  mov   rdi, rbx             ; rbx is still a pointer after the call
  19  call  swap                 ; called with one slot on the stack
  24  pop   rdi
  25  mov   eax, 60              ; Linux `exit`
  30  xor   edi, edi
  32  syscall
swap:                            ; rdi = pointer to the record
  34  mov   rax, [rdi]
  37  mov   rcx, [rdi+8]
  41  mov   [rdi], rcx
  44  mov   [rdi+8], rax
  48  ret
```

The numbers are offsets from the start of the code. The program is laid out
for the addresses of the ELF file it can be written to: code at `0x4000b0`,
the record at `0x401000`. `lake exe swap` runs it in the model;
`lake exe swap --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Swap

/-! ## The program -/

def field (disp : BitVec 32) : Mem := .sib (some .rdi) none disp

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterFirst | afterSecond | swap | record
  deriving DecidableEq

/-- The record's two fields. -/
def record : List (BitVec 64) := [3, 5]

/-- The record's bytes, as they sit in the file and in memory. -/
def recordBytes : List Byte := record.flatMap le64

def code : List (Asm Label) := [
  -- the record comes first, in a segment of its own that can be written;
  -- the instructions follow in another, a page on
  .segment .rw,
  .label .record, .bytes recordBytes,
  .segment .rx,
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .record,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rdi)),
  .call .swap,
  .label .afterFirst,
  .ins (.push .rbx),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)),
  .call .swap,
  .label .afterSecond,
  .ins (.pop .rdi),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall,
  .label .swap,
  .ins (.mov .w64 (.r_m .rax (field 0))),
  .ins (.mov .w64 (.r_m .rcx (field 8))),
  .ins (.mov .w64 (.rm_r (.mem (field 0)) .rcx)),
  .ins (.mov .w64 (.rm_r (.mem (field 8)) .rax)),
  .ins .ret]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

/-- Where the record is loaded. -/
def dataBase : BitVec 64 := Asm.addr code base .record

def fetch : Fetch := Asm.fetch base code

/-- What the program puts in memory, line by line. -/
def parts : List (Nat × Perm × List Byte) := Asm.parts base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every instruction stands in an executable segment, and every jump, call and
-- reference to data reaches the label it names.
#guard Asm.wellFormed code && Asm.offsetsFit base code

/-- The starting state but for `rip`: the program in memory, and with it
the record
in writable memory, and two free stack slots below `rsp`. -/
def prepared : State :=
  ((Asm.load State.init base code).setPerm 0x7ffffff0 16 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. -/
def start : State :=
  { prepared with rip := entry }

/-! ## Running it -/

def recordIs (x y : BitVec 64) : Outcome → Bool
  | .next s => s.load64 dataBase == x && s.load64 (dataBase + 8) == y
  | _ => false

-- After the first call returns (eight steps) the fields are exchanged, and
-- after the second (eight more) they are back. Instructions are decoded from memory.
#guard recordIs 5 3 (runMem linux 8 start)
#guard recordIs 3 5 (runMem linux 16 start)

end Swap

/-- The program, with what running it takes. -/
def Swap.program : Runnable where
  name := "swap"
  elf := Asm.elf Swap.base Swap.code .start
  start := Swap.start
