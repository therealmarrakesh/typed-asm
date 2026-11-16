import TypedAsm

/-!
# A function with a stack frame, proved safe

Exercises stack-frame allocation, locals, 32-bit and byte loads and stores,
a conditional jump in the middle of a block, and a comparison of two exactly
known values.

```asm
_start:
   0  lea   rdi, [rip + record]  ; the record is one page after the load address
   7  mov   esi, 7
  12  mov   edx, 7
  17  cmp   rsi, rdx
  20  jne   spin                 ; never taken
  26  call  pick
  31  mov   edi, eax
  33  mov   eax, 60              ; Linux `exit`
  38  syscall
spin:
  40  jmp   spin
pick:                            ; rdi = pointer to the record; result in rax
  45  sub   rsp, 16              ; two locals
  49  mov   [rsp], rdi           ; local 0: the pointer
  53  mov   eax, [rdi+8]         ; low half of the second field
  56  mov   [rsp+8], rax         ; local 1: that value
  61  mov   [rdi+12], eax        ; 32-bit store into the top half of the second field
  64  mov   [rdi+1], al          ; byte store into the first field
  67  test  rax, rax
  70  je    skip
  76  mov   rcx, [rsp]           ; the local is still a pointer
  80  movzx eax, byte ptr [rcx]
skip:
  83  add   rsp, 16
  87  ret
```

The numbers are offsets from the start of the code. The program is laid out
for the addresses of the ELF file it can be written to: code at `0x4000b0`,
the record at `0x401000`. `lake exe frame` runs it in the model;
`lake exe frame --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Frame

/-! ## The program -/

def rspSlot (disp : BitVec 32) : Mem := .sib (some .rsp) none disp

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterCall | spin | pick | skip | record
  deriving DecidableEq

/-- The record's two fields. -/
def record : List (BitVec 64) := [0x1234, 1]

/-- The record's bytes, as they sit in the file and in memory. -/
def recordBytes : List Byte := record.flatMap le64

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .record,
  .ins (.mov .w32 (.rm_i (.reg .rsi) 7)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 7)),
  .ins (.alu .cmp .w64 (.rm_r (.reg .rsi) .rdx)),
  .jcc .ne .spin,
  .call .pick,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .spin,
  .jmp .spin,
  .label .pick,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .ins (.mov .w64 (.rm_r (.mem (rspSlot 0)) .rdi)),
  .ins (.mov .w32 (.r_m .rax (.sib (some .rdi) none 8))),
  .ins (.mov .w64 (.rm_r (.mem (rspSlot 8)) .rax)),
  .ins (.mov .w32 (.rm_r (.mem (.sib (some .rdi) none 12)) .rax)),
  .ins (.store8 (.sib (some .rdi) none 1) .rax),
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .skip,
  .ins (.mov .w64 (.r_m .rcx (rspSlot 0))),
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rcx) none 0))),
  .label .skip,
  .ins (.alu .add .w64 (.rm_i (.reg .rsp) 16)),
  .ins .ret,
  .segment .rw,
  .label .record, .bytes recordBytes]

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

/-- The starting state but for `rip`: the program in memory, and with it the
record in writable memory, and three free stack slots below `rsp`. -/
def prepared : State :=
  ((Asm.load State.init base code .start).setPerm 0x7fffffe8 24 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. -/
def start : State :=
  { prepared with rip := entry }

/-! ## Running it -/

-- The second field is not zero, so the result is the low byte of the first: 0x34.
-- (The byte store changed the first field's second byte, not its low byte.)
#guard exitsWith 0x34 (runMem linux 100 start)

end Frame

/-- The program, with what running it takes. -/
def Frame.program : Runnable where
  name := "frame"
  elf := Asm.elf Frame.base Frame.code .start
  start := Frame.start
