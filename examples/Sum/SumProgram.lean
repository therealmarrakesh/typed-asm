import TypedAsm

/-!
# Summing an array, proved safe

A function that sums `n` 64-bit integers through a moving pointer, with a
loop counter. Its safety depends on the counter and the pointer staying in
step, which the typing expresses with types that depend on values: the
contexts inside the loop are indexed by how many elements have been consumed.

```asm
_start:
   0  lea   rdi, [rip + array]   ; the array is one page after the load address
   7  mov   esi, 5
  12  call  sum
  17  mov   edi, eax
  19  mov   eax, 60              ; Linux `exit`
  24  syscall
sum:                             ; rdi = pointer, rsi = count, result in rax
  26  xor   eax, eax
  28  test  rsi, rsi
  31  je    done
loop:
  37  add   rax, [rdi]
  40  add   rdi, 8
  44  sub   rsi, 1
  48  jne   loop
done:
  54  ret
```

The numbers are offsets from the start of the code. The program is laid out
for the addresses of the ELF file it can be written to: code at `0x4000b0`,
the array at `0x401000`. `lake exe sum` runs it in the model;
`lake exe sum --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Sum

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterCall | sum | loop | done | array
  deriving DecidableEq

def array : List (BitVec 64) := [3, 1, 4, 1, 5]

/-- The array's bytes, as they sit in the file and in memory. -/
def arrayBytes : List Byte := array.flatMap le64

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .array,
  .ins (.mov .w32 (.rm_i (.reg .rsi) 5)),
  .call .sum,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .sum,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.test .w64 (.reg .rsi) (.reg .rsi)),
  .jcc .e .done,
  .label .loop,
  .ins (.alu .add .w64 (.r_m .rax (.sib (some .rdi) none 0))),
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 8)),
  .ins (.alu .sub .w64 (.rm_i (.reg .rsi) 1)),
  .jcc .ne .loop,
  .label .done,
  .ins .ret,
  .segment .ro,
  .label .array, .bytes arrayBytes]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

/-- Where the array is loaded. -/
def dataBase : BitVec 64 := Asm.addr code base .array

def fetch : Fetch := Asm.fetch base code

/-- What the program puts in memory, line by line. -/
def parts : List (Nat × Perm × List Byte) := Asm.parts base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every instruction stands in an executable segment, and every jump, call and
-- reference to data reaches the label it names.
#guard Asm.wellFormed code && Asm.offsetsFit base code

/-- The starting state but for `rip`: the program in memory, and with it
the array
in read-only memory, and one free stack slot below `rsp`. -/
def prepared : State :=
  ((Asm.load State.init base code).setPerm 0x7ffffff8 8 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. -/
def start : State :=
  { prepared with rip := entry }

-- The program exits with status 14 = 3 + 1 + 4 + 1 + 5, whether instructions
-- come from the table or are decoded from memory.
#guard exitsWith 14 (run fetch linux 100 start)
#guard exitsWith 14 (runMem linux 100 start)

end Sum

/-- The program, with what running it takes. -/
def Sum.program : Runnable where
  name := "sum"
  elf := Asm.elf Sum.base Sum.code .start
  start := Sum.start
