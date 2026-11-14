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
  | start | afterCall | sum | loop | done
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.lea .w64 .rdi (.rip 0xf49)),
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
  .ins .ret]

/-- Where the code is loaded. -/
def base : BitVec 64 := BitVec.ofNat 64 Elf.codeBase

/-- Where the array is loaded. -/
def dataBase : BitVec 64 := BitVec.ofNat 64 Elf.dataBase

def fetch : Fetch := Asm.fetch base code

/-- The program's bytes. -/
def image : List Byte := Asm.image base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump and call reaches the label it names.
#guard Asm.offsetsFit base code

def array : List (BitVec 64) := [3, 1, 4, 1, 5]

/-- The array's bytes, as they sit in the file and in memory. -/
def arrayBytes : List Byte := array.flatMap le64

/-- Everything in the starting state except the program itself: the array
in read-only memory, and one free stack slot below `rsp`. -/
def prepared : State :=
  let s := (State.init.setPerm dataBase 40 .ro).setPerm 0x7ffffff8 8 .rw
  let s := (array.zipIdx).foldl (fun s (v, i) => s.store64 (dataBase + 8 * BitVec.ofNat 64 i) v) s
  s.setReg .rsp 0x80000000

/-- A starting state: `prepared`, with the program's bytes in executable
memory and `rip` at the entry. -/
def start : State :=
  { prepared.loadCode base image with rip := entry }

-- The program exits with status 14 = 3 + 1 + 4 + 1 + 5, whether instructions
-- come from the table or are decoded from memory.
#guard exitsWith 14 (run fetch linux 100 start)
#guard exitsWith 14 (runMem linux 100 start)

end Sum

/-- With no arguments, runs the program on the machine with code in memory:
what it writes goes to standard output, how it ended to standard error, and
its exit status becomes this executable's. With `--elf FILE`, writes the
program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  exeMain Sum.entry.toNat Sum.image Sum.arrayBytes Sum.start args
