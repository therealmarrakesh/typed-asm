import TypedAsm

/-!
# A bounds-checked array read, proved safe

`get` reads element `i` of an array of `n` integers, for any `i` at all: it
compares the index with the length first, and reads only if it is in range.
The typing follows the check. The index arrives as an integer the types know
nothing about; it is given a name, the comparison then says something about
that name, and the indexed load is entered only with the index known to be
below the length.

```asm
_start:
     lea   rdi, [rip + array]   ; the array is one page after the load address
     mov   esi, 5               ; its length
     mov   edx, 3               ; the index
     call  get
afterCall:
     mov   edi, eax
     mov   eax, 60              ; Linux `exit`
     syscall
get:                            ; rdi = array, rsi = length, rdx = index; result in rax
     cmp   rdx, rsi
     jb    inbounds
     xor   eax, eax             ; out of range: return 0
     ret
inbounds:
     mov   rax, [rdi + rdx*8]
     ret
```

The program is laid out for the addresses of the ELF file it can be written
to: code at `0x4000b0`, the array at `0x401000`. `lake exe index` runs it in
the model; `lake exe index --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Index

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterCall | get | inbounds | array
  deriving DecidableEq

def array : List (BitVec 64) := [10, 20, 30, 40, 50]

/-- The array's bytes, as they sit in the file and in memory. -/
def arrayBytes : List Byte := array.flatMap le64

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .array,
  .ins (.mov .w32 (.rm_i (.reg .rsi) 5)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .call .get,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .get,
  .ins (.alu .cmp .w64 (.rm_r (.reg .rdx) .rsi)),
  .jcc .b .inbounds,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret,
  .label .inbounds,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) (some (.rdx, .s8)) 0))),
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

-- Element 3 is 40.
#guard exitsWith 40 (run fetch linux 100 start)
#guard exitsWith 40 (runMem linux 100 start)

end Index

/-- The program, with what running it takes. -/
def Index.program : Runnable where
  name := "index"
  elf := Asm.elf Index.base Index.code .start
  start := Index.start
