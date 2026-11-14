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
spin:
     jmp   spin
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
  | start | afterCall | spin | get | inbounds
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.lea .w64 .rdi (.rip 0xf49)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 5)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .call .get,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .spin,
  .jmp .spin,
  .label .get,
  .ins (.alu .cmp .w64 (.rm_r (.reg .rdx) .rsi)),
  .jcc .b .inbounds,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret,
  .label .inbounds,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) (some (.rdx, .s8)) 0))),
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

def array : List (BitVec 64) := [10, 20, 30, 40, 50]

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

def describe : Outcome → String
  | .next s => s!"still running at rip = {s.rip.toNat}"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

def exitsWith (code : BitVec 32) : Outcome → Bool
  | .exit c => c == code
  | _ => false

-- Element 3 is 40.
#guard exitsWith 40 (run fetch linux 100 start)
#guard exitsWith 40 (runMem linux 100 start)

end Index

/-- With no arguments, runs the program on the machine with code in memory
and prints the outcome. With `--elf FILE`, writes the program as a Linux executable. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["--elf", path] =>
    let bytes := Elf.file Index.entry.toNat Index.image Index.arrayBytes
    IO.FS.writeBinFile path (ByteArray.mk (bytes.map fun b => b.toNat.toUInt8).toArray)
    IO.println s!"wrote {bytes.length} bytes to {path}"
  | _ => IO.println (Index.describe (runMem linux 100 Index.start))
