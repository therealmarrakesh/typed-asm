import TypedAsm

/-!
# Printing a file, proved safe

Opens the file `input.txt`, copies it to standard output 64 bytes at a time,
closes it, and exits with status 0; or exits with status 1 if the file
cannot be opened.

```asm
_start:
     mov   eax, 257              ; `openat`
     mov   edi, -100             ; relative to the current directory
     lea   rsi, [rip + name]
     xor   edx, edx              ; for reading
     xor   r10d, r10d
     syscall
     test  rax, rax
     js    fail
     mov   r12, rax              ; the descriptor
next:
     xor   eax, eax              ; `read`
     mov   rdi, r12
     lea   rsi, [rip + buffer]
     mov   edx, 64
     syscall
     test  rax, rax
     jle   done                  ; nothing left, or an error
     mov   rdx, rax              ; as many bytes as were read
     mov   eax, 1                ; `write`
     mov   edi, 1
     syscall
     jmp   next
done:
     mov   eax, 3                ; `close`
     mov   rdi, r12
     syscall
     xor   edi, edi
     mov   eax, 231              ; `exit_group`
     syscall
fail:
     mov   edi, 1
     mov   eax, 231
     syscall
```

Nothing about the file needs a type. The name is bytes the kernel reads; the
descriptor is a number, and the kernel refuses one that is not open. What is
typed is what it always is: the buffer the `read` stores into.

`lake exe cat --file input.txt` runs it in the model on that file;
`lake exe cat --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Cat

/-! ## The program -/

inductive Label
  | start | next | done | fail
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rax) 257)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) (-100))),
  .ins (.lea .w64 .rsi (.rip 0xf3f)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.alu .xor .w32 (.rm_r (.reg .r10) .r10)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins (.mov .w64 (.rm_r (.reg .r12) .rax)),
  .label .next,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r12)),
  .ins (.lea .w64 .rsi (.rip 0xf30)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 64)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .done,
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins .syscall,
  .jmp .next,
  .label .done,
  .ins (.mov .w32 (.rm_i (.reg .rax) 3)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r12)),
  .ins .syscall,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall]

/-- Where the code is loaded. -/
def base : BitVec 64 := BitVec.ofNat 64 Elf.codeBase

/-- Where the data is loaded: the file's name, then the buffer. -/
def dataBase : BitVec 64 := BitVec.ofNat 64 Elf.dataBase

/-- Where the buffer is. -/
def bufferAt : BitVec 64 := dataBase + 16

def fetch : Fetch := Asm.fetch base code

/-- The program's bytes. -/
def image : List Byte := Asm.image base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump reaches the label it names, and the two address computations
-- give the addresses of the name and of the buffer.
#guard Asm.offsetsFit base code
#guard base + 17 + 0xf3f == dataBase
#guard base + 48 + 0xf30 == bufferAt

/-- The file's name, `input.txt`, as bytes. -/
def name : List Byte := [0x69, 0x6e, 0x70, 0x75, 0x74, 0x2e, 0x74, 0x78, 0x74]

#guard name == bytesOf "input.txt"

/-- The data's bytes: the name with the zero that ends it, filled out to 16
bytes, then a buffer of 64. -/
def dataBytes : List Byte :=
  name ++ List.replicate 7 0 ++ List.replicate 64 0

/-- Everything in the starting state except the program itself: the data in
writable memory. The program uses no stack. -/
def prepared : State :=
  (State.init.loadData dataBase dataBytes .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with the program's bytes in executable
memory and `rip` at the entry. There are no files. -/
def start : State :=
  { prepared.loadCode base image with rip := entry }

/-- The starting state with the given files there. -/
def startWith (files : List File) : State :=
  { start with world := { files := files.toArray } }

/-! ## Running it -/

-- With no such file it exits with status 1, having written nothing.
#guard wroteAndExited "" 1 (runMemFinal linux 1000 start)

-- The file comes out as it is; other files are left alone.
#guard wroteAndExited "one\ntwo\n" 0
  (runMemFinal linux 1000
    (startWith [fileOf "other.txt" (bytesOf "no"), fileOf "input.txt" (bytesOf "one\ntwo\n")]))

-- A file longer than the buffer takes several reads.
def long : List Byte := (List.range 200).map (BitVec.ofNat 8 ·)

#guard (runMemFinal linux 10000 (startWith [fileOf "input.txt" long])).1.world.output == long

-- When it has finished, the descriptor it was given is closed again.
#guard (runMemFinal linux 10000 (startWith [fileOf "input.txt" long])).1.world.fds.length == 3

-- A file the program may not read is not opened.
#guard wroteAndExited "" 1
  (runMemFinal linux 1000
    (startWith [{ fileOf "input.txt" (bytesOf "secret") with mayRead := false }]))

end Cat

/-- With no arguments, runs the program on the machine with code in memory;
`--file input.txt` gives it that file. With `--elf FILE`, writes the program
as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  exeMain Cat.entry.toNat Cat.image Cat.dataBytes Cat.start args (writable := true)
