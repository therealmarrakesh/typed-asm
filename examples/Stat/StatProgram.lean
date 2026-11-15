import TypedAsm

/-!
# Asking about a file, the time and chance, proved safe

Opens the file `input.txt`, asks the kernel how long it is in two ways and
checks that the answers agree, asks the time, asks for eight random bytes,
closes the file, and exits with the file's length as its status (its low
eight bits, as Linux reports it). If anything is refused it exits with
status 255.

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
     lea   r13, [rip + buffer]
     mov   eax, 5                ; `fstat`: what the kernel knows of the file
     mov   rdi, r12
     mov   rsi, r13
     syscall
     test  rax, rax
     jnz   fail
     mov   eax, 8                ; `lseek` to the end: the length again
     mov   rdi, r12
     xor   esi, esi
     mov   edx, 2
     syscall
     mov   rbx, [r13 + 48]       ; the length `fstat` gave
     cmp   rax, rbx
     jne   fail
     mov   eax, 228              ; `clock_gettime`
     mov   edi, 1
     mov   rsi, r13
     syscall
     test  rax, rax
     jnz   fail
     mov   eax, 318              ; `getrandom`: eight bytes
     mov   rdi, r13
     mov   esi, 8
     xor   edx, edx
     syscall
     cmp   rax, 8
     jne   fail
     mov   eax, 3                ; `close`
     mov   rdi, r12
     syscall
     mov   rdi, rbx
     mov   eax, 231              ; `exit_group`
     syscall
fail:
     mov   edi, 255
     mov   eax, 231
     syscall
```

Three calls here store into the program's memory, each a different amount:
`fstat` 144 bytes, `clock_gettime` 16, `getrandom` as many as it is asked
for. Each is typed by the same condition as a `read`: that many bytes from
the buffer are plain bytes of a writable block. The buffer is 144 bytes,
so all three fit.

The program has two data segments. The file's name is in one that can only
be read; the buffer is in another, a page on, that can be written.

`lake exe stat --file input.txt` runs it in the model on that file;
`lake exe stat --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Stat

/-! ## The program -/

inductive Label
  | start | fail | path | buffer
  deriving DecidableEq

/-- The file's name, `input.txt`, as bytes. -/
def name : List Byte := [0x69, 0x6e, 0x70, 0x75, 0x74, 0x2e, 0x74, 0x78, 0x74]

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rax) 257)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) (-100))),
  .ref (.lea .w64 .rsi (.rip 0)) .path,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.alu .xor .w32 (.rm_r (.reg .r10) .r10)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins (.mov .w64 (.rm_r (.reg .r12) .rax)),
  .ref (.lea .w64 .r13 (.rip 0)) .buffer,
  .ins (.mov .w32 (.rm_i (.reg .rax) 5)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r12)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .r13)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .ne .fail,
  .ins (.mov .w32 (.rm_i (.reg .rax) 8)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r12)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rsi) .rsi)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 2)),
  .ins .syscall,
  .ins (.mov .w64 (.r_m .rbx (.sib (some .r13) none 48))),
  .ins (.alu .cmp .w64 (.rm_r (.reg .rax) .rbx)),
  .jcc .ne .fail,
  .ins (.mov .w32 (.rm_i (.reg .rax) 228)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .r13)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .ne .fail,
  .ins (.mov .w32 (.rm_i (.reg .rax) 318)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r13)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 8)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins .syscall,
  .ins (.alu .cmp .w64 (.rm_i (.reg .rax) 8)),
  .jcc .ne .fail,
  .ins (.mov .w32 (.rm_i (.reg .rax) 3)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r12)),
  .ins .syscall,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 255)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .segment .ro,
  .label .path, .bytes (name ++ [0]),
  .segment .rw,
  .label .buffer, .space 144]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

/-- Where the buffer is. -/
def bufferAt : BitVec 64 := Asm.addr code base .buffer

def fetch : Fetch := Asm.fetch base code

/-- What the program puts in memory, line by line. -/
def parts : List (Nat × Perm × List Byte) := Asm.parts base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every instruction stands in an executable segment, and every jump, call and
-- reference to data reaches the label it names.
#guard Asm.wellFormed code && Asm.offsetsFit base code

#guard name == bytesOf "input.txt"

/-- The starting state but for `rip`: the program in memory, and with it
its two
data segments in memory, the name readable and the buffer writable. The
program uses no stack. -/
def prepared : State :=
  (Asm.load State.init base code).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. There are no files. -/
def start : State :=
  { prepared with rip := entry }

/-- The starting state with the given files there. -/
def startWith (files : List File) : State :=
  { start with world := { files := files.toArray } }

/-! ## Running it -/

-- With no such file it exits with status 255.
#guard wroteAndExited "" 255 (runMemFinal linux 1000 start)

-- The status is the file's length.
#guard wroteAndExited "" 5 (runMemFinal linux 1000 (startWith [fileOf "input.txt" (bytesOf "hello")]))

#guard wroteAndExited "" 300
  (runMemFinal linux 1000 (startWith [fileOf "input.txt" (List.replicate 300 0x61)]))

-- By the end the kernel has been asked the time once and has handed out
-- eight random bytes, and the descriptor is closed again.
#guard (runMemFinal linux 1000 (startWith [fileOf "input.txt" (bytesOf "hello")])).1.world.asks == 1
#guard (runMemFinal linux 1000 (startWith [fileOf "input.txt" (bytesOf "hello")])).1.world.drawn == 8
#guard (runMemFinal linux 1000 (startWith [fileOf "input.txt" (bytesOf "hello")])).1.world.fds.length == 3

end Stat

/-- The program, with what running it takes. -/
def Stat.program : Runnable where
  name := "stat"
  elf := Asm.elf Stat.base Stat.code .start
  start := Stat.start
