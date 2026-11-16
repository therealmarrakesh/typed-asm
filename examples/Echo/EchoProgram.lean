import TypedAsm

/-!
# Copying input to output, proved safe

Reads up to 16 bytes at a time from standard input and writes them to
standard output, until there is nothing more to read.

```asm
_start:
     xor   eax, eax              ; `read`
     xor   edi, edi              ; from standard input
     lea   rsi, [rip + buffer]   ; the buffer is one page after the load address
     mov   edx, 16
     syscall
     test  rax, rax
     jle   done                  ; nothing left, or an error
     mov   rdx, rax              ; as many bytes as were read
     mov   eax, 1                ; `write`
     mov   edi, 1                ; to standard output
     syscall
     jmp   _start
done:
     mov   eax, 60               ; `exit`
     xor   edi, edi
     syscall
```

The typing of the `read` is what makes this safe: the kernel stores up to 16
bytes at the buffer, and the type of `rsi` says those 16 bytes are plain
bytes of a writable block, so nothing typed is overwritten. The
`write` needs no such condition, since the kernel only reads.

The program is laid out for the addresses of the ELF file it can be written
to: code at `0x4000b0`, the buffer at `0x401000`. `lake exe echo` runs it in
the model on this process's standard input; `lake exe echo --elf FILE`
writes an executable that Linux can run.
-/

open TypedAsm

namespace Echo

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | done | buffer
  deriving DecidableEq

/-- The buffer's bytes as they sit in the file: sixteen zeros. -/
def bufferBytes : List Byte := List.replicate 16 0

def code : List (Asm Label) := [
  .label .start,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ref (.lea .w64 .rsi (.rip 0)) .buffer,
  .ins (.mov .w32 (.rm_i (.reg .rdx) 16)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .done,
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins .syscall,
  .jmp .start,
  .label .done,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall,
  .segment .rw,
  .label .buffer, .bytes bufferBytes]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

/-- Where the buffer is loaded. -/
def dataBase : BitVec 64 := Asm.addr code base .buffer

def fetch : Fetch := Asm.fetch base code

/-- What the program puts in memory, line by line. -/
def parts : List (Nat × Perm × List Byte) := Asm.parts base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every instruction stands in an executable segment, and every jump, call and
-- reference to data reaches the label it names.
#guard Asm.wellFormed code && Asm.offsetsFit base code

/-- The starting state but for `rip`: the program in memory, and with it the
buffer in writable memory. The program uses no stack. -/
def prepared : State :=
  (Asm.load State.init base code .start).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. Nothing is waiting
to be read. -/
def start : State :=
  { prepared with rip := entry }

/-- The starting state with the given input waiting, one event per `read`. -/
def startWith (input : List ReadEvent) : State :=
  { start with world := { input := input } }

/-! ## Running it -/

-- With nothing to read it exits at once, having written nothing.
#guard wroteAndExited "" 0 (runMemFinal linux 1000 start)

-- Input comes back unchanged. The second piece is longer than the buffer,
-- so it takes several reads.
#guard wroteAndExited "hello, world: this is longer than sixteen bytes\n" 0
  (runMemFinal linux 1000
    (startWith [.bytes (bytesOf "hello, "),
      .bytes (bytesOf "world: this is longer than sixteen bytes\n")]))

-- An error from `read` ends the loop like the end of input does.
#guard wroteAndExited "ab" 0
  (runMemFinal linux 1000 (startWith [.bytes (bytesOf "ab"), .error .io, .bytes (bytesOf "cd")]))

-- This program trusts each `write` to take everything. When one takes less,
-- as the kernel is allowed to, what it did not take is lost: here the first
-- `write` accepts only three bytes. The program is still safe.
#guard wroteAndExited "helab" 0
  (runMemFinal linux 1000
    { startWith [.bytes (bytesOf "hello"), .bytes (bytesOf "ab")] with
      world := {
        input := [.bytes (bytesOf "hello"), .bytes (bytesOf "ab")]
        fates := [.short 3] } })

-- A longer input, 4,096 bytes in one piece, comes back intact. The model
-- runs at a steady speed however much it has stored; if that were lost,
-- this check would be the first thing to slow down.
def sample : List Byte := (List.range 4096).map (BitVec.ofNat 8 ·)

#guard (runMemFinal linux 100000 (startWith [.bytes sample])).1.world.output == sample

end Echo

/-- The program, with what running it takes. -/
def Echo.program : Runnable where
  name := "echo"
  elf := Asm.elf Echo.base Echo.code .start
  start := Echo.start
  readsInput := true
