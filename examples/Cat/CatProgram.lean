import TypedAsm

/-!
# Printing a file, proved safe

Opens the file named by its first argument, copies it to standard output 64
bytes at a time, closes it, and exits with status 0. It exits with status 2
if it is given no argument, and 1 if the file cannot be opened.

```asm
_start:
     mov   rax, [rsp]            ; how many arguments, the program's name included
     cmp   rax, 2
     jb    usage
     mov   rsi, [rsp + 16]       ; the first argument: the address of a name
     mov   eax, 257              ; `openat`
     mov   edi, -100             ; relative to the current directory
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
usage:
     mov   edi, 2
     mov   eax, 231
     syscall
```

The arguments are where Linux puts them: the count at `[rsp]`, then the
address of each argument's text. To the types these are stack slots holding
numbers, which is all this program needs of them: the name's address goes
to the kernel as it is, and the kernel refuses an address it cannot read.
The descriptor is a number too. What is typed is what it always is: the
buffer the `read` stores into.

`lake exe cat -- FILE` runs it in the model on that file of this machine;
`lake exe cat --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Cat

/-! ## The program -/

inductive Label
  | start | next | done | fail | usage
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rsp) none 0))),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rax) 2)),
  .jcc .b .usage,
  .ins (.mov .w64 (.r_m .rsi (.sib (some .rsp) none 16))),
  .ins (.mov .w32 (.rm_i (.reg .rax) 257)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) (-100))),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.alu .xor .w32 (.rm_r (.reg .r10) .r10)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins (.mov .w64 (.rm_r (.reg .r12) .rax)),
  .label .next,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r12)),
  .ins (.lea .w64 .rsi (.rip 0xf14)),
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
  .ins .syscall,
  .label .usage,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 2)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall]

/-- Where the code is loaded. -/
def base : BitVec 64 := BitVec.ofNat 64 Elf.codeBase

/-- Where the buffer is loaded. -/
def dataBase : BitVec 64 := BitVec.ofNat 64 Elf.dataBase

def fetch : Fetch := Asm.fetch base code

/-- The program's bytes. -/
def image : List Byte := Asm.image base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump reaches the label it names, and the address computation gives
-- the address of the buffer.
#guard Asm.offsetsFit base code
#guard base + 60 + 0xf14 == dataBase

/-- The data's bytes: a buffer of 64. -/
def dataBytes : List Byte := List.replicate 64 0

/-- Everything in a starting state except the stack and the program itself:
the buffer in writable memory. -/
def prepared : State :=
  State.init.loadData dataBase dataBytes .rw

/-- A starting state: the buffer, a stack holding the given arguments, the
program's bytes in executable memory, and `rip` at the entry. The first
argument is by custom the program's own name. -/
def startArgs (args : List (List Byte)) : State :=
  { (prepared.withArgs 0 args).loadCode base image with rip := entry }

/-- That state with the given files there. -/
def startWith (args : List String) (files : List File) : State :=
  { startArgs (args.map bytesOf) with world := { files := files.toArray } }

/-! ## Running it -/

-- Given no argument it exits with status 2, having written nothing.
#guard wroteAndExited "" 2 (runMemFinal linux 1000 (startWith ["cat"] []))
#guard wroteAndExited "" 2 (runMemFinal linux 1000 (startWith [] []))

-- With no such file it exits with status 1.
#guard wroteAndExited "" 1 (runMemFinal linux 1000 (startWith ["cat", "input.txt"] []))

-- The file named comes out as it is; other files are left alone.
#guard wroteAndExited "one\ntwo\n" 0
  (runMemFinal linux 1000
    (startWith ["cat", "input.txt"]
      [fileOf "other.txt" (bytesOf "no"), fileOf "input.txt" (bytesOf "one\ntwo\n")]))

#guard wroteAndExited "no" 0
  (runMemFinal linux 1000
    (startWith ["cat", "other.txt"]
      [fileOf "other.txt" (bytesOf "no"), fileOf "input.txt" (bytesOf "one\ntwo\n")]))

-- A file longer than the buffer takes several reads.
def long : List Byte := (List.range 200).map (BitVec.ofNat 8 ·)

#guard (runMemFinal linux 10000
  (startWith ["cat", "long"] [fileOf "long" long])).1.world.output == long

-- When it has finished, the descriptor it was given is closed again.
#guard (runMemFinal linux 10000
  (startWith ["cat", "long"] [fileOf "long" long])).1.world.fds.length == 3

-- A file the program may not read is not opened.
#guard wroteAndExited "" 1
  (runMemFinal linux 1000
    (startWith ["cat", "secret"] [{ fileOf "secret" (bytesOf "hidden") with mayRead := false }]))

end Cat

/-- `lake exe cat -- FILE` runs the program on the machine with code in
memory, given that file of this machine. With `--elf FILE`, writes the
program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  exeMain Cat.entry.toNat Cat.image Cat.dataBytes (Cat.startArgs []) args (writable := true)
    (startArgs := some Cat.startArgs) (name := "cat")
