import TypedAsm

/-!
# Printing files, proved safe

Copies each file named by its arguments to standard output, 64 bytes at a
time, and exits with status 0; or stops and exits with status 1 at the first
file it cannot open.

```asm
_start:
     mov   r13, [rsp]            ; how many arguments, the program's name included
     mov   r14d, 1               ; the argument to do next
file:
     cmp   r14, r13
     jae   done                  ; no more arguments
     mov   rsi, [rsp + r14*8 + 8] ; this argument: the address of a name
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
     jle   eof                   ; nothing left, or an error
     mov   rdx, rax              ; as many bytes as were read
     mov   eax, 1                ; `write`
     mov   edi, 1
     syscall
     jmp   next
eof:
     mov   eax, 3                ; `close`
     mov   rdi, r12
     syscall
     add   r14, 1
     jmp   file
done:
     xor   edi, edi
     mov   eax, 231              ; `exit_group`
     syscall
fail:
     mov   edi, 1
     mov   eax, 231
     syscall
```

The arguments are where Linux puts them: the count at `[rsp]`, then the
address of each argument's text. How many slots there are depends on the
count, so the program's contexts do too: there is one for each count `c`,
with `c` exactly known in `r13` and the slots after it numbering `c + 4`.
The load of an argument's address is typed because it comes after the
comparison that found the index below the count.

What the slots hold are numbers to the types, which is all this program
needs: a name's address goes to the kernel as it is, and the kernel refuses
an address it cannot read. The descriptor is a number too. The buffer the
`read` stores into is typed as it always is.

`lake exe cat -- FILE...` runs it in the model on those files of this
machine; `lake exe cat --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Cat

/-! ## The program -/

inductive Label
  | start | file | next | eof | done | fail | buffer
  deriving DecidableEq, Hashable

/-- The data's bytes: a buffer of 64. -/
def dataBytes : List Byte := List.replicate 64 0

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w64 (.r_m .r13 (.sib (some .rsp) none 0))),
  .ins (.mov .w32 (.rm_i (.reg .r14) 1)),
  .label .file,
  .ins (.alu .cmp .w64 (.rm_r (.reg .r14) .r13)),
  .jcc .ae .done,
  .ins (.mov .w64 (.r_m .rsi (.sib (some .rsp) (some (.r14, .s8)) 8))),
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
  .ref (.lea .w64 .rsi (.rip 0)) .buffer,
  .ins (.mov .w32 (.rm_i (.reg .rdx) 64)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .eof,
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins .syscall,
  .jmp .next,
  .label .eof,
  .ins (.mov .w32 (.rm_i (.reg .rax) 3)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r12)),
  .ins .syscall,
  .ins (.alu .add .w64 (.rm_i (.reg .r14) 1)),
  .jmp .file,
  .label .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .segment .rw,
  .label .buffer, .bytes dataBytes]

-- Where the program is loaded, what it puts in memory, where it starts,
-- all from the lines above.
asm_program code start .start stack 0

/-- That state with the given files there. -/
def startWith (args : List String) (files : List File) : State :=
  { startArgs (args.map bytesOf) with world := { files := files.toArray } }

/-! ## Running it -/

def someFiles : List File :=
  [fileOf "a" (bytesOf "one\n"), fileOf "b" (bytesOf "two\n"), fileOf "c" (bytesOf "three\n")]

-- Given no file to print it prints nothing, whether or not it was told its
-- own name.
#guard wroteAndExited "" 0 (runMemFinal linux 1000 (startWith ["cat"] someFiles))
#guard wroteAndExited "" 0 (runMemFinal linux 1000 (startWith [] someFiles))

-- One file comes out as it is.
#guard wroteAndExited "two\n" 0 (runMemFinal linux 1000 (startWith ["cat", "b"] someFiles))

-- Several come out one after another, in the order asked for.
#guard wroteAndExited "three\none\ntwo\none\n" 0
  (runMemFinal linux 10000 (startWith ["cat", "c", "a", "b", "a"] someFiles))

-- It stops at the first file it cannot open, having printed those before it.
#guard wroteAndExited "one\n" 1
  (runMemFinal linux 10000 (startWith ["cat", "a", "missing", "b"] someFiles))

-- A file longer than the buffer takes several reads.
def long : List Byte := (List.range 200).map (BitVec.ofNat 8 ·)

#guard (runMemFinal linux 10000
  (startWith ["cat", "long"] [fileOf "long" long])).1.world.output == long

-- When it has finished, every descriptor it was given is closed again.
#guard (runMemFinal linux 10000
  (startWith ["cat", "c", "a", "b"] someFiles)).1.world.fds.length == 3

-- A file the program may not read is not opened.
#guard wroteAndExited "" 1
  (runMemFinal linux 1000
    (startWith ["cat", "secret"] [{ fileOf "secret" (bytesOf "hidden") with mayRead := false }]))

end Cat

/-- The program, with what running it takes. -/
def Cat.program : Runnable where
  name := "cat"
  elf := Asm.elf Cat.base Cat.code .start
  startArgs := Cat.startArgs
