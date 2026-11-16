import TypedAsm

/-!
# Hello: what a program writes, proved

Writes a line to standard output and ends:

```asm
_start:
     mov   eax, 1               ; `write`
     mov   edi, 1               ; to standard output
     lea   rsi, [rip + message]
     mov   edx, 14              ; this many bytes
     syscall
     mov   eax, 60              ; `exit`
     xor   edi, edi
     syscall

segment readable

message: db "Hello, world!", 10
```

Besides being safe, the program is proved to write what it should: the one
`write` it makes offers the kernel exactly the bytes of the message, on
descriptor 1. That is in `Hello.lean`.

`lake exe hello` runs the program in the model; `lake exe hello --elf FILE`
writes an executable that Linux can run.
-/

open TypedAsm

namespace Hello

/-! ## The program -/

inductive Label
  | start | message
  deriving DecidableEq

/-- The line the program writes. -/
def message : List Byte := "Hello, world!\n".toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ref (.lea .w64 .rsi (.rip 0)) .message,
  .ins (.mov .w32 (.rm_i (.reg .rdx) 14)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall,
  .segment .ro,
  .label .message, .bytes message]

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
asm_program code start .start stack 0 named "hello"

-- It ends with status 0.
#guard exitsWith 0 (runMem linux 100 start)

end Hello
