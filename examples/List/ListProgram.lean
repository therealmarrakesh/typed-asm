import TypedAsm

/-!
# Walking a linked list, proved safe

The data holds three nodes, each a value and the address of the next node,
the last with zero for its address. The program adds up the values,
following the links until it meets the zero.

```asm
_start:
     lea   rdi, [rip + list]    ; the first node, one page after the load address
     xor   eax, eax
loop:
     test  rdi, rdi
     jz    done                 ; the end of the list
     add   rax, [rdi]
     mov   rdi, [rdi + 8]       ; the next node, or zero
     jmp   loop
done:
     mov   edi, eax
     mov   eax, 60              ; `exit`
     syscall

list:    dq 3, second
second:  dq 4, third
third:   dq 5, 0
```

A node's second field points to a node, so its type has to mention the kind
of block it is itself part of. And the field may be zero, so nothing may be
loaded through it until a test has shown that it is not.

`lake exe list` runs it in the model; `lake exe list --elf FILE` writes an
executable that Linux can run.
-/

open TypedAsm

namespace List3

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | loop | done | first | second | third
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .first,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .label .loop,
  .ins (.test .w64 (.reg .rdi) (.reg .rdi)),
  .jcc .e .done,
  .ins (.alu .add .w64 (.r_m .rax (.sib (some .rdi) none 0))),
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rdi) none 8))),
  .jmp .loop,
  .label .done,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .segment .ro,
  .label .first, .bytes (le64 3), .quad .second,
  .label .second, .bytes (le64 4), .quad .third,
  .label .third, .bytes (le64 5 ++ le64 0)]

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it the
-- list. The program uses no stack.
asm_program code start .start stack 0 named "list"

/-- Where the list is loaded. Each node is sixteen bytes. -/
def dataBase : BitVec 64 := Asm.addr code base .first

/-- The data's bytes: three nodes, each a value and the address of the next. -/
def listBytes : List Byte := Asm.dataAt base code .first 48

-- 3 + 4 + 5.
#guard exitsWith 12 (runMem linux 100 start)

end List3

