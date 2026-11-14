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
  | start | loop | done
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.lea .w64 .rdi (.rip 0xf49)),
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
  .ins .syscall]

/-- Where the code is loaded. -/
def base : BitVec 64 := BitVec.ofNat 64 Elf.codeBase

/-- Where the list is loaded. Each node is sixteen bytes. -/
def dataBase : BitVec 64 := BitVec.ofNat 64 Elf.dataBase

def fetch : Fetch := Asm.fetch base code

/-- The program's bytes. -/
def image : List Byte := Asm.image base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump reaches the label it names, and the address computation gives
-- the address of the first node.
#guard Asm.offsetsFit base code
#guard base + 7 + 0xf49 == dataBase

/-- The data's bytes: three nodes, each a value and the address of the next. -/
def listBytes : List Byte :=
  le64 3 ++ le64 (dataBase + 16) ++ le64 4 ++ le64 (dataBase + 32) ++ le64 5 ++ le64 0

/-- Everything in the starting state except the program itself: the list.
The program uses no stack. -/
def prepared : State :=
  (State.init.loadData dataBase listBytes .ro).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with the program's bytes in executable
memory and `rip` at the entry. -/
def start : State :=
  { prepared.loadCode base image with rip := entry }

-- 3 + 4 + 5.
#guard exitsWith 12 (runMem linux 100 start)

end List3

/-- With no arguments, runs the program on the machine with code in memory.
With `--elf FILE`, writes the program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  exeMain List3.entry.toNat List3.image List3.listBytes List3.start args
