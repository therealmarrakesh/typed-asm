import TypedAsm

/-!
# A recursive function, proved safe

Factorial, written the recursive way: each call that is not the last pushes
its argument, calls itself with one less, and multiplies on the way back.

```asm
_start:
     mov   edi, 5
     call  fact
afterCall:
     mov   edi, eax
     mov   eax, 60              ; `exit`
     syscall
fact:                           ; rdi = n; result in rax
     test  rdi, rdi
     jne   again
     mov   eax, 1
     ret
again:
     push  rdi
     sub   rdi, 1
     call  fact
afterAgain:
     pop   rdi
     imul  rax, rdi
     ret
```

Each level of the recursion uses two stack slots, so the stack a call needs
depends on its argument. The typing says exactly that: the function's
signature is indexed by `n`, takes exactly `n` in `rdi`, and needs `2 * n`
slots. A caller must then have that much room, which is what rules out
running off the end of the stack.

`lake exe fact` runs it in the model; `lake exe fact --elf FILE` writes an
executable that Linux can run.
-/

open TypedAsm

namespace Fact

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterCall | fact | again | afterAgain
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 5)),
  .call .fact,
  .label .afterCall,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fact,
  .ins (.test .w64 (.reg .rdi) (.reg .rdi)),
  .jcc .ne .again,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .ret,
  .label .again,
  .ins (.push .rdi),
  .ins (.alu .sub .w64 (.rm_i (.reg .rdi) 1)),
  .call .fact,
  .label .afterAgain,
  .ins (.pop .rdi),
  .ins (.imul2 .w64 .rax (.reg .rdi)),
  .ins .ret]

/-- Where the code is loaded. -/
def base : BitVec 64 := BitVec.ofNat 64 Elf.codeBase

/-- The program has no data; this is where its empty data segment goes. -/
def dataBase : BitVec 64 := BitVec.ofNat 64 Elf.dataBase

def fetch : Fetch := Asm.fetch base code

/-- The program's bytes. -/
def image : List Byte := Asm.image base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump and call reaches the label it names.
#guard Asm.offsetsFit base code

/-- Everything in the starting state except the program itself: eleven free
stack slots below `rsp`, one for the first return address and two for each
of the five levels below it. -/
def prepared : State :=
  ((State.init.loadData dataBase [] .ro).setPerm 0x7fffffa8 88 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with the program's bytes in executable
memory and `rip` at the entry. -/
def start : State :=
  { prepared.loadCode base image with rip := entry }

-- 5! = 120.
#guard exitsWith 120 (runMem linux 200 start)

end Fact

/-- With no arguments, runs the program on the machine with code in memory.
With `--elf FILE`, writes the program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  exeMain Fact.entry.toNat Fact.image [] Fact.start args
