import TypedAsm

/-!
# Handing a function a pointer to a local, proved safe

`work` makes room on the stack for a local of sixteen bytes and hands its
address to `fill`, which stores two numbers through it. `work` then adds up
what it finds in its local, and the program exits with the sum, 7.

```asm
_start:
     call  work
     mov   edi, eax
     mov   eax, 60               ; `exit`
     syscall
work:
     sub   rsp, 16               ; a local of sixteen bytes
     lea   rdi, [rsp]            ; its address
     call  fill
     mov   rax, [rsp]
     add   rax, [rsp + 8]
     add   rsp, 16
     ret
fill:
     mov   qword ptr [rdi], 3
     mov   qword ptr [rdi + 8], 4
     ret
```

A function is handed memory by being handed a block to own. So for the call,
`work` detaches its local from the stack: the local becomes a block `work`
owns, which it hands to `fill` and is given back. Only the top of a stack
can be detached, so what lies above the local, `work`'s return address and
its caller's part of the stack, is detached with it, and nothing reaches it
while `fill` runs. After the call everything is attached again and the stack
is as it was, with the local holding what `fill` stored.

`lake exe lend` runs it in the model; `lake exe lend --elf FILE` writes an
executable that Linux can run.
-/

open TypedAsm

namespace Lend

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | done | work | filled | fill
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .call .work,
  .label .done,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .work,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .ins (.lea .w64 .rdi (.sib (some .rsp) none 0)),
  .call .fill,
  .label .filled,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rsp) none 0))),
  .ins (.alu .add .w64 (.r_m .rax (.sib (some .rsp) none 8))),
  .ins (.alu .add .w64 (.rm_i (.reg .rsp) 16)),
  .ins .ret,
  .label .fill,
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rdi) none 0)) 3)),
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rdi) none 8)) 4)),
  .ins .ret]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

def fetch : Fetch := Asm.fetch base code

/-- What the program puts in memory, line by line. -/
def parts : List (Nat × Perm × List Byte) := Asm.parts base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump and call reaches the label it names.
#guard Asm.offsetsFit base code

/-- The starting state but for `rip`: the program in memory, and with it four
free stack slots below `rsp`: a return address, the local, and another return
address. -/
def prepared : State :=
  ((Asm.load State.init base code).setPerm 0x7fffffe0 32 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. -/
def start : State :=
  { prepared with rip := entry }

-- 3 + 4.
#guard exitsWith 7 (runMem linux 100 start)

end Lend

/-- The program, with what running it takes. -/
def Lend.program : Runnable where
  name := "lend"
  elf := Asm.elf Lend.base Lend.code .start
  start := Lend.start
