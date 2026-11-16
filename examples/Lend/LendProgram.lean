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

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it four
-- free stack slots below `rsp`: a return address, the local, and another
-- return address.
asm_program code start .start stack 4 named "lend"

-- 3 + 4.
#guard exitsWith 7 (runMem linux 100 start)

end Lend

