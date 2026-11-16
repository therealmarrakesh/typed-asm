import TypedAsm

/-!
# Calling through a table of functions, proved safe

The data holds a table of two function addresses. The program picks an
entry by an index it first checks against the size of the table, calls
through the table, and also keeps a function pointer in a register that
survives a call and calls through that.

```asm
_start:
     lea   rbx, [rip + table]     ; rbx is preserved by the functions called
     mov   edi, 5
     mov   ecx, 1                 ; which entry
     cmp   rcx, 2                 ; the table has two
     jae   bad
     call  qword ptr [rbx + rcx*8]   ; square: 25
     mov   edi, eax
     mov   r12, [rbx]             ; a function pointer kept across a call
     call  r12                    ; double: 50
     mov   edi, eax
     call  r12                    ; and again, r12 still holds it: 100
     mov   edi, eax
     mov   eax, 60                ; `exit`
     syscall
bad:
     mov   edi, 1
     mov   eax, 60
     syscall
double:                           ; rdi = n; result in rax
     lea   rax, [rdi + rdi]
     ret
square:
     mov   rax, rdi
     imul  rax, rdi
     ret

table:  dq double, square         ; in a read-only segment between the two of code
```

That the table's entries are function pointers is a fact about the data, as
in the `Table` example; here it also rests on the two functions being well
typed, since a function pointer is by definition safe to call.

`lake exe dispatch` runs it in the model; `lake exe dispatch --elf FILE`
writes an executable that Linux can run.
-/

open TypedAsm

namespace Dispatch

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterFirst | afterSecond | afterThird | bad | double | square | table
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 5)),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 1)),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rcx) 2)),
  .jcc .ae .bad,
  .ins (.call (.ind (.mem (.sib (some .rbx) (some (.rcx, .s8)) 0)))),
  .label .afterFirst,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w64 (.r_m .r12 (.sib (some .rbx) none 0))),
  .ins (.call (.ind (.reg .r12))),
  .label .afterSecond,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.call (.ind (.reg .r12))),
  .label .afterThird,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .bad,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  -- the table, in a segment that can only be read
  .segment .ro,
  .label .table, .quad .double, .quad .square,
  -- the two functions, in an executable segment of their own
  .segment .rx,
  .label .double,
  .ins (.lea .w64 .rax (.sib (some .rdi) (some (.rdi, .s1)) 0)),
  .ins .ret,
  .label .square,
  .ins (.mov .w64 (.rm_r (.reg .rax) .rdi)),
  .ins (.imul2 .w64 .rax (.reg .rdi)),
  .ins .ret]

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it the
-- table, and one free stack slot below `rsp`.
asm_program code start .start stack 1 named "dispatch"

/-- Where the table is loaded. -/
def dataBase : BitVec 64 := Asm.addr code base .table

/-- The table's bytes: the addresses of the two functions. -/
def tableBytes : List Byte := Asm.dataAt base code .table 16

-- 5 squared, doubled, and doubled again.
#guard exitsWith 100 (runMem linux 100 start)

end Dispatch

