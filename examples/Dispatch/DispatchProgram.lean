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

table:  dq double, square         ; one page after the load address
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
  .label .double,
  .ins (.lea .w64 .rax (.sib (some .rdi) (some (.rdi, .s1)) 0)),
  .ins .ret,
  .label .square,
  .ins (.mov .w64 (.rm_r (.reg .rax) .rdi)),
  .ins (.imul2 .w64 .rax (.reg .rdi)),
  .ins .ret,
  .segment false,
  .label .table, .quad .double, .quad .square]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

/-- Where the table is loaded. -/
def dataBase : BitVec 64 := Asm.addr code base .table

def fetch : Fetch := Asm.fetch base code

/-- The program's bytes. -/
def image : List Byte := Asm.image base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- The instructions come first and the data after, and every jump, call and
-- reference to data reaches the label it names.
#guard Asm.wellFormed code && Asm.offsetsFit base code

/-- The table's bytes: the addresses of the two functions. -/
def tableBytes : List Byte := Asm.dataImage base code

/-- Everything in the starting state except the program itself: the table,
and one free stack slot below `rsp`. -/
def prepared : State :=
  ((State.init.loadData dataBase tableBytes .ro).setPerm 0x7ffffff8 8 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with the program's bytes in executable
memory and `rip` at the entry. -/
def start : State :=
  { prepared.loadCode base image with rip := entry }

-- 5 squared, doubled, and doubled again.
#guard exitsWith 100 (runMem linux 100 start)

end Dispatch

/-- The program, with what running it takes. -/
def Dispatch.program : Runnable where
  name := "dispatch"
  entry := Dispatch.entry.toNat
  image := Dispatch.image
  segments := (Asm.segments Dispatch.base Dispatch.code).map fun (b, w, bs) => (b.toNat, w, bs)
  start := Dispatch.start
