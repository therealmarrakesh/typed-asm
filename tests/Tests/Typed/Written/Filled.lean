import TypedAsm
import TypedAsm.U.Checked

/-!
# What a function left in memory it was lent, known to its caller

```asm
_start:
     sub   rsp, 8
     mov   rdi, rsp
     call  fill
     movzx eax, byte [rsp + 2]   ; one of the bytes fill stored
     lea   rbx, [table]
     movzx edx, byte [rbx + rax]
     xor   edi, edi
     mov   eax, 60
     syscall
fill:                            ; rdi: eight bytes lent
     mov   eax, 7
     mov   [rdi], al
     mov   eax, 3
     mov   [rdi + 1], al
     mov   eax, 5
     mov   [rdi + 2], al
     mov   eax, 1
     mov   [rdi + 3], al
     ret                         ; the first four are each at most so much
table: 8 bytes
```

The read through the table is typed only because the function's type says
what the bytes it stored are when it returns: each at most seven.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Filled

inductive L
  | start | fill | table
  deriving DecidableEq, Hashable

/-- A number put in `eax`, and its low byte stored so far past `rdi`. -/
def st (o : BitVec 32) (v : BitVec 32) : List (Asm L) :=
  [.ins (.mov .w32 (.rm_i (.reg .rax) v)), .ins (.store8 (.sib (some .rdi) none o) .rax)]

def code : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 8)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .call .fill,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rsp) none 2))),
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rbx) (some (.rax, .s1)) 0))),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fill] ++ st 0 7 ++ st 1 3 ++ st 2 5 ++ st 3 1 ++ [
  .ins .ret,
  .segment .ro,
  .label .table, .bytes (List.replicate 8 0)]

asm_program code start .start stack 2

#guard exitsWith 0 (runMem linux 1000 start)

def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(Asm.addr code base .table, plainBlock 8 false)]

def pg : Prog :=
  { code := progCode (Asm.table base code), pre := preExits (· == 0)
    statics := staticIn blocks (Asm.addr code base .table) }

/-- The labels, the function said to leave bytes each at most so much. -/
def labelsFor (most : BitVec 64) : List U.Label :=
  [⟨entry, inProgram 2⟩,
   ⟨Asm.addr code base .fill,
     inFunction (takes := [(.was .rdi, 8)])
       (returnRows := [bytesAt (.was .rdi) 4 (.range 0 most)])⟩]

def labels : List U.Label := labelsFor 7

/-- Whether the program is typed with the function said to leave bytes
each at most so much. -/
def typed (most : BitVec 64) : Bool :=
  wholeOkWith code .start 2 [] blocks pg (labelsFor most) (needFuel pg (labelsFor most) [])

#guard typed 7
-- said to leave bytes at most eight: the read may be one past the table. Refused
#guard !typed 8
-- said to leave bytes at most four: it stores a seven and a five. Refused
#guard !typed 4

asm_checked code start .start stack 2 program pg labels labels blocks blocks exits (· == 0)

end Tests.Written.Filled
