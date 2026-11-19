import TypedAsm
import TypedAsm.U.Checked

/-!
# What `write` answers, used as an index

```asm
_start:
     sub   rsp, 8
     mov   rsi, rsp
     mov   edx, 7
     mov   edi, 1
     mov   eax, 1
     syscall                     ; write(1, rsp, 7): how many it took
     test  rax, rax
     js    done
     lea   rbx, [table]
     movzx edx, byte [rbx + rax] ; one of the table's bytes, by that number
done:
     xor   edi, edi
     mov   eax, 60
     syscall
table: 8 bytes
```

The kernel may take fewer bytes than a `write` offers, never more: what it
answers is an error number or no more than was offered. So the answer to a
`write` of seven is an index into a table of eight; into a table of seven
it may be one past the end.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Wrote

inductive L
  | start | done | table
  deriving DecidableEq, Hashable

/-- The program, with a table of so many bytes. -/
def codeOf (n : Nat) : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 8)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rsp)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 7)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .done,
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rbx) (some (.rax, .s1)) 0))),
  .label .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .segment .ro,
  .label .table, .bytes (List.replicate n 0)]

def code : List (Asm L) := codeOf 8

asm_program code start .start stack 2

#guard exitsWith 0 (runMem linux 1000 start)

def blocksOn (n : Nat) : List (BitVec 64 × U.LayoutS) :=
  blocksWith (codeOf n) .start
    [(Asm.addr (codeOf n) (Asm.base (codeOf n)) .table, plainBlock n false)]

def pgOf (n : Nat) : Prog :=
  { code := progCode (Asm.table (Asm.base (codeOf n)) (codeOf n))
    statics := staticIn (blocksOn n) (Asm.addr (codeOf n) (Asm.base (codeOf n)) .table) }

def labelsOf (n : Nat) : List U.Label :=
  [⟨Asm.addr (codeOf n) (Asm.base (codeOf n)) .start, inProgram 2⟩]

/-- Whether the program is typed with a table of so many bytes. -/
def typed (n : Nat) : Bool :=
  wholeOkWith (codeOf n) .start 2 [] (blocksOn n) (pgOf n) (labelsOf n)
    (needFuel (pgOf n) (labelsOf n) [])

#guard typed 8
-- a table of seven: the answer may be seven, one past it. Refused
#guard !typed 7

def blocks : List (BitVec 64 × U.LayoutS) := blocksOn 8
def pg : Prog := pgOf 8
def labels : List U.Label := labelsOf 8

asm_checked code start .start stack 2 program pg labels labels blocks blocks

end Tests.Written.Wrote
