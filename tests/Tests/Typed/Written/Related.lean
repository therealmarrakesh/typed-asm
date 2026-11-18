import TypedAsm
import TypedAsm.U.Checked

/-!
# A sum of low halves bounded by a relation between its operands

```asm
_start:
     mov   edx, 7
     mov   ecx, 4
     call  f
     xor   edi, edi
     mov   eax, 60
     syscall
f:                       ; rdx at most 10, rcx at most rdx
     mov   eax, ecx
     add   eax, 1        ; a sum of low halves: at most 11, since it does not wrap
     add   eax, edx      ; and another, of that and rdx: at most 21
     lea   r8, [table]
     movzx edx, byte [r8 + rax]
     ret
table: 22 bytes
```

That each 32-bit sum is the sum itself, and so the last at most twenty-one,
follows only from the relation between the operands, not from the range of
either; and that the second does not wrap is seen only once the first is.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Related

inductive L
  | start | f | table
  deriving DecidableEq, Hashable

/-- The program, with a table of so many bytes. -/
def codeOf (size : Nat) : List (Asm L) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rdx) 7)),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 4)),
  .call .f,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .f,
  .ins (.mov .w32 (.rm_r (.reg .rax) .rcx)),
  .ins (.alu .add .w32 (.rm_i (.reg .rax) 1)),
  .ins (.alu .add .w32 (.rm_r (.reg .rax) .rdx)),
  .ref (.lea .w64 .r8 (.rip 0)) .table,
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .r8) (some (.rax, .s1)) 0))),
  .ins .ret,
  .segment .ro,
  .label .table, .bytes (List.replicate size 0)]

def code : List (Asm L) := codeOf 22

asm_program code start .start stack 1

#guard exitsWith 0 (runMem linux 1000 start)

def blocksFor (size : Nat) : List (BitVec 64 × U.LayoutS) :=
  blocksWith (codeOf size) .start
    [(Asm.addr (codeOf size) (Asm.base (codeOf size)) .table, plainBlock size false)]

def pgFor (size : Nat) : Prog :=
  { code := progCode (Asm.table (Asm.base (codeOf size)) (codeOf size)), pre := preExits (· == 0)
    statics := staticIn (blocksFor size) (Asm.addr (codeOf size) (Asm.base (codeOf size)) .table) }

def labelsFor (size : Nat) : List U.Label :=
  [⟨Asm.addr (codeOf size) (Asm.base (codeOf size)) .start, inProgram 1⟩,
   ⟨Asm.addr (codeOf size) (Asm.base (codeOf size)) .f,
     inFunction (known := [(.was .rdx, .range 0 10), (.was .rcx, .upTo (.was .rdx) false)])⟩]

def blocks : List (BitVec 64 × U.LayoutS) := blocksFor 22

def pg : Prog := pgFor 22

def labels : List U.Label := labelsFor 22

/-- Whether the program with a table of so many bytes is typed. -/
def typed (size : Nat) : Bool :=
  wholeOkWith (codeOf size) .start 1 [] (blocksFor size) (pgFor size) (labelsFor size)
    (needFuel (pgFor size) (labelsFor size) [])

#guard typed 22
-- a table one byte shorter: the last read may be one past it. Refused
#guard !typed 21

asm_checked code start .start stack 1 program pg labels labels blocks blocks exits (· == 0)

end Tests.Written.Related
