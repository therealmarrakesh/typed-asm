import TypedAsm
import TypedAsm.U.Checked

/-!
# P1: a static table of four records (text pointer, number)

```asm
_start:
     lea   rbx, [rip + table]
     xor   r12d, r12d          ; sum
     xor   r13d, r13d          ; i
loop:
     cmp   r13, 4
     jae   done
     mov   rdi, r13
     shl   rdi, 4
     add   rdi, rbx            ; &table[i]
     call  reclen
     add   r12, rax
     add   r13, 1
     jmp   loop
done:
     mov   edi, r12d
     mov   eax, 60
     syscall
reclen:                        ; rdi = record; rax = strlen(rec.text) + rec.n
     mov   rsi, [rdi]
     mov   rax, [rdi + 8]
scan:
     movzx ecx, byte [rsi]
     test  rcx, rcx
     jz    out
     add   rax, 1
     add   rsi, 1
     jmp   scan
out: ret

segment ro
table: dq s0, 5, s1, 6, s2, 7, s3, 8
s0: db "a",0
s1: db "bb",0
s2: db "ccc",0
s3: db "",0
```
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Records

inductive Label
  | start | loop | back | done | reclen | scan | out | table | r1 | r2 | r3 | s0 | s1 | s2 | s3
  deriving DecidableEq, Hashable

def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.alu .xor .w32 (.rm_r (.reg .r12) .r12)),
  .ins (.alu .xor .w32 (.rm_r (.reg .r13) .r13)),
  .label .loop,
  .ins (.alu .cmp .w64 (.rm_i (.reg .r13) 4)),
  .jcc .ae .done,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r13)),
  .ins (.shift .shl .w64 (.reg .rdi) (.imm 4)),
  .ins (.alu .add .w64 (.rm_r (.reg .rdi) .rbx)),
  .call .reclen,
  .label .back,
  .ins (.alu .add .w64 (.rm_r (.reg .r12) .rax)),
  .ins (.alu .add .w64 (.rm_i (.reg .r13) 1)),
  .jmp .loop,
  .label .done,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .r12)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .reclen,
  .ins (.mov .w64 (.r_m .rsi (.sib (some .rdi) none 0))),
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 8))),
  .label .scan,
  .ins (.movzx .w32 .rcx .w8 (.mem (.sib (some .rsi) none 0))),
  .ins (.test .w64 (.reg .rcx) (.reg .rcx)),
  .jcc .e .out,
  .ins (.alu .add .w64 (.rm_i (.reg .rax) 1)),
  .ins (.alu .add .w64 (.rm_i (.reg .rsi) 1)),
  .jmp .scan,
  .label .out,
  .ins .ret,
  .segment .ro,
  .label .table, .quad .s0, .bytes (le64 5),
  .label .r1, .quad .s1, .bytes (le64 6),
  .label .r2, .quad .s2, .bytes (le64 7),
  .label .r3, .quad .s3, .bytes (le64 8),
  .label .s0, .bytes [0x61, 0],
  .label .s1, .bytes [0x62, 0x62, 0],
  .label .s2, .bytes [0x63, 0x63, 0x63, 0],
  .label .s3, .bytes [0]]

asm_program code start .start stack 1

-- 1+5 + 2+6 + 3+7 + 0+8 = 32
#guard exitsWith 32 (runMem linux 400 start)

/-- A record: a pointer to text, then a number. -/
def recShape : ShapeS := .mk 16 (.cons 0 (.str 0) .nil)

/-- The table as one block: four records, sixty-four bytes. -/
def tableShape : ShapeS :=
  .mk 64 (.cons 0 (.str 0) (.cons 8 .any (.cons 16 (.str 0) (.cons 24 .any
    (.cons 32 (.str 0) (.cons 40 .any (.cons 48 (.str 0) (.cons 56 .any .nil))))))))

def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start
    [(Asm.addr code base .table, { shape := tableShape, writable := false }),
     (Asm.addr code base .s0, textBlock [0x61, 0]),
     (Asm.addr code base .s1, textBlock [0x62, 0x62, 0]),
     (Asm.addr code base .s2, textBlock [0x63, 0x63, 0x63, 0]),
     (Asm.addr code base .s3, textBlock [0])]

def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks (Asm.addr code base .table) }

/-- The function takes a pointer to a record. -/
def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .loop,
     inProgram 1 (regs := [(.rbx, .lit (Asm.addr code base .table))])
       (known := [(.was .r13, .range 0 4)])⟩,
   ⟨Asm.addr code base .reclen, inFunction (known := recordAt (.was .rdi) [(0, .str 0), (8, .any)])⟩,
   ⟨Asm.addr code base .scan, inFunction (known := [(.was .rsi, .str 0)])⟩]

asm_checked code start .start stack 1 program pg labels labels blocks blocks

end Tests.Written.Records
