import TypedAsm

/-!
# Arithmetic, narrow stack access and indirect transfers, proved safe

Exercises the instructions the other examples do not: multiply and divide,
shifts and rotates, `neg`, `not`, `popcnt`, `bswap`, sign extension,
conditional move and set, arithmetic whose destination is in memory, 32-bit
and byte access to stack slots, a call through a stack slot, a jump through
a register, and `ud2`.

```asm
_start:
     lea   rdi, [rip + record]   ; the record is one page after the load address
     lea   rax, [rip + compute]
     sub   rsp, 8
     mov   [rsp], rax            ; a function pointer in a stack slot
     call  qword ptr [rsp]
afterCall:
     add   rsp, 8
     mov   edi, eax
     lea   rcx, [rip + finish]
     jmp   rcx
finish:
     add   dword ptr [rip + record+12], 1   ; a global, addressed directly
     mov   rsi, qword ptr [rip + record]
     mov   eax, 60               ; Linux `exit`
     syscall
trap:
     ud2                         ; nothing jumps here
compute:                         ; rdi = pointer to the record; result in rax
     sub   rsp, 16               ; two locals
     mov   dword ptr [rsp], 7
     mov   dword ptr [rsp+8], 3
     mov   eax, dword ptr [rsp]
     imul  eax, dword ptr [rsp+8]   ; 21
     add   dword ptr [rsp+8], eax   ; local 1 = 24
     add   qword ptr [rdi], 2       ; first field = 7
     mov   ecx, dword ptr [rsp+8]
     shl   ecx, 2                   ; 96
     mov   byte ptr [rsp+4], cl
     movzx edx, byte ptr [rsp+4]
     neg   edx
     not   edx                      ; 95
     popcnt esi, edx                ; 6
     bswap edx
     shr   edx, 24                  ; 95 again
     mov   eax, edx
     cdq
     mov   ecx, 9
     idiv  ecx                      ; eax = 10, edx = 5
     imul  eax, eax, 3              ; 30
     cmp   eax, edx
     cmovg edx, eax                 ; 30
     setg  byte ptr [rdi+8]         ; second field = 1
     movsxd rcx, dword ptr [rdi+8]
     add   eax, esi                 ; 36
     add   eax, ecx                 ; 37
     sub   eax, dword ptr [rdi]     ; 30
     mov   ecx, 2
     mul   ecx                      ; 60
     cqo
     xor   edx, edx
     div   rcx                      ; 30
     test  dword ptr [rsp+8], 8
     cmp   dword ptr [rsp+8], 24
     rol   eax, cl                  ; 120
     add   rsp, 16
     ret
```

The program is laid out for the addresses of the ELF file it can be written
to: code at `0x4000b0`, the record at `0x401000`. `lake exe ops` runs it in
the model; `lake exe ops --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Ops

/-! ## The program -/

def rspSlot (disp : BitVec 32) : Mem := .sib (some .rsp) none disp

def field (disp : BitVec 32) : Mem := .sib (some .rdi) none disp

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | afterCall | finish | trap | compute | record
  deriving DecidableEq

/-- The record's two fields. -/
def record : List (BitVec 64) := [5, 0]

/-- The record's bytes, as they sit in the file and in memory. -/
def recordBytes : List Byte := record.flatMap le64

/-- The program. Its `rip`-relative operands name what they reach by label:
the record in the data, and two places in the code whose addresses it takes. -/
def code : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .record,
  .ref (.lea .w64 .rax (.rip 0)) .compute,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 8)),
  .ins (.mov .w64 (.rm_r (.mem (rspSlot 0)) .rax)),
  .ins (.call (.ind (.mem (rspSlot 0)))),
  .label .afterCall,
  .ins (.alu .add .w64 (.rm_i (.reg .rsp) 8)),
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ref (.lea .w64 .rcx (.rip 0)) .finish,
  .ins (.jmp (.ind (.reg .rcx))),
  .label .finish,
  .ref (.alu .add .w32 (.rm_i (.mem (.rip 0)) 1)) .record 12,
  .ref (.mov .w64 (.r_m .rsi (.rip 0))) .record,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .trap,
  .ins .ud2,
  .label .compute,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .ins (.mov .w32 (.rm_i (.mem (rspSlot 0)) 7)),
  .ins (.mov .w32 (.rm_i (.mem (rspSlot 8)) 3)),
  .ins (.mov .w32 (.r_m .rax (rspSlot 0))),
  .ins (.imul2 .w32 .rax (.mem (rspSlot 8))),
  .ins (.alu .add .w32 (.rm_r (.mem (rspSlot 8)) .rax)),
  .ins (.alu .add .w64 (.rm_i (.mem (field 0)) 2)),
  .ins (.mov .w32 (.r_m .rcx (rspSlot 8))),
  .ins (.shift .shl .w32 (.reg .rcx) (.imm 2)),
  .ins (.store8 (rspSlot 4) .rcx),
  .ins (.movzx .w32 .rdx .w8 (.mem (rspSlot 4))),
  .ins (.unary .neg .w32 (.reg .rdx)),
  .ins (.unary .not .w32 (.reg .rdx)),
  .ins (.popcnt .w32 .rsi (.reg .rdx)),
  .ins (.bswap .w32 .rdx),
  .ins (.shift .shr .w32 (.reg .rdx) (.imm 24)),
  .ins (.mov .w32 (.rm_r (.reg .rax) .rdx)),
  .ins .cdq,
  .ins (.mov .w32 (.rm_i (.reg .rcx) 9)),
  .ins (.mulDiv .idiv .w32 (.reg .rcx)),
  .ins (.imul3 .w32 .rax (.reg .rax) 3),
  .ins (.alu .cmp .w32 (.rm_r (.reg .rax) .rdx)),
  .ins (.cmov .g .w32 .rdx (.reg .rax)),
  .ins (.setcc .g (.mem (field 8))),
  .ins (.movsxd .rcx (.mem (field 8))),
  .ins (.alu .add .w32 (.rm_r (.reg .rax) .rsi)),
  .ins (.alu .add .w32 (.rm_r (.reg .rax) .rcx)),
  .ins (.alu .sub .w32 (.r_m .rax (field 0))),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 2)),
  .ins (.mulDiv .mul .w32 (.reg .rcx)),
  .ins .cqo,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.mulDiv .div .w64 (.reg .rcx)),
  .ins (.test .w32 (.mem (rspSlot 8)) (.imm 8)),
  .ins (.alu .cmp .w32 (.rm_i (.mem (rspSlot 8)) 24)),
  .ins (.shift .rol .w32 (.reg .rax) .cl),
  .ins (.alu .add .w64 (.rm_i (.reg .rsp) 16)),
  .ins .ret,
  .segment .rw,
  .label .record, .bytes recordBytes]

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it the
-- record in writable memory, and four free stack slots below `rsp`.
asm_program code start .start stack 4 named "ops"

/-! ## Running it -/

-- The arithmetic in the listing comes to 120, whether instructions come
-- from the table or are decoded from memory.
#guard exitsWith 120 (run fetch linux 100 start)
#guard exitsWith 120 (runMem linux 100 start)

end Ops

