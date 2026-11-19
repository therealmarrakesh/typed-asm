import TypedAsm
import TypedAsm.U.Checked

/-!
# A function that carves pieces off memory it is lent

```asm
_start:
     mov   eax, 9                ; a page
     xor   edi, edi
     mov   esi, 4096
     mov   edx, 3
     mov   r10d, 0x22
     mov   r8, -1
     xor   r9d, r9d
     syscall
     test  rax, rax
     js    fail
     mov   rbx, rax              ; the arena: rbx, r12 bytes
     mov   r12d, 4096
     mov   rdi, rbx              ; a piece of 16
     mov   rsi, r12
     mov   edx, 16
     call  carve
     test  rax, rax
     jz    fail
     mov   qword [rax], 1
     mov   qword [rax + 8], 2
     add   rbx, 16
     sub   r12, 16
     mov   rdi, rbx              ; and of 32
     mov   rsi, r12
     mov   edx, 32
     call  carve
     test  rax, rax
     jz    fail
     mov   qword [rax + 24], 3
     xor   edi, edi
     mov   eax, 60
     syscall
fail:
     mov   edi, 1
     mov   eax, 60
     syscall
carve:                           ; rdi, rsi bytes; rdx wanted
     cmp   rdx, rsi
     ja    none
     mov   rax, rdi
     ret
none:
     xor   eax, eax
     ret
```

`carve` is lent the arena and does not give it back as it was: either it
gives it back whole and returns nought, or it hands its caller the piece at
the address it returns and gives back the rest after it.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Arena

inductive L
  | start | fail | carve | none
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .ins (.mov .w32 (.rm_i (.reg .r10) 0x22)),
  .ins (.mov .w64 (.rm_i (.reg .r8) (-1))),
  .ins (.alu .xor .w32 (.rm_r (.reg .r9) .r9)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .r12) 4096)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .r12)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 16)),
  .call .carve,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .fail,
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rax) none 0)) 1)),
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rax) none 8)) 2)),
  .ins (.alu .add .w64 (.rm_i (.reg .rbx) 16)),
  .ins (.alu .sub .w64 (.rm_i (.reg .r12) 16)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .r12)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 32)),
  .call .carve,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .fail,
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rax) none 24)) 3)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .carve,
  .ins (.alu .cmp .w64 (.rm_r (.reg .rdx) .rsi)),
  .jcc .a .none,
  .ins (.mov .w64 (.rm_r (.reg .rax) .rdi)),
  .ins .ret,
  .label .none,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret]

asm_program code start .start stack 1

-- with nothing said of the world outside, the model's `mmap` refuses
#guard exitsWith 1 (runMem linux 1000 start)

def pg : Prog :=
  { code := progCode (Asm.table base code), pre := preExits (fun c => c == 0 || c == 1) }

/-- `carve`: the arena it is lent, given back whole with nought; or the piece
at the address it returns and the rest after it. -/
def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .carve,
     inFunction (uses := [(.was .rdi, .was .rsi)])
       (results := [(.rax, 0)]) (gives := [(.was .rdi, .was .rsi)])
       (orReturns := [returnsWith (results := [(.rax, .was .rdi)])
         (gives := [(.was .rdi, .was .rdx),
                    (.add (.was .rdi) (.was .rdx), .add (.was .rsi) (-(Val.was .rdx)))])])⟩]

asm_checked code start .start stack 1 program pg labels labels exits (fun c => c == 0 || c == 1)

/-- The labels, the rest `carve` gives back said to be as large as the whole
arena, not less the piece carved off. -/
def labelsWhole : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .carve,
     inFunction (uses := [(.was .rdi, .was .rsi)])
       (results := [(.rax, 0)]) (gives := [(.was .rdi, .was .rsi)])
       (orReturns := [returnsWith (results := [(.rax, .was .rdi)])
         (gives := [(.was .rdi, .was .rdx),
                    (.add (.was .rdi) (.was .rdx), .was .rsi)])])⟩]

-- Refused
#guard !wholeOkWith code .start 1 [] (blocksOf code .start) pg labelsWhole (needFuel pg labelsWhole [])

end Tests.Written.Arena
