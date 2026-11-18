import TypedAsm
import TypedAsm.U.Checked

/-!
head -c 100: copy at most 100 bytes of standard input to standard output,
handling short reads and short writes; exit 0, or 1 on an error.

_start:
    sub   rsp, 64         ; buffer
    mov   r12d, 100       ; bytes still to copy
loop:                     ; r12 in 0..100
    test  r12, r12
    jz    done
    xor   eax, eax        ; read
    xor   edi, edi
    mov   rsi, rsp
    mov   edx, 64
    cmp   r12, rdx
    cmovb rdx, r12        ; at most what is left
    syscall
    test  rax, rax
    jz    done            ; end of input
    js    fail
    sub   r12, rax
    mov   rbx, rax        ; bytes in the buffer
    xor   r13d, r13d      ; bytes of them written
wloop:                    ; rbx in 1..64, r13 < rbx
    mov   eax, 1          ; write
    mov   edi, 1
    lea   rsi, [rsp+r13]
    mov   rdx, rbx
    sub   rdx, r13
    syscall
    test  rax, rax
    jle   fail
    add   r13, rax
    cmp   r13, rbx
    jb    wloop
    jmp   loop
done:
    xor   edi, edi
    mov   eax, 60
    syscall
fail:
    mov   edi, 1
    mov   eax, 60
    syscall
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Head

inductive Label
  | start | loop | wloop | done | fail
  deriving DecidableEq, Hashable

def code : List (Asm Label) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 64)),
  .ins (.mov .w32 (.rm_i (.reg .r12) 100)),
  .label .loop,
  .ins (.test .w64 (.reg .r12) (.reg .r12)),
  .jcc .e .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rsp)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 64)),
  .ins (.alu .cmp .w64 (.rm_r (.reg .r12) .rdx)),
  .ins (.cmov .b .w64 .rdx (.reg .r12)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .done,
  .jcc .s .fail,
  .ins (.alu .sub .w64 (.rm_r (.reg .r12) .rax)),
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .r13) .r13)),
  .label .wloop,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.lea .w64 .rsi (.sib (some .rsp) (some (.r13, .s1)) 0)),
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rbx)),
  .ins (.alu .sub .w64 (.rm_r (.reg .rdx) .r13)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .fail,
  .ins (.alu .add .w64 (.rm_r (.reg .r13) .rax)),
  .ins (.alu .cmp .w64 (.rm_r (.reg .r13) .rbx)),
  .jcc .b .wloop,
  .jmp .loop,
  .label .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

asm_program code start .start stack 8

def startWith (input : List ReadEvent) (fates : List TypedAsm.Fate := []) : State :=
  { start with world := { input := input, fates := fates } }

#guard wroteAndExited "" 0 (runMemFinal linux 1000 start)
#guard wroteAndExited "hello" 0 (runMemFinal linux 1000 (startWith [.bytes (bytesOf "hello")]))
#guard (runMemFinal linux 100000
  (startWith [.bytes (List.replicate 150 0x41)])).1.world.output == List.replicate 100 0x41
#guard wroteAndExited "hello" 0 (runMemFinal linux 1000
  (startWith [.bytes (bytesOf "hello")] [.short 2, .short 1]))

def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (fun c => c == 0 || c == 1) }

def labels : List U.Label :=
  [⟨entry, inProgram 8⟩,
   ⟨Asm.addr code base .loop, inProgram 8 (pushed := [.bytes 64])
     (known := [(.was .r12, .range 0 100)])⟩,
   ⟨Asm.addr code base .wloop, inProgram 8 (pushed := [.bytes 64])
     (known := [(.was .r12, .range 0 100), (.was .rbx, .range 1 64),
       (.was .r13, .upTo (.was .rbx) true)])⟩]

asm_checked code start .start stack 8 program pg labels labels
  exits (fun c => c == 0 || c == 1)

end Tests.Written.Head
