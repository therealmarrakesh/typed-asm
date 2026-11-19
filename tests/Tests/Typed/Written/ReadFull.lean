import TypedAsm
import TypedAsm.U.Checked

/-!
Read 16 bytes of standard input (fewer only at its end) into a stack buffer
with `read_full(buf, len)`, which goes round over short reads advancing its
pointer; write what was got; exit 0, or 1 on a read error.

_start:
    sub   rsp, 16
    mov   rdi, rsp
    mov   esi, 16
    call  read_full
    test  rax, rax
    js    fail
    mov   rdx, rax
    mov   eax, 1
    mov   edi, 1
    mov   rsi, rsp
    syscall
    xor   edi, edi
    mov   eax, 60
    syscall
fail:
    mov   edi, 1
    mov   eax, 60
    syscall

read_full:                  ; rdi = buffer, rsi = its size; rax = bytes got, or an error
    push  rbx
    push  r12
    push  r13
    mov   rbx, rdi          ; where the next bytes go
    mov   r12, rsi          ; room left
    xor   r13d, r13d        ; bytes got
rf:
    test  r12, r12
    jz    rfdone
    xor   eax, eax
    xor   edi, edi
    mov   rsi, rbx
    mov   rdx, r12
    syscall
    test  rax, rax
    jz    rfdone
    js    rferr
    add   rbx, rax
    sub   r12, rax
    add   r13, rax
    jmp   rf
rfdone:
    mov   rax, r13
rferr:
    pop   r13
    pop   r12
    pop   rbx
    ret
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.ReadFull

inductive Label
  | start | fail | read_full | rf | rfdone | rferr
  deriving DecidableEq, Hashable

def code : List (Asm Label) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 16)),
  .call .read_full,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rsp)),
  .ins .syscall,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .read_full,
  .ins (.push .rbx),
  .ins (.push .r12),
  .ins (.push .r13),
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .r12) .rsi)),
  .ins (.alu .xor .w32 (.rm_r (.reg .r13) .r13)),
  .label .rf,
  .ins (.test .w64 (.reg .r12) (.reg .r12)),
  .jcc .e .rfdone,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rbx)),
  .ins (.mov .w64 (.rm_r (.reg .rdx) .r12)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .rfdone,
  .jcc .s .rferr,
  .ins (.alu .add .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.alu .sub .w64 (.rm_r (.reg .r12) .rax)),
  .ins (.alu .add .w64 (.rm_r (.reg .r13) .rax)),
  .jmp .rf,
  .label .rfdone,
  .ins (.mov .w64 (.rm_r (.reg .rax) .r13)),
  .label .rferr,
  .ins (.pop .r13),
  .ins (.pop .r12),
  .ins (.pop .rbx),
  .ins .ret]

asm_program code start .start stack 6

def startWith (input : List ReadEvent) : State :=
  { start with world := { input := input } }

#guard wroteAndExited "abcdefghijklmnop" 0 (runMemFinal linux 10000
  (startWith [.bytes (bytesOf "abc"), .bytes (bytesOf "defghij"), .bytes (bytesOf "klmnopqrst")]))
#guard wroteAndExited "ab" 0 (runMemFinal linux 10000 (startWith [.bytes (bytesOf "ab")]))
#guard wroteAndExited "" 1 (runMemFinal linux 10000 (startWith [.bytes (bytesOf "ab"), .error .io]))

def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (fun c => c == 0 || c == 1) }

def labels : List U.Label :=
  [⟨entry, inProgram 6⟩,
   ⟨Asm.addr code base .read_full, inFunction (room := 24) (takes := [(.was .rdi, .was .rsi)])⟩,
   -- the buffer is at a value the label names, so many bytes; the pointer is so far into it
   ⟨Asm.addr code base .rf, inFunction (room := 24)
     (pushed := [.saved .rbx, .saved .r12, .saved .r13])
     (takes := [(.named 0, .named 1)])
     (regs := [(.rbx, .named 0 + .was .r13), (.r12, .named 1 + -(Val.was .r13))])
     (known := [(.was .r13, .upTo (.named 1) false)])⟩]

asm_checked code start .start stack 6 program pg labels labels
  exits (fun c => c == 0 || c == 1)

/-- The labels, the room left in the buffer said at the loop to be the whole
of it, however far the pointer has gone. -/
def labelsAll : List U.Label :=
  [⟨entry, inProgram 6⟩,
   ⟨Asm.addr code base .read_full, inFunction (room := 24) (takes := [(.was .rdi, .was .rsi)])⟩,
   ⟨Asm.addr code base .rf, inFunction (room := 24)
     (pushed := [.saved .rbx, .saved .r12, .saved .r13])
     (takes := [(.named 0, .named 1)])
     (regs := [(.rbx, .named 0 + .was .r13), (.r12, .named 1)])
     (known := [(.was .r13, .upTo (.named 1) false)])⟩]

-- a `read` of that many from there may store past the buffer. Refused
#guard !wholeOkWith code .start 6 [] (blocksOf code .start) pg labelsAll (needFuel pg labelsAll [])

end Tests.Written.ReadFull
