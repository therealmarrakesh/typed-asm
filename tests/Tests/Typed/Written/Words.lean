import TypedAsm
import TypedAsm.U.Checked

/-!
_start:
  sub  rsp, 64          ; the buffer
  xor  r12d, r12d       ; words so far
  xor  r13d, r13d       ; 1 while inside a word
chunk:
  xor  eax, eax         ; read(0, rsp, 64)
  xor  edi, edi
  mov  rsi, rsp
  mov  edx, 64
  syscall
  test rax, rax
  jle  done             ; end of input, or an error
  xor  ecx, ecx         ; index into the chunk
byte:
  cmp  rcx, rax
  jae  chunk
  movzx edx, byte [rsp+rcx]
  add  rcx, 1
  cmp  edx, ' '
  je   space
  cmp  edx, 10
  je   space
  cmp  edx, 9
  je   space
  test r13, r13
  jnz  byte             ; still in the same word
  mov  r13d, 1
  add  r12, 1
  jmp  byte
space:
  xor  r13d, r13d
  jmp  byte
done:
  mov  edi, r12d
  and  edi, 255
  mov  eax, 60
  syscall
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Words

inductive L
  | start | chunk | byte | space | done
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 64)),
  .ins (.alu .xor .w32 (.rm_r (.reg .r12) .r12)),
  .ins (.alu .xor .w32 (.rm_r (.reg .r13) .r13)),
  .label .chunk,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rsp)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 64)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rcx) .rcx)),
  .label .byte,
  .ins (.alu .cmp .w64 (.rm_r (.reg .rcx) .rax)),
  .jcc .ae .chunk,
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rsp) (some (.rcx, .s1)) 0))),
  .ins (.alu .add .w64 (.rm_i (.reg .rcx) 1)),
  .ins (.alu .cmp .w32 (.rm_i (.reg .rdx) 32)),
  .jcc .e .space,
  .ins (.alu .cmp .w32 (.rm_i (.reg .rdx) 10)),
  .jcc .e .space,
  .ins (.alu .cmp .w32 (.rm_i (.reg .rdx) 9)),
  .jcc .e .space,
  .ins (.test .w64 (.reg .r13) (.reg .r13)),
  .jcc .ne .byte,
  .ins (.mov .w32 (.rm_i (.reg .r13) 1)),
  .ins (.alu .add .w64 (.rm_i (.reg .r12) 1)),
  .jmp .byte,
  .label .space,
  .ins (.alu .xor .w32 (.rm_r (.reg .r13) .r13)),
  .jmp .byte,
  .label .done,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .r12)),
  .ins (.alu .and .w32 (.rm_i (.reg .rdi) 255)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

asm_program code start .start stack 8

def startWith (input : List ReadEvent) : State := { start with world := { input := input } }

#guard exitsWith 0 (runMem linux 10000 (startWith []))
#guard exitsWith 3 (runMem linux 10000 (startWith [.bytes (bytesOf "one two\tthree\n")]))
#guard exitsWith 3 (runMem linux 10000 (startWith [.bytes (bytesOf "  a b"), .bytes (bytesOf "c d ")]))

def pg : Prog := { code := progCode (Asm.table base code), pre := preExits (fun c => decide (c < 256)) }

def labels : List U.Label :=
  [⟨entry, inProgram 8⟩,
   ⟨Asm.addr code base .chunk, inProgram 8 (pushed := [.bytes 64])⟩,
   ⟨Asm.addr code base .byte, inProgram 8 (pushed := [.bytes 64])
      (known := [(.was .rax, .upTo (.lit 64) false), (.was .rcx, .upTo (.was .rax) false)])⟩]

asm_checked code start .start stack 8 program pg labels labels exits (fun c => decide (c < 256))

/-- The labels, the count a `read` handed back said to be at most so much. -/
def labelsMost (most : BitVec 64) : List U.Label :=
  [⟨entry, inProgram 8⟩,
   ⟨Asm.addr code base .chunk, inProgram 8 (pushed := [.bytes 64])⟩,
   ⟨Asm.addr code base .byte, inProgram 8 (pushed := [.bytes 64])
      (known := [(.was .rax, .upTo (.lit most) false), (.was .rcx, .upTo (.was .rax) false)])⟩]

-- at most seventy-two: the bytes read would be of the buffer or of the eight
-- after it, the count of arguments, which the program has too
#guard wholeOkWith code .start 8 [] (blocksOf code .start) pg (labelsMost 72) (needFuel pg (labelsMost 72) [])
-- at most seventy-three: a byte past those. Refused
#guard !wholeOkWith code .start 8 [] (blocksOf code .start) pg (labelsMost 73) (needFuel pg (labelsMost 73) [])

end Tests.Written.Words
