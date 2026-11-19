import TypedAsm
import TypedAsm.U.Checked

/-!
_start:
  mov  rax, [rsp]       ; argc
  sub  rsp, 32          ; the digits, and a newline at the end
  mov  ecx, 31          ; where the next digit goes, from the end
  mov  edx, 10
  mov  [rsp+31], dl     ; newline
  mov  r8d, 10
digit:
  test rcx, rcx
  jz   print            ; no room left: stop (the bound, made explicit)
  sub  rcx, 1
  xor  edx, edx
  div  r8               ; rax = rax / 10, rdx = rax % 10
  add  edx, '0'
  mov  [rsp+rcx], dl
  test rax, rax
  jnz  digit
print:
  lea  rsi, [rsp+rcx]   ; write(1, rsp+rcx, 32-rcx)
  mov  edx, 32
  sub  rdx, rcx
  mov  eax, 1
  mov  edi, 1
  syscall
  xor  edi, edi
  mov  eax, 60
  syscall
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Digits

inductive L
  | start | digit | print
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rsp) none 0))),
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 32)),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 31)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 10)),
  .ins (.store8 (.sib (some .rsp) none 31) .rdx),
  .ins (.mov .w32 (.rm_i (.reg .r8) 10)),
  .label .digit,
  .ins (.test .w64 (.reg .rcx) (.reg .rcx)),
  .jcc .e .print,
  .ins (.alu .sub .w64 (.rm_i (.reg .rcx) 1)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.mulDiv .div .w64 (.reg .r8)),
  .ins (.alu .add .w32 (.rm_i (.reg .rdx) 48)),
  .ins (.store8 (.sib (some .rsp) (some (.rcx, .s1)) 0) .rdx),
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .ne .digit,
  .label .print,
  .ins (.lea .w64 .rsi (.sib (some .rsp) (some (.rcx, .s1)) 0)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 32)),
  .ins (.alu .sub .w64 (.rm_r (.reg .rdx) .rcx)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins .syscall,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

asm_program code start .start stack 4

def startWith (args : List String) : State := startArgs (args.map bytesOf)

#guard (runMemFinal linux 10000 (startWith [])).1.world.output == bytesOf "0\n"
#guard (runMemFinal linux 10000 (startWith ["p", "a", "b"])).1.world.output == bytesOf "3\n"
#guard (runMemFinal linux 10000 (startWith ((List.range 12).map toString))).1.world.output == bytesOf "12\n"

/-- A byte that is a digit or the end of a line, written to standard output. -/
def digitOrLine (fd : BitVec 64) (b : BitVec 8) : Bool :=
  fd == 1 && ((48 ≤ b && b ≤ 57) || b == 10)

def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preOut [] (· == 0) (fun _ _ => false) (some digitOrLine) }

def labels : List U.Label :=
  [⟨entry, inProgram 4⟩,
   ⟨Asm.addr code base .digit, inProgram 4 (pushed := [.bytes 32])
      (regs := [(.r8, 10)]) (known := [(.was .rcx, .upTo (.lit 31) false)])
      (rows := [bytesAt (stackAt 4 [.bytes 32] (.was .rcx))
        (.add (.lit 31) (-(Val.was .rcx))) (.range 48 57),
        bytesAt (stackAt 4 [.bytes 32] 31) 1 (.range 10 10)])⟩]

asm_checked code start .start stack 4 program pg labels labels exits (· == 0)
  writes (fun _ _ => false) said [] each digitOrLine

/-- The labels, the digits stored said to be bytes from 48 to 58. -/
def labelsColon : List U.Label :=
  [⟨entry, inProgram 4⟩,
   ⟨Asm.addr code base .digit, inProgram 4 (pushed := [.bytes 32])
      (regs := [(.r8, 10)]) (known := [(.was .rcx, .upTo (.lit 31) false)])
      (rows := [bytesAt (stackAt 4 [.bytes 32] (.was .rcx))
        (.add (.lit 31) (-(Val.was .rcx))) (.range 48 58),
        bytesAt (stackAt 4 [.bytes 32] 31) 1 (.range 10 10)])⟩]

-- a byte of 58 is no digit, and the program is to write only digits and the
-- end of a line. Refused
#guard !wholeOkWith code .start 4 [] (blocksOf code .start) pg labelsColon (needFuel pg labelsColon [])

end Tests.Written.Digits

