import TypedAsm
import TypedAsm.U.Checked

/-!
Exit with the number argv[1] spells in decimal (its leading digits).

_start:
  xor  eax, eax         ; the value
  mov  rcx, [rsp]
  cmp  rcx, 2
  jb   done
  mov  rsi, [rsp+16]    ; argv[1]
digit:
  movzx edx, byte [rsi]
  sub  edx, '0'
  cmp  edx, 9
  ja   done             ; not a digit (the nought at the end among them)
  imul rax, rax, 10
  add  rax, rdx
  add  rsi, 1
  jmp  digit
done:
  mov  edi, eax
  mov  eax, 60
  syscall
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Atoi

inductive L
  | start | digit | done
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.mov .w64 (.r_m .rcx (.sib (some .rsp) none 0))),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rcx) 2)),
  .jcc .b .done,
  .ins (.mov .w64 (.r_m .rsi (.sib (some .rsp) none 16))),
  .label .digit,
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rsi) none 0))),
  .ins (.alu .sub .w32 (.rm_i (.reg .rdx) 48)),
  .ins (.alu .cmp .w32 (.rm_i (.reg .rdx) 9)),
  .jcc .a .done,
  .ins (.imul3 .w64 .rax (.reg .rax) 10),
  .ins (.alu .add .w64 (.rm_r (.reg .rax) .rdx)),
  .ins (.alu .add .w64 (.rm_i (.reg .rsi) 1)),
  .jmp .digit,
  .label .done,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

asm_program code start .start stack 0

def startWith (args : List String) : State := startArgs (args.map bytesOf)

#guard exitsWith 0 (runMem linux 1000 (startWith []))
#guard exitsWith 42 (runMem linux 1000 (startWith ["p", "42"]))
#guard exitsWith 7 (runMem linux 1000 (startWith ["p", "7x9"]))

def pg : Prog := { code := progCode (Asm.table base code) }

def labels : List U.Label :=
  [⟨entry, inProgram 0⟩,
   ⟨Asm.addr code base .digit, inProgram 0 (known := [(.was .rsi, .str (.lit 0))])⟩]

asm_checked code start .start stack 0 program pg labels labels

end Tests.Written.Atoi
