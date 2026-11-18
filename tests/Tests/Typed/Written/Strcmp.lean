import TypedAsm
import TypedAsm.U.Checked

/-!
_start:
  mov rcx, [rsp]
  cmp rcx, 3
  jb  few
  mov rdi, [rsp+16]     ; argv[1]
  mov rsi, [rsp+24]     ; argv[2]
  call strcmp
  mov edi, eax          ; 0 equal, 1 not
  mov eax, 60
  syscall
few:
  mov edi, 2
  mov eax, 60
  syscall
strcmp:                 ; rdi, rsi: text; eax = 0 if equal, else 1
  movzx eax, byte [rdi]
  movzx edx, byte [rsi]
  cmp eax, edx
  jne differ
  test eax, eax
  jz  same
  add rdi, 1
  add rsi, 1
  jmp strcmp
differ:
  mov eax, 1
  ret
same:
  xor eax, eax
  ret
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Strcmp

inductive L
  | start | few | strcmp | differ | same
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ins (.mov .w64 (.r_m .rcx (.sib (some .rsp) none 0))),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rcx) 3)),
  .jcc .b .few,
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rsp) none 16))),
  .ins (.mov .w64 (.r_m .rsi (.sib (some .rsp) none 24))),
  .call .strcmp,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .few,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 2)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .strcmp,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 0))),
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rsi) none 0))),
  .ins (.alu .cmp .w32 (.rm_r (.reg .rax) .rdx)),
  .jcc .ne .differ,
  .ins (.test .w32 (.reg .rax) (.reg .rax)),
  .jcc .e .same,
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 1)),
  .ins (.alu .add .w64 (.rm_i (.reg .rsi) 1)),
  .jmp .strcmp,
  .label .differ,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .ret,
  .label .same,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret]

asm_program code start .start stack 1

def startWith (args : List String) : State := startArgs (args.map bytesOf)

#guard exitsWith 2 (runMem linux 1000 (startWith []))
#guard exitsWith 2 (runMem linux 1000 (startWith ["p", "a"]))
#guard exitsWith 0 (runMem linux 1000 (startWith ["p", "abc", "abc"]))
#guard exitsWith 1 (runMem linux 1000 (startWith ["p", "abc", "abd"]))
#guard exitsWith 1 (runMem linux 1000 (startWith ["p", "ab", "abc"]))
#guard exitsWith 0 (runMem linux 1000 (startWith ["p", "", ""]))

def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (fun c => c == 0 || c == 1 || c == 2) }

def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .strcmp, inFunction
      (known := [(.was .rdi, .str (.lit 0)), (.was .rsi, .str (.lit 0))])
      (returns := [(.given .rax, .range 0 1)])⟩]

asm_checked code start .start stack 1 program pg labels labels
  exits (fun c => c == 0 || c == 1 || c == 2)

end Tests.Written.Strcmp
