import TypedAsm

/-!
# The lengths of the arguments, by a function, proved safe

Exits with how many bytes its arguments have, all told. Each argument's
length is found by a function, which keeps where the text starts in a
register it saves on the stack and goes along the text in a loop; the
total is kept on the stack across the calls.

```asm
_start:
     mov   r13, [rsp]             ; how many arguments, the program's name included
     mov   r14d, 1                ; the argument to do next
     xor   eax, eax
     push  rax                    ; the total so far, on the stack
arg:
     cmp   r14, r13
     jae   done                   ; no more arguments
     mov   rdi, [rsp + r14*8 + 16] ; where this argument's text starts
     call  len
back:
     add   [rsp], rax             ; added to the total
     add   r14, 1
     jmp   arg
done:
     pop   rdi                    ; the total is the status
     mov   eax, 60                ; `exit`
     syscall
len:                              ; rdi = text; its length in rax
     push  r12                    ; the caller's, given back at the end
     mov   r12, rdi               ; where the text starts
scan:
     movzx eax, byte ptr [rdi]
     test  rax, rax
     jz    found                  ; a zero ends the text
     add   rdi, 1
     jmp   scan
found:
     sub   rdi, r12               ; how far the end is from the start
     mov   rax, rdi
     pop   r12
     ret
```

The program uses its stack three ways: it keeps its total there, below
the arguments; the call pushes the address it returns to; and `len` pushes
a register it must give back as it found it, so that it can use that
register to keep where the text starts. At the deepest, in the loop, three
slots are in use; the program asks for four below its arguments.

`lake exe lengths -- ARG...` runs it in the model; `lake exe lengths --elf
FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Lengths

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | arg | back | done | len | scan | found
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w64 (.r_m .r13 (.sib (some .rsp) none 0))),
  .ins (.mov .w32 (.rm_i (.reg .r14) 1)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.push .rax),
  .label .arg,
  .ins (.alu .cmp .w64 (.rm_r (.reg .r14) .r13)),
  .jcc .ae .done,
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rsp) (some (.r14, .s8)) 16))),
  .call .len,
  .label .back,
  .ins (.alu .add .w64 (.rm_r (.mem (.sib (some .rsp) none 0)) .rax)),
  .ins (.alu .add .w64 (.rm_i (.reg .r14) 1)),
  .jmp .arg,
  .label .done,
  .ins (.pop .rdi),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .len,
  .ins (.push .r12),
  .ins (.mov .w64 (.rm_r (.reg .r12) .rdi)),
  .label .scan,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 0))),
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .found,
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 1)),
  .jmp .scan,
  .label .found,
  .ins (.alu .sub .w64 (.rm_r (.reg .rdi) .r12)),
  .ins (.mov .w64 (.rm_r (.reg .rax) .rdi)),
  .ins (.pop .r12),
  .ins .ret]

-- Where the program is loaded, what it puts in memory, where it starts,
-- all from the lines above.
asm_program code start .start stack 4

/-- That state for arguments given as strings. -/
def startWith (args : List String) : State :=
  startArgs (args.map bytesOf)

/-! ## Running it -/

-- With nothing but its name, or nothing at all, the total is nought.
#guard exitsWith 0 (runMem linux 1000 (startWith ["lengths"]))
#guard exitsWith 0 (runMem linux 1000 (startWith []))

-- Three bytes, nine, none, six and eight: twenty-six.
#guard exitsWith 26
  (runMem linux 10000 (startWith ["lengths", "one", "two words", "", "héllo", "--flag=3"]))

end Lengths

/-- The program, with what running it takes. -/
def Lengths.program : Runnable where
  name := "lengths"
  elf := Asm.elf Lengths.base Lengths.code .start
  startArgs := Lengths.startArgs
