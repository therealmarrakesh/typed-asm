import TypedAsm

/-!
# The lengths of the arguments, by a function, proved safe

Exits with how many bytes its arguments have, all told. Each argument's
length is found by a function, which finds where the argument's text ends
by another; the total is kept on the stack across the calls.

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
     mov   r12, rdi               ; where the text starts, kept across the call
     call  stop
     sub   rdi, r12               ; how far the end is from the start
     mov   rax, rdi
     pop   r12
     ret
stop:                             ; rdi = text; rdi at the zero that ends it
     movzx eax, byte ptr [rdi]
     test  rax, rax
     jz    stopped                ; a zero ends the text
     add   rdi, 1
     jmp   stop
stopped:
     ret
```

The program uses its stack three ways: it keeps its total there, below
the arguments; each call pushes the address it returns to; and `len` pushes
a register it must give back as it found it, so that it can use that
register to keep where the text starts while it calls `stop`. At the
deepest, in `stop`, four slots are in use, so the program asks for four
below its arguments.

`lake exe lengths -- ARG...` runs it in the model; `lake exe lengths --elf
FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Lengths

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | arg | back | done | len | stop | stopped
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
  .call .stop,
  .ins (.alu .sub .w64 (.rm_r (.reg .rdi) .r12)),
  .ins (.mov .w64 (.rm_r (.reg .rax) .rdi)),
  .ins (.pop .r12),
  .ins .ret,
  .label .stop,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 0))),
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .stopped,
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 1)),
  .jmp .stop,
  .label .stopped,
  .ins .ret]

-- Where the program is loaded, what it puts in memory, where it starts,
-- all from the lines above.
asm_program code start .start

/-- A starting state but for the stack and `rip`: the program in memory. -/
def prepared : State :=
  Asm.load State.init base code .start

/-- A starting state: `prepared`, given a stack that holds the arguments and
four free slots below them, with `rip` at the entry. The first argument is
by custom the program's own name. -/
def startArgs (args : List (List Byte)) : State :=
  { prepared.withArgs 4 args with rip := entry }

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
  start := Lengths.startArgs []
  startArgs := some Lengths.startArgs
