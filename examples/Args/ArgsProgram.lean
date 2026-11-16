import TypedAsm

/-!
# Printing arguments, proved safe

Writes each of its arguments to standard output on a line of its own.

```asm
_start:
     mov   r13, [rsp]            ; how many arguments, the program's name included
     mov   r14d, 1               ; the argument to do next
arg:
     cmp   r14, r13
     jae   done                  ; no more arguments
     mov   rsi, [rsp + r14*8 + 8] ; where this argument's text starts
     mov   rdi, rsi
scan:
     movzx eax, byte ptr [rdi]   ; the byte at the place reached
     test  rax, rax
     jz    found                 ; a zero ends the text
     add   rdi, 1
     jmp   scan
found:
     sub   rdi, rsi              ; how long the text is
     mov   rdx, rdi
     mov   eax, 1                ; `write` the text
     mov   edi, 1
     syscall
     mov   eax, 1                ; `write` the end of the line
     mov   edi, 1
     lea   rsi, [rip + newline]
     mov   edx, 1
     syscall
     add   r14, 1
     jmp   arg
done:
     xor   edi, edi
     mov   eax, 231              ; `exit_group`
     syscall
```

This program looks at what its arguments say: to write one it must know how
long it is, and the only way to find out is to read it byte by byte until
the zero that ends it. Nothing tells the program the length beforehand, so
nothing can tell the types either. What makes each read safe is the read
before it: a byte that was not zero was not the last, so there is another.
The type of `rdi` records exactly that, and `add rdi, 1` is typed only where
it holds.

`lake exe args -- ARG...` runs it in the model; `lake exe args --elf FILE`
writes an executable that Linux can run.
-/

open TypedAsm

namespace Args

/-! ## The program -/

inductive Label
  | start | arg | scan | found | done | newline
  deriving DecidableEq

/-- The data's bytes: the end of a line, filled out to eight bytes. -/
def dataBytes : List Byte := [0x0a, 0, 0, 0, 0, 0, 0, 0]

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w64 (.r_m .r13 (.sib (some .rsp) none 0))),
  .ins (.mov .w32 (.rm_i (.reg .r14) 1)),
  .label .arg,
  .ins (.alu .cmp .w64 (.rm_r (.reg .r14) .r13)),
  .jcc .ae .done,
  .ins (.mov .w64 (.r_m .rsi (.sib (some .rsp) (some (.r14, .s8)) 8))),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsi)),
  .label .scan,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 0))),
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .found,
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 1)),
  .jmp .scan,
  .label .found,
  .ins (.alu .sub .w64 (.rm_r (.reg .rdi) .rsi)),
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ref (.lea .w64 .rsi (.rip 0)) .newline,
  .ins (.mov .w32 (.rm_i (.reg .rdx) 1)),
  .ins .syscall,
  .ins (.alu .add .w64 (.rm_i (.reg .r14) 1)),
  .jmp .arg,
  .label .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .segment .ro,
  .label .newline, .bytes dataBytes]

-- Where the program is loaded, what it puts in memory, where it starts,
-- all from the lines above.
asm_program code start .start

/-- A starting state but for the stack and `rip`: the program in memory, and
with it the data. -/
def prepared : State :=
  Asm.load State.init base code .start

/-- A starting state: `prepared`, given a stack that holds the arguments, with
`rip` at the entry. The first argument is by custom the program's own name. -/
def startArgs (args : List (List Byte)) : State :=
  { prepared.withArgs 0 args with rip := entry }

/-- That state for arguments given as strings. -/
def startWith (args : List String) : State :=
  startArgs (args.map bytesOf)

/-! ## Running it -/

-- Given nothing to print it prints nothing.
#guard wroteAndExited "" 0 (runMemFinal linux 1000 (startWith ["args"]))
#guard wroteAndExited "" 0 (runMemFinal linux 1000 (startWith []))

-- Each argument comes out on a line of its own, whatever its length.
#guard wroteAndExited "one\ntwo words\n\nx\n" 0
  (runMemFinal linux 10000 (startWith ["args", "one", "two words", "", "x"]))

end Args

/-- The program, with what running it takes. -/
def Args.program : Runnable where
  name := "args"
  elf := Asm.elf Args.base Args.code .start
  start := Args.startArgs []
  startArgs := some Args.startArgs
