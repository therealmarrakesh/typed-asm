import TypedAsm

/-!
# Using only what `getrandom` delivered, proved safe

Asks the kernel for 512 random bytes and writes to standard output the bytes
it was given: as many as the call says it stored, which may be fewer than
were asked for.

```asm
_start:
     lea   rdi, [rip + buffer]
     mov   esi, 512
     xor   edx, edx              ; no flags
     mov   eax, 318              ; `getrandom`
     syscall
     test  rax, rax
     jle   fail                  ; an error, or nothing
     mov   rdx, rax              ; as many bytes as were stored
     lea   rsi, [rip + buffer]
     mov   edi, 1                ; to standard output
     mov   eax, 1                ; `write`
     syscall
     xor   edi, edi
     mov   eax, 60               ; `exit`
     syscall
fail:
     mov   edi, 1
     mov   eax, 60
     syscall
```

The kernel may stop a `getrandom` for more than 256 bytes before it has
delivered them all, and says how many it delivered. This program passes that
number on to `write`. `careless` below is the same program with one
instruction changed, `mov edx, 512` for `mov rdx, rax`: it writes all 512
bytes whatever it was given. Both are safe. Only this one writes nothing but
bytes the kernel supplied.

The buffer is full of `.` in the file, so a byte the kernel did not replace
shows in the output.
-/

open TypedAsm

namespace Random

/-! ## The program -/

inductive Label
  | start | fail | buffer
  deriving DecidableEq, Hashable

/-- The buffer's bytes as they sit in the file: 512 full stops. -/
def bufferBytes : List Byte := List.replicate 512 0x2e

/-- The program, with the instruction that sets the number of bytes to write. -/
def codeWith (count : Instr) : List (Asm Label) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .buffer,
  .ins (.mov .w32 (.rm_i (.reg .rsi) 512)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 318)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .fail,
  .ins count,
  .ref (.lea .w64 .rsi (.rip 0)) .buffer,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .syscall,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .segment .rw,
  .label .buffer, .bytes bufferBytes]

/-- The program: it writes as many bytes as `getrandom` said it stored. -/
def code : List (Asm Label) := codeWith (.mov .w64 (.rm_r (.reg .rdx) .rax))

/-- The same, but it writes 512 bytes whatever `getrandom` said. -/
def careless : List (Asm Label) := codeWith (.mov .w32 (.rm_i (.reg .rdx) 512))

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it the
-- buffer in writable memory. The program uses no stack.
asm_program code start .start stack 0 named "random"

/-- The starting state with the kernel set to do `fates` with the calls for
randomness, and to supply the bytes `random`. -/
def startWith (fates : List Fate) (random : Nat → Byte) : State :=
  { start with world := { fates := fates, random := random } }

/-- The careless program's starting state, likewise. -/
def carelessWith (fates : List Fate) (random : Nat → Byte) : State :=
  { (Asm.load State.init (Asm.base careless) careless .start).setReg .rsp 0x80000000 with
    rip := Asm.addr careless (Asm.base careless) .start
    world := { fates := fates, random := random } }

/-! ## Running it -/

/-- The bytes the kernel supplies in these runs: `A` every time. -/
def letters : Nat → Byte := fun _ => 0x41

def repeated (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

-- Given everything, it writes 512 bytes from the kernel.
#guard wroteAndExited (repeated 'A' 512) 0 (runMemFinal linux 1000 (startWith [] letters))

-- Given 100, it writes those 100 and no more.
#guard wroteAndExited (repeated 'A' 100) 0
  (runMemFinal linux 1000 (startWith [.short 100] letters))

-- The careless program, given 100, writes them and then 412 bytes that were
-- in the buffer all along. It is as safe as the other, and wrong.
#guard wroteAndExited (repeated 'A' 100 ++ repeated '.' 412) 0
  (runMemFinal linux 1000 (carelessWith [.short 100] letters))

-- Given everything, the two cannot be told apart.
#guard wroteAndExited (repeated 'A' 512) 0 (runMemFinal linux 1000 (carelessWith [] letters))

end Random

