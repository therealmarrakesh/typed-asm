import TypedAsm

/-!
# A function that hands back a page it made, proved safe

Calls a function that asks the kernel for a page and returns its address,
reads standard input into the page, turns every bit of it over a byte at a
time, writes the page out, and gives it back. It exits with status 0, or 1
if the kernel has no memory to give.

```asm
_start:
     call  page                  ; a page, at an address in `rax`
back:
     mov   rbx, rax              ; the page: ours
     mov   [rbx], rbx            ; its first word: its own address
     xor   eax, eax              ; `read` into it, up to all of it
     xor   edi, edi
     mov   rsi, rbx
     mov   edx, 4096
     syscall
     xor   ecx, ecx
loop:
     cmp   rcx, 4096
     jae   done
     movzx eax, byte ptr [rbx + rcx]
     xor   eax, 0xff
     mov   [rbx + rcx], al
     add   rcx, 1
     jmp   loop
done:
     mov   eax, 1                ; `write` it out
     mov   edi, 1
     mov   rsi, rbx
     mov   edx, 4096
     syscall
     mov   eax, 11               ; `munmap`: give the page back
     mov   rdi, rbx
     mov   esi, 4096
     syscall
     xor   edi, edi
     mov   eax, 231              ; `exit_group`
     syscall
page:                            ; returns a page nobody else has
     mov   eax, 9                ; `mmap`
     xor   edi, edi
     mov   esi, 4096
     mov   edx, 3
     mov   r10d, 0x22
     mov   r8, -1
     xor   r9d, r9d
     syscall
     test  rax, rax
     js    fail
     ret
fail:
     mov   edi, 1
     mov   eax, 231
     syscall
```

The function `page` cannot say in its signature where the page it returns
will be: the kernel decides. Its signature says instead that whatever
address `x` comes back in `rax`, the caller owns a page there; and the place
it returns to is typed for every `x`. Just before returning the function
says which `x` it is returning with.

Two smaller things are shown on the way. The program stores the page's own
address in its first word, so that word is no longer typed as a number; the
`read` that follows may still store over it, and afterwards it is a number
again. And the loop reaches the page a byte at a time, through an index
known only to be less than 4096.

`lake exe fresh` runs it in the model on standard input;
`lake exe fresh --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Fresh

/-! ## The program -/

inductive Label
  | start | back | loop | done | page | fail
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .call .page,
  .label .back,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rbx) none 0)) .rbx)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rbx)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 4096)),
  .ins .syscall,
  .ins (.alu .xor .w32 (.rm_r (.reg .rcx) .rcx)),
  .label .loop,
  .ins (.alu .cmp .w64 (.rm_i (.reg .rcx) 4096)),
  .jcc .ae .done,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rbx) (some (.rcx, .s1)) 0))),
  .ins (.alu .xor .w32 (.rm_i (.reg .rax) 0xff)),
  .ins (.store8 (.sib (some .rbx) (some (.rcx, .s1)) 0) .rax),
  .ins (.alu .add .w64 (.rm_i (.reg .rcx) 1)),
  .jmp .loop,
  .label .done,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rbx)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 4096)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 11)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins .syscall,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .label .page,
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .ins (.mov .w32 (.rm_i (.reg .r10) 0x22)),
  .ins (.mov .w64 (.rm_i (.reg .r8) (-1))),
  .ins (.alu .xor .w32 (.rm_r (.reg .r9) .r9)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins .ret,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

def fetch : Fetch := Asm.fetch base code

/-- What the program puts in memory, line by line. -/
def parts : List (Nat × Perm × List Byte) := Asm.parts base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump and call reaches the label it names.
#guard Asm.offsetsFit base code

/-- The starting state but for `rip`: the program in memory, and with it one
free stack slot, for the return address of the one call. -/
def prepared : State :=
  ((Asm.load State.init base code).setPerm 0x7ffffff8 8 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. Nothing is waiting
to be read, and every request for memory is refused. -/
def start : State :=
  { prepared with rip := entry }

/-- A page for each request for memory, one after another. -/
def pages : Nat → Option (BitVec 64) :=
  fun i => some (BitVec.ofNat 64 (0x10000000 + 4096 * i))

/-- The starting state with the given input waiting and the given answers to
requests for memory. -/
def startWith (input : List Byte) (place : Nat → Option (BitVec 64) := pages) : State :=
  { start with world := { input := [.bytes input], place := place } }

/-! ## Running it -/

def exitedWith (out : List Byte) (code : BitVec 32) (r : State × Outcome) : Bool :=
  r.1.world.output == out && exitsWith code r.2

-- With no memory to be had it exits with status 1, having written nothing.
#guard exitedWith [] 1 (runMemFinal linux 100000 start)

-- Every bit is turned over: the three bytes read, the byte of the page's
-- address that they did not reach, and the zeros after it.
#guard exitedWith ([0xfe, 0xfd, 0x0f, 0xef] ++ List.replicate 4092 0xff) 0
  (runMemFinal linux 100000 (startWith [1, 2, 0xf0]))

-- With nothing to read, what is turned over is the page's own address in
-- its first word, and zeros.
#guard exitedWith ([0xff, 0xff, 0xff, 0xef] ++ List.replicate 4092 0xff) 0
  (runMemFinal linux 100000 (startWith []))

-- By the end the page is inaccessible again.
#guard (runMemFinal linux 100000 (startWith [])).1.perm 0x10000000 == .none

end Fresh

/-- The program, with what running it takes. -/
def Fresh.program : Runnable where
  name := "fresh"
  elf := Asm.elf Fresh.base Fresh.code .start
  start := Fresh.start
  readsInput := true
