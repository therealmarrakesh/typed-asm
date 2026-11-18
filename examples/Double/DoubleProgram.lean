import TypedAsm

/-!
# Handing a page to a function, proved safe

Takes a page from the kernel, reads standard input into it, calls a function
that doubles each of the page's 512 words, writes the page out, and gives it
back. It exits with status 0, or 1 if the kernel has no memory to give.

```asm
_start:
     mov   eax, 9                ; `mmap` one page
     xor   edi, edi
     mov   esi, 4096
     mov   edx, 3
     mov   r10d, 0x22
     mov   r8, -1
     xor   r9d, r9d
     syscall
     test  rax, rax
     js    fail
     mov   rbx, rax              ; the page: ours
     xor   eax, eax              ; `read` into it, up to all of it
     xor   edi, edi
     mov   rsi, rbx
     mov   edx, 4096
     syscall
     mov   rdi, rbx
     call  double                ; the page is the function's until it returns
back:
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
fail:
     mov   edi, 1
     mov   eax, 231
     syscall
double:                          ; doubles each word of the page at `rdi`
     xor   ecx, ecx
loop:
     cmp   rcx, 512
     jae   done
     mov   rax, [rdi + rcx*8]
     add   rax, rax
     mov   [rdi + rcx*8], rax
     add   rcx, 1
     jmp   loop
done:
     ret
```

The page belongs to the program, and for the length of the call to the
function: its signature says it takes the page at the address in `rdi` and
gives the same page back. While the function runs the caller does not own
the page, and could not touch it; when the function returns it must still
own the page to hand it back, so it could not have given it to the kernel.

The function reaches the words through an index that is known only to be
less than 512, which the test at the top of the loop establishes. The kernel
reads into the page directly, since the program owns it and all of it is
numbers.

`lake exe double` runs it in the model on standard input;
`lake exe double --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Double

/-! ## The program -/

inductive Label
  | start | back | fail | double | loop | done
  deriving DecidableEq, Hashable

def code : List (Asm Label) := [
  .label .start,
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
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rbx)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 4096)),
  .ins .syscall,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)),
  .call .double,
  .label .back,
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
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .label .double,
  .ins (.alu .xor .w32 (.rm_r (.reg .rcx) .rcx)),
  .label .loop,
  .ins (.alu .cmp .w64 (.rm_i (.reg .rcx) 512)),
  .jcc .ae .done,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) (some (.rcx, .s8)) 0))),
  .ins (.alu .add .w64 (.rm_r (.reg .rax) .rax)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdi) (some (.rcx, .s8)) 0)) .rax)),
  .ins (.alu .add .w64 (.rm_i (.reg .rcx) 1)),
  .jmp .loop,
  .label .done,
  .ins .ret]

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it one
-- free stack slot, for the return address of the one call.
asm_program code start .start stack 1

/-- A page for each request for memory, one after another. -/
def pages : Nat → Option (BitVec 64) :=
  fun i => some (BitVec.ofNat 64 (0x10000000 + 4096 * i))

/-- The starting state with the given input waiting and the given answers to
requests for memory. -/
def startWith (input : List Byte) (place : Nat → Option (BitVec 64) := pages) : State :=
  { start with world := { input := [.bytes input], place := place } }

/-! ## Running it -/

/-- A page of bytes that begins with the given ones and is zero after. -/
def page (bytes : List Byte) : List Byte :=
  bytes ++ List.replicate (4096 - bytes.length) 0

def exitedWith (out : List Byte) (code : BitVec 32) (r : State × Outcome) : Bool :=
  r.1.world.output == out && exitsWith code r.2

-- With no memory to be had it exits with status 1, having written nothing.
#guard exitedWith [] 1 (runMemFinal linux 10000 start)

-- Each word comes back doubled: bytes 1, 2, 3 become 2, 4, 6, and a byte of
-- 0x80 carries into the next.
#guard exitedWith (page [2, 4, 6, 0, 0, 0, 0, 0, 0, 1]) 0
  (runMemFinal linux 10000 (startWith [1, 2, 3, 0, 0, 0, 0, 0, 0x80]))

-- With nothing to read it writes a page of zeros.
#guard exitedWith (page []) 0 (runMemFinal linux 10000 (startWith []))

-- By the end the page is inaccessible again.
#guard (runMemFinal linux 10000 (startWith [])).1.perm 0x10000000 == .none

end Double

/-- The program, with what running it takes. -/
def Double.program : Runnable where
  name := "double"
  elf := Asm.elf Double.base Double.code .start
  startArgs := Double.startArgs
  readsInput := true
