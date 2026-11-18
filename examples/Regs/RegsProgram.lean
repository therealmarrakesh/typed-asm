import TypedAsm

/-!
# What a system call leaves alone, looked at by the program itself

The model of the kernel says that a call that returns changes three
registers and no other: `rax` holds what the call answers, `rcx` the
address of the instruction after it, and `r11` whatever the processor saved
there. This program holds the kernel to that. Before each call it puts a
number of its own in every register the call does not take; after it, it
compares each register with what it put there, and `rcx` with the address
of the next instruction; and it ends with status nought only if every
comparison came out equal, after every call the model has that returns.

So the same program is two things. Checked, it is proved to end only with
nought: on the model, nothing else can happen. Run as a Linux executable,
it ends with nought only if the kernel really leaves those registers alone.
The recorded runs compare the two.

Each call is made so that it returns at once whatever is outside: on a
descriptor that is not open, for no bytes, or of a clock.

`lake exe regs` runs it in the model; `lake exe regs --elf FILE` writes an
executable that Linux can run.
-/

open TypedAsm

namespace Regs

/-- Labels: the start, where a comparison that fails goes, the instruction
after each call, the path a call is given, and where the pages are done
with. -/
inductive Label
  | start | fail | after (k : Nat) | path | noPage | done
  deriving DecidableEq, Hashable

/-- What a register is given before a call: a number, the address of the
buffer on the stack, or the address of the path. -/
inductive Arg
  | num (n : BitVec 32)
  | buf
  | path
  deriving DecidableEq, Hashable

/-- The registers looked at, each with the number it holds where a call
does not take it. -/
def marks : List (Reg × BitVec 32) :=
  [(.rbx, 0x101), (.rdx, 0x102), (.rsi, 0x103), (.rdi, 0x104), (.rbp, 0x105), (.r8, 0x106),
   (.r9, 0x107), (.r10, 0x108), (.r12, 0x109), (.r13, 0x10a), (.r14, 0x10b), (.r15, 0x10c)]

/-- What each register is given before a call that takes `args`. -/
def given (args : List (Reg × Arg)) : List (Reg × Arg) :=
  marks.map fun m => (m.1, (args.lookup m.1).getD (.num m.2))

/-- A register given something. -/
def put : Reg × Arg → Asm Label
  | (r, .num n) => .ins (.mov .w64 (.rm_i (.reg r) n))
  | (r, .buf) => .ins (.lea .w64 r (.sib (some .rsp) none 0))
  | (r, .path) => .ref (.lea .w64 r (.rip 0)) .path

/-- A register compared with what it was given: `r11`, which the call has
written over, is used for what is not a number written out. To `fail`
where they differ. -/
def look : Reg × Arg → List (Asm Label)
  | (r, .num n) => [.ins (.alu .cmp .w64 (.rm_i (.reg r) n)), .jcc .ne .fail]
  | (r, .buf) =>
    [.ins (.lea .w64 .r11 (.sib (some .rsp) none 0)),
     .ins (.alu .cmp .w64 (.rm_r (.reg r) .r11)), .jcc .ne .fail]
  | (r, .path) =>
    [.ref (.lea .w64 .r11 (.rip 0)) .path,
     .ins (.alu .cmp .w64 (.rm_r (.reg r) .r11)), .jcc .ne .fail]

/-- After the `k`th call: each register against what it was given, and
`rcx` against the address of the instruction after the call. -/
def looks (k : Nat) (regs : List (Reg × Arg)) : List (Asm Label) :=
  regs.flatMap look ++
    [.ref (.lea .w64 .r11 (.rip 0)) (.after k),
     .ins (.alu .cmp .w64 (.rm_r (.reg .rcx) .r11)), .jcc .ne .fail]

/-- The `k`th call, number `nr`, taking `args`: every register given
something, the call, and every register looked at. -/
def probe (k : Nat) (nr : BitVec 32) (args : List (Reg × Arg)) : List (Asm Label) :=
  (given args).map put ++
    [.ins (.mov .w32 (.rm_i (.reg .rax) nr)), .ins .syscall, .label (.after k)] ++
    looks k (given args)

def code : List (Asm Label) :=
  [.label .start,
   .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 160))] ++
  probe 0 39 [] ++                                                    -- getpid
  probe 1 1 [(.rdi, .num 1), (.rsi, .buf), (.rdx, .num 0)] ++         -- write, of no bytes
  probe 2 3 [(.rdi, .num 99)] ++                                      -- close
  probe 3 8 [(.rdi, .num 99), (.rsi, .num 0), (.rdx, .num 0)] ++      -- lseek
  probe 4 257 [(.rdi, .num (-100)), (.rsi, .path), (.rdx, .num 0), (.r10, .num 0)] ++  -- openat
  probe 5 74 [(.rdi, .num 99)] ++                                     -- fsync
  probe 6 75 [(.rdi, .num 99)] ++                                     -- fdatasync
  probe 7 0 [(.rdi, .num 99), (.rsi, .buf), (.rdx, .num 8)] ++        -- read
  probe 8 5 [(.rdi, .num 99), (.rsi, .buf)] ++                        -- fstat
  probe 9 228 [(.rdi, .num 1), (.rsi, .buf)] ++                       -- clock_gettime
  probe 10 318 [(.rdi, .buf), (.rsi, .num 8), (.rdx, .num 0)] ++      -- getrandom
  probe 11 9 [(.rdi, .num 0), (.rsi, .num 4096), (.rdx, .num 3), (.r10, .num 0x22),
    (.r8, .num (-1)), (.r9, .num 0)] ++                               -- mmap
  [.ins (.test .w64 (.reg .rax) (.reg .rax)),
   .jcc .s .noPage,
   .ins (.mov .w64 (.rm_r (.reg .rbx) .rax))] ++
  -- munmap, of the page just given: `rdi` and `rbx` hold its address
  ((given [(.rsi, .num 4096)]).filter fun g => g.1 != .rbx && g.1 != .rdi).map put ++
  [.ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)),
   .ins (.mov .w32 (.rm_i (.reg .rax) 11)), .ins .syscall, .label (.after 12),
   .ins (.alu .cmp .w64 (.rm_r (.reg .rdi) .rbx)), .jcc .ne .fail] ++
  looks 12 ((given [(.rsi, .num 4096)]).filter fun g => g.1 != .rbx && g.1 != .rdi) ++
  [.label .noPage,
   .label .done,
   .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
   .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
   .ins .syscall,
   .label .fail,
   .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
   .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
   .ins .syscall,
   .segment .ro,
   .label .path, .bytes (bytesOf "/nowhere/at/all" ++ [0])]

-- Where the program is loaded, what it puts in memory, where it starts and
-- the state it starts in, all from the lines above.
asm_program code start .start stack 20 named "regs"

/-! ## Running it -/

-- On the model every comparison comes out equal.
#guard exitsWith 0 (runMem linux 10000 start)

end Regs
