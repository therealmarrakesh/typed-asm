# TypedAsm

TypedAsm is a typed x86-64 macro-assembler embedded in Lean 4. It defines an
instruction set, machine semantics (including a model of Linux system calls),
and typing rules for registers, the stack, and memory. Authors write assembly
as Lean terms, generate instruction sequences with Lean functions and macros,
and state and prove properties of those programs in Lean.

## Status

What exists and is checked today:

- A model of an x86-64 subset: 79 instructions, in thirty forms, with an
  encoder and a decoder proved to round-trip.
- A type system for that model, with its soundness proof. A typed program
  never gets stuck and never faults, on the machine that decodes its
  instructions from memory.
- Memory and the stack are typed to the byte. Stack space can be lent to a
  called function, and arrays can be indexed by any value within bounds,
  through a pointer or at a fixed address.
- Beyond safety, what a program ends with: a program can be proved to exit
  only with a status satisfying a stated condition. `examples/Fact` is proved
  to end with 120, the factorial of five, through its recursion.
- An assembler with labels for code and data. A program can have any number
  of segments, in any order. Each segment is executable, read-only or
  writable, and can be aligned.
- A model of the Linux calls a program needs (`read`, `write`, `openat`,
  `close`, `fstat`, `lseek`, `fsync`, `fdatasync`, `mmap`, `munmap`, `getpid`,
  `exit`, `exit_group`, `clock_gettime`, `getrandom`). Where the kernel has a choice the model has
  it too: a call may hand over fewer bytes than were asked for, or fail, and
  what a program may conclude from a result is stated and proved.
- Twenty-three example programs in `examples/`, each built into an executable
  whose safety theorem depends only on Lean's three standard axioms.
- Tests against real tools: 79,628 instructions against the GNU assembler,
  13,579 instruction sequences against a real processor, including which
  fault each bad access raises, and 45 whole-program runs compared with the
  same programs run as Linux executables. The memory each program starts
  with in the model is checked to be its executable file, byte for byte.

The example programs are written as Lean constructor terms. What an author
writes beyond the program is the context that holds at each label that is
jumped back to, called or returned to, and three commands:

- `asm_program code start .l` lays the program out and defines what it puts
  in memory and the state it starts in.
- `asm_typing At` takes those contexts and works out the rest of the typing:
  the program's blocks of memory from its labelled data, the stack it needs
  and whether it takes arguments from the entry label's context, and the
  contract with whatever loads it.
- `asm_safety At.start` proves the program well typed and, from that, safe
  from every state meeting the contract, whatever the outside world does.
  With `exits Q` after it, it also proves that the program ends only with a
  status satisfying `Q`.

Each instruction is typed without being told how. Seventeen of the twenty-three
examples need nothing more than this. In the others, a label's block says
what cannot be read off the program: where an owned block is split, joined
or made part of the shared memory, which piece of the stack is lent to a
function, what a register holding a label's address is a pointer to, or a
fact about what the program computes.

A program that is not typed is told why in terms of the program: which
instruction, what it would need, what could go wrong on the machine if it
ran, and which earlier instruction gave a register or the flags what they
hold.
