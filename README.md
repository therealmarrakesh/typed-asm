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
- A checker for the type system: a function, proved sound against the
  typing rules, that works out the context after each instruction. It works
  on contexts written as data, and finds for itself where an operand is: the
  block a pointer points into, the owned block an address is in, the element
  of an array, the piece of the stack, a block of the program. What it
  cannot settle by looking, a bound on an index say, it returns to be
  shown. A run of instructions is checked in one evaluation, through to
  where the block ends: a jump to a label or running into one, a direct
  call, a return, with system calls that return stepped over on the way.
  At a label, a call or a return the checker compares the context reached
  with the one wanted there. Where it refuses an instruction, the reason
  given is worked out from the same parts: there is no second, slower way
  of typing an instruction.
- Memory and the stack are typed to the byte. Stack space can be lent to a
  called function, and arrays can be indexed by any value within bounds,
  through a pointer or at a fixed address.
- Beyond safety, what a program ends with: a program can be proved to exit
  only with a status satisfying a stated condition. `examples/Fact` is proved
  to end with 120, the factorial of five, through its recursion.
- And what it writes: data that is never written can say the bytes it
  holds, the type system keeps that true, and a program can be proved to
  offer the kernel, at every `write`, only bytes satisfying a stated
  condition; and from that, that everything a whole run adds to the output
  is the first so many bytes of something satisfying it, the kernel being
  free to take fewer bytes than it is offered. `examples/Hello` is proved to
  end with 0 and to write its message and nothing else, on standard output.
  The bytes may also be ones the program made: a value it stored on its
  stack or in a block it owns, exactly known, is its eight bytes, least
  significant first, and a `write` from such fields offers those bytes; a
  byte the program then stores into such a field leaves it exactly known,
  with that byte replaced. What a program read and then writes back is not
  yet followed.
- An assembler with labels for code and data. A program can have any number
  of segments, in any order. Each segment is executable, read-only or
  writable, and can be aligned.
- A model of the Linux calls a program needs (`read`, `write`, `openat`,
  `close`, `fstat`, `lseek`, `fsync`, `fdatasync`, `mmap`, `munmap`, `getpid`,
  `exit`, `exit_group`, `clock_gettime`, `getrandom`). Where the kernel has a choice the model has
  it too: a call may hand over fewer bytes than were asked for, or fail, and
  what a program may conclude from a result is stated and proved.
- Twenty-four example programs in `examples/`, each built into an executable
  whose safety theorem depends only on Lean's three standard axioms.
- Tests against real tools: 79,628 instructions against the GNU assembler,
  13,579 instruction sequences against a real processor, including which
  fault each bad access raises, and 45 whole-program runs compared with the
  same programs run as Linux executables. The memory each program starts
  with in the model is checked to be its executable file, byte for byte.
  What the checker answers is tested case by case, accepted and refused.

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
  status satisfying `Q`; with `writes R`, that every `write` it makes offers
  a descriptor and bytes satisfying `R`, and that every entry a run adds to
  the world's record of writes is the start of such bytes (`asm_typing At
  data` first makes the program's read-only data say its bytes). The two may
  be given together.

Each instruction is typed without being told how, and so is each way a
block ends: a jump, a call or a return, through a label or through a value,
a call that ends the program, memory asked of the kernel or given back.
Twenty of the twenty-four examples need nothing more than their contexts. In
the other four, a label's block says what cannot be read off the program:
where an owned block is split, joined or made part of the shared memory,
which piece of the stack is lent to a function, what kind a new block is to
be, or which of a family of signatures a recursive call is made at. A
fact about what the program computes is a theorem marked `@[asm_fact]`:
`examples/Fact` gives two, what the function returns for zero and what its
multiply computes, and the checker uses them where they are needed.

A program that is not typed is told why in terms of the program: which
instruction, what it would need, what could go wrong on the machine if it
ran, and which earlier instruction gave a register or the flags what they
hold.
