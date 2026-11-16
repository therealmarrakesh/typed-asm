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
  called function, and arrays can be indexed by any value within bounds.
- An assembler with labels for code and data. A program can have any number
  of segments, in any order. Each segment is executable, read-only or
  writable, and can be aligned.
- A model of the Linux calls a program needs (`read`, `write`, `openat`,
  `close`, `fstat`, `lseek`, `mmap`, `munmap`, `exit`, `exit_group`,
  `clock_gettime`, `getrandom`).
- Twenty-one example programs in `examples/`, each built into an executable
  whose safety theorem depends only on Lean's three standard axioms.
- Tests against real tools: 79,628 instructions against the GNU assembler,
  13,579 instruction sequences against a real processor, including which
  fault each bad access raises, and 42 whole-program runs compared with the
  same programs run as Linux executables. The memory each program starts
  with in the model is checked to be its executable file, byte for byte.

The example programs are written as Lean constructor terms, and their typing
is done by tactics.
