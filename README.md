# TypedAsm

An x86-64 assembler embedded in Lean 4, with a type system for instructions
and the machine state they act on. Programs and their types can be checked
and computed over directly.

## What this is

Programs are ordinary x86-64 assembly, written as Lean terms. Their types and
semantics are defined in Lean as well: a program is typed by a judgment
proved sound, and reasoned about against the same semantics that defines how
it runs.

## Status

What exists and is checked today:

- A model of an x86-64 subset: about thirty instruction forms, with an encoder
  and a decoder proved to round-trip.
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
  13,460 instruction sequences against a real processor, and 42 whole-program
  runs compared with the same programs run as Linux executables.

The example programs are written as Lean constructor terms, and their typing
is done by tactics.
