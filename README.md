# TypedAsm

An x86-64 assembler embedded in Lean 4, in which instructions, data, layouts
and the facts about them are all values that can be computed with and proved
things about.

## What this is

Instructions, data, layouts, contexts and signatures are all values of Lean
types, inside a language where values can be computed with and propositions
about them can be proved. Safety is the first thing proved about them. It is a
consequence of the embedding, not its definition.

What follows from that:

- **The macro language is Lean.** Any function that returns instructions is a
  macro, with the full language behind it: recursion, data structures, type
  classes.
- **Programs are data.** They can be generated, transformed, analysed,
  specialised and compared by ordinary functions, and those functions can
  themselves be proved correct.
- **Types are computed, not just checked.** A signature can depend on a
  number, a context on an address.
- **Any statable property is provable in principle.** Not only "never
  faults", but "these two routines are equivalent", "this uses at most `k`
  stack slots", "this returns the sum". The semantics to state all of those
  exists today.
- **The output carries its meaning.** The bytes in the executable are the
  image of a term, through an encoder proved to round-trip, so a statement
  about the term is a statement about the file.

One qualification. Safety has a general method, the type system. Other
properties so far have only the raw semantics to be proved against; there is
no program logic yet to make them convenient.

## Status

What exists and is checked today:

- A model of an x86-64 subset: about thirty instruction forms, with an encoder
  and a decoder proved to round-trip.
- A type system for that model, with its soundness proof. A typed program
  never gets stuck and never faults, on the machine that decodes its
  instructions from memory.
- A model of the Linux calls a program needs (`read`, `write`, `openat`,
  `close`, `fstat`, `lseek`, `mmap`, `munmap`, `exit`, `exit_group`,
  `clock_gettime`, `getrandom`).
- Twenty example programs in `examples/`, each built into an executable whose
  safety theorem depends only on Lean's three standard axioms.
- Tests against real tools: 79,628 instructions against the GNU assembler,
  13,460 instruction sequences against a real processor, and 41 whole-program
  runs compared with the same programs run as Linux executables.

There is no surface language. The example programs are written as Lean
constructor terms, and their typing is done by tactics.
