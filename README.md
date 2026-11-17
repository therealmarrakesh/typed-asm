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
- A model of the Linux calls a program needs (`read`, `write`, `openat`,
  `close`, `fstat`, `lseek`, `fsync`, `fdatasync`, `mmap`, `munmap`,
  `getpid`, `exit`, `exit_group`, `clock_gettime`, `getrandom`). Where the
  kernel has a choice the model has it too: a call may hand over fewer bytes
  than were asked for, or fail.
- An assembler with labels for code and data. A program can have any number
  of segments, in any order. Each segment is executable, read-only or
  writable, and can be aligned.
- A type system for that model, with its soundness proof: a typed program
  never gets stuck and never faults, on the machine that decodes its
  instructions from memory. A context says what each register holds, as a
  term; what memory the code holds alone, byte for byte, a region being as
  many bytes as a value says where that is what it is; and what is known
  of values: that one points into a block others may point into, of a shape
  or of a kind; that it points to text; that it is code wanting a family of
  contexts, which is what a function is; that it lies in a range, or below
  another value; that it is the address of a row of as many values as a
  value says.
- A checker for the type system: a function, proved sound, that Lean's
  kernel runs. Each instruction is a description, as data, of what it reads,
  writes and computes, and one rule types them all. The checker walks a
  program from each label to where control leaves, through branches and
  system calls, and at a label, a call or a return compares the context
  reached with the one wanted there. It reasons about numbers itself: sums
  are taken apart so that the same value written two ways is seen to be the
  same, and what is known of how large values are is decided by a small
  procedure for whole numbers. Whether bytes lie within a region, and
  whether two stretches of one are apart, are questions for the same
  procedure.
- Functions an author defines in Lean, as terms: a label may say that a
  function returns what such a function gives of its argument. Where the
  values are numbers, the kernel computes it. What the checker cannot see,
  the author gives as laws, each two terms that are the same value where
  some values lie in given ranges, and proves once, as any theorem is.
- One check for a whole program as written: that its labels' code is typed,
  and that the state the kernel loads it into starts as its entry asks. The
  program says what blocks its segments are (a record, a table of pointers,
  the nodes of a list, a line of text) and the check reads that off the
  program's own bytes. A program started with arguments is checked once for
  every list of arguments.
- Beyond safety, what a program ends with: a program can be proved to exit
  only with a status satisfying a stated condition. And what it writes:
  data that is never written can say the bytes it holds, and a program can
  be proved to offer the kernel, at every `write`, only bytes satisfying a
  stated condition. `examples/Hello` is proved to end with 0 and to write
  its message and nothing else, on standard output.
- Twenty-four example programs in `examples/`, each built into an executable
  whose theorems depend only on Lean's three standard axioms.
- Tests against real tools: 79,628 instructions against the GNU assembler,
  13,579 instruction sequences against a real processor, including which
  fault each bad access raises, and 46 whole-program runs compared with the
  same programs run as Linux executables. The memory each program starts
  with in the model is checked to be its executable file, byte for byte.
  What the checker answers is tested case by case: what it accepts, and,
  as theorems, what it refuses.

The example programs are written as Lean constructor terms. What an author
writes beyond the program is what the labels want that are jumped back to,
called or returned to, each said by what differs from nothing being known,
and two commands:

- `asm_program code start .l stack n` lays the program out and defines what
  it puts in memory and the state it starts in.
- `asm_checked code start .l stack n program pg labels ls` runs the check
  and states what it shows: the program is safe, whatever the outside world
  holds. With `exits q` after it, also that the program ends only with a
  status `q` holds of. `asm_checked_args` is the same for a program started
  with arguments: safe whatever its arguments.

No proof is written for twenty-three of the twenty-four. In
`examples/Fact`, the recursive factorial, two laws of the factorial are
proved, in a dozen lines; with them its function is typed once for every
argument: that it needs sixteen bytes of stack for each unit of its
argument, and that it returns the factorial. The program is then proved to
end with 120. A function is typed once, for every caller its label allows:
`examples/Sum` and `examples/Index` take any row of values of any length;
`examples/Fresh` has a function that hands its caller a page of memory,
`examples/Double` one that takes a page and gives it back;
`examples/Dispatch` calls through a table of pointers to functions.

What is not there:

- A program is refused with the place its check stops and a short reason
  (`explain`), not yet with an account in the program's own terms of what
  the instruction would need.
- What a program writes is followed only for bytes the program's data says
  it holds, not for bytes the program made or read.
- The examples are written as constructor terms; there is no notation for
  instructions or labels.
