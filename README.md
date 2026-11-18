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
  program's own bytes. Every program is started as Linux starts it, with its
  arguments on its stack, and is checked once for every list of arguments.
- Beyond safety, what a program ends with: a program can be proved to exit
  only with a status satisfying a stated condition. And what it writes:
  data that is never written can say the bytes it holds, a number the
  program stored in memory it holds is its eight bytes, and a program can
  be proved to offer the kernel, at every `write`, only bytes satisfying a
  stated condition. `examples/Hello` is proved to end with 0 and to write
  its message and nothing else, on standard output.
- Twenty-five example programs in `examples/`, each built into an executable
  whose theorems depend only on Lean's three standard axioms.
- Tests against real tools: 79,628 instructions against the GNU assembler,
  13,579 instruction sequences against a real processor, including which
  fault each bad access raises, and 49 whole-program runs compared with the
  same programs run as Linux executables. The memory each program starts
  with in the model is checked to be its executable file, byte for byte.
  What the checker answers is tested case by case: what it accepts, and,
  as theorems, what it refuses.

The example programs are written as Lean constructor terms. What an author
writes beyond the program is what the labels want that are jumped back to,
called or returned to, each said by what differs from nothing being known,
and two commands:

- `asm_program code start .l stack n` lays the program out and defines what
  it puts in memory and the state it starts in, given its arguments: as
  Linux starts it, how many arguments there are at the stack pointer, their
  addresses after that, and the stack it asks for below.
- `asm_checked code start .l stack n program pg labels ls` runs the check
  and states what it shows: the program is safe, whatever its arguments and
  whatever the outside world holds. With `exits q` after it, also that the
  program ends only with a status `q` holds of.

A label is said one way, in the program's own code (`inProgram`) or in a
function (`inFunction`): what the registers hold, what is known, and what
has been put on the stack since the program started or the function was
entered, one thing after another: a value, a register the function keeps
for its caller, or so many bytes. `examples/Lengths` keeps a total on its
stack across calls to a function that saves a register and loops.

No proof is written for twenty-four of the twenty-five. In
`examples/Fact`, the recursive factorial, two laws of the factorial are
proved, in a dozen lines; with them its function is typed once for every
argument: that it needs sixteen bytes of stack for each unit of its
argument, and that it returns the factorial. The program is then proved to
end with 120. A function is typed once, for every caller its label allows:
`examples/Sum` and `examples/Index` take any row of values of any length;
`examples/Fresh` has a function that hands its caller a page of memory,
`examples/Double` one that takes a page and gives it back;
`examples/Dispatch` calls through a table of pointers to functions.

A program that is refused is told why by the command that checks it, in
the program's terms: which instruction, by its number and as it is written;
what it reads or writes, and where; what the machine could do there if the
program ran; what a register holds and which earlier instruction left it
so; where a label or a return is reached in a context it does not allow,
each thing wanted that is not so; and where a loop has no label, that, and
where the loop starts. The code a call returns to is looked into in the
same way. It is worked out from the parts the check is made of, and nothing
rests on it. How far the check goes is worked out from the program: there
is no number of steps for an author to give.

What is not there:

- What a program writes is followed for bytes its data says it holds and
  for bytes it made, not for bytes it read. A store of two or four bytes
  into a number it made leaves that number unknown; a store of one or of
  eight does not.
- There are no signals in the model. An exit status is the value handed to
  `exit`; a parent process sees its low eight bits.
- The examples are written as constructor terms; there is no notation for
  instructions or labels.
