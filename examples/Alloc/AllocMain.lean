import AllocProgram

/-- With no arguments, runs the program on the machine with code in memory,
on this process's standard input. With `--elf FILE`, writes the program as a
Linux executable. -/
def main (args : List String) : IO UInt32 :=
  Alloc.program.main args
