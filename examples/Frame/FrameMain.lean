import FrameProgram

/-- With no arguments, runs the program on the machine with code in memory:
what it writes goes to standard output, how it ended to standard error, and
its exit status becomes this executable's. With `--elf FILE`, writes the
program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  Frame.program.main args
