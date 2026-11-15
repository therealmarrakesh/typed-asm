import ArgsProgram

/-- `lake exe args -- ARG...` runs the program on the machine with code in
memory. With `--elf FILE`, writes the program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  Args.program.main args
