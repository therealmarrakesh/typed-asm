import LengthsProgram

/-- `lake exe lengths -- ARG...` runs the program on the machine with code in
memory. With `--elf FILE`, writes the program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  Lengths.program.main args
