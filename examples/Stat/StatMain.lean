import StatProgram

/-- With no arguments, runs the program on the machine with code in memory;
`--file input.txt` gives it that file. With `--elf FILE`, writes the program
as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  Stat.program.main args
