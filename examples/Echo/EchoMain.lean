import EchoProgram

/-- With no arguments, runs the program on the machine with code in memory,
copying this process's standard input to its standard output. With
`--elf FILE`, writes the program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  Echo.program.main args
