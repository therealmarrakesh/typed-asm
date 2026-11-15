import CatProgram

/-- `lake exe cat -- FILE...` runs the program on the machine with code in
memory, given those files of this machine. With `--elf FILE`, writes the
program as a Linux executable. -/
def main (args : List String) : IO UInt32 :=
  Cat.program.main args
