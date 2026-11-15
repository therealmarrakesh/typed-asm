import Tests

/-!
# Regenerating the recorded results

`lake exe capture` rewrites the files in `tests/data` from real tools. It is
needed only when the lists of test cases change, and unlike the tests it
needs a particular machine: x86-64 Linux, with the GNU assembler (`as`,
`objcopy`, `nm`) and a C compiler (`cc`).

* `lake exe capture encoding` assembles every instruction with `as`.
* `lake exe capture hardware` runs every snippet on this processor.
* `lake exe capture programs` runs every whole program as a Linux executable.
* `lake exe capture` does all three.
-/

open TypedAsm

def workDir : System.FilePath := "tests/capture/build"

def sh (command : String) : IO Unit := do
  let out ← IO.Process.output { cmd := "sh", args := #["-c", command] }
  if out.exitCode ≠ 0 then
    throw <| IO.userError s!"command failed: {command}\n{out.stderr}"

def captureEncoding : IO Unit := do
  let instrs := Tests.Encoding.instrs.toArray
  let mut source := ".intel_syntax noprefix\n.text\n"
  for h : n in [0:instrs.size] do
    source := source ++ s!"L{n}: {Tests.Encoding.asmText instrs[n]}\n"
  source := source ++ s!"L{instrs.size}:\n"
  IO.FS.writeFile (workDir / "t.s") source
  sh s!"cd {workDir} && as -o t.o t.s && objcopy -O binary --only-section=.text t.o t.bin \
    && nm t.o > t.nm"
  let blob ← IO.FS.readBinFile (workDir / "t.bin")
  -- the address of each label
  let mut addr : Array Nat := Array.replicate (instrs.size + 1) 0
  for line in (← IO.FS.readFile (workDir / "t.nm")).splitOn "\n" do
    match line.splitOn " " with
    | [a, _, name] =>
      if name.startsWith "L" then
        if let some n := (name.drop 1).toNat? then
          if n ≤ instrs.size then
            addr := addr.set! n (a.foldl (fun acc c =>
              acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0)
    | _ => pure ()
  let mut out := ""
  for n in [0:instrs.size] do
    let bytes := (blob.extract addr[n]! addr[n + 1]!).toList.map fun b => BitVec.ofNat 8 b.toNat
    out := out ++ Tests.Encoding.hex bytes ++ "\n"
  IO.FS.writeFile "tests/data/encoding.txt" out
  IO.println s!"wrote tests/data/encoding.txt ({instrs.size} instructions)"

def captureHardware : IO Unit := do
  let cases := Tests.Hardware.cases
  let input := String.join (cases.map fun (sn, inp) => Tests.Hardware.caseLine sn inp ++ "\n")
  IO.FS.writeFile (workDir / "cases.txt") input
  sh s!"cc -O1 -o {workDir}/runner tests/capture/runner.c \
    && {workDir}/runner < {workDir}/cases.txt > tests/data/hardware.txt"
  IO.println s!"wrote tests/data/hardware.txt ({cases.length} cases)"

/-- A word as the shell takes it, whatever is in it. -/
def quoted (s : String) : String :=
  "'" ++ s.replace "'" "'\\''" ++ "'"

def bytesFile (path : System.FilePath) (bytes : List Byte) : IO Unit :=
  IO.FS.writeBinFile path (ByteArray.mk (bytes.map fun b => b.toNat.toUInt8).toArray)

/-- Each case in a directory of its own, holding the executable, the files
the case has and nothing else. The program is run there under its own name,
with the case's arguments and standard input. -/
def capturePrograms : IO Unit := do
  let cases := Tests.Programs.cases
  let root := workDir / "programs"
  if ← root.pathExists then IO.FS.removeDirAll root
  let mut out := ""
  for c in cases do
    let dir := root / c.label
    IO.FS.createDirAll dir
    let exe := c.program.name
    bytesFile (dir / exe) c.program.elf
    for (name, bytes) in c.files do
      bytesFile (dir / name) bytes
    -- standard input and what is recorded stay outside the directory
    bytesFile (root / "stdin") c.input
    let args := " ".intercalate (c.args.map quoted)
    sh s!"chmod +x {dir}/{exe} && cd {dir} && \
      (./{exe} {args} < ../stdin > ../stdout; echo $? > ../status)"
    let status := (← IO.FS.readFile (root / "status")).trimAscii.toString.toNat!
    let written := (← IO.FS.readBinFile (root / "stdout")).toList.map fun b =>
      BitVec.ofNat 8 b.toNat
    out := out ++ Tests.Programs.line status written ++ "\n"
  IO.FS.writeFile "tests/data/programs.txt" out
  IO.println s!"wrote tests/data/programs.txt ({cases.length} cases)"

def main (args : List String) : IO Unit := do
  IO.FS.createDirAll workDir
  match args with
  | ["encoding"] => captureEncoding
  | ["hardware"] => captureHardware
  | ["programs"] => capturePrograms
  | [] => captureEncoding; captureHardware; capturePrograms
  | _ => IO.println "usage: lake exe capture [encoding|hardware|programs]"
