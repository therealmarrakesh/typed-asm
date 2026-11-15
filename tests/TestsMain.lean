import Tests

/-!
# The test program

Checks the model against results recorded from real tools:

* the encoder against the GNU assembler, and the decoder against the encoder
* the instruction semantics against a real processor
* whole programs against the same programs run as Linux executables

It needs nothing but Lean: the recorded results are in `tests/data`. Run it
with `lake test`. To regenerate the recorded results, see `Capture.lean`.
-/

open TypedAsm

def readLines (path : System.FilePath) : IO (Array String) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").toArray.filter (· ≠ "")

/-- Reports up to a few failures and returns whether there were none. -/
def report (name : String) (total : Nat) (failures : Array String) : IO Bool := do
  if failures.isEmpty then
    IO.println s!"{name}: {total} cases, all pass"
    return true
  IO.println s!"{name}: {failures.size} of {total} cases FAIL"
  for f in failures.toList.take 10 do
    IO.println s!"  {f}"
  return false

def checkEncoding : IO Bool := do
  let expected ← readLines "tests/data/encoding.txt"
  let instrs := Tests.Encoding.instrs.toArray
  if expected.size ≠ instrs.size then
    IO.println s!"encoding: the data file has {expected.size} lines but there are \
      {instrs.size} instructions; regenerate it"
    return false
  let mut failures : Array String := #[]
  for h : n in [0:instrs.size] do
    let i := instrs[n]
    let bytes := i.encode
    let ours := Tests.Encoding.hex bytes
    if ours ≠ expected[n]! then
      failures := failures.push s!"{i.toAsm}: encoded as {ours}, the assembler gives {expected[n]!}"
    else if decode bytes ≠ some (i, bytes.length) then
      failures := failures.push s!"{i.toAsm}: {ours} does not decode back"
  report "encoding" instrs.size failures

def checkHardware : IO Bool := do
  let expected ← readLines "tests/data/hardware.txt"
  let cases := Tests.Hardware.cases.toArray
  if expected.size ≠ cases.size then
    IO.println s!"hardware: the data file has {expected.size} lines but there are \
      {cases.size} cases; regenerate it"
    return false
  let mut failures : Array String := #[]
  for (c, real) in cases.zip expected do
    let model := Tests.Hardware.modelLine c.1 c.2
    unless Tests.Hardware.agrees model real do
      let text := "; ".intercalate (c.1.map Instr.toAsm)
      failures := failures.push s!"{text}: model `{model}`, processor `{real}`"
  report "hardware" cases.size failures

def checkPrograms : IO Bool := do
  let expected ← readLines "tests/data/programs.txt"
  let cases := Tests.Programs.cases.toArray
  if expected.size ≠ cases.size then
    IO.println s!"programs: the data file has {expected.size} lines but there are \
      {cases.size} cases; regenerate it"
    return false
  let mut failures : Array String := #[]
  for (c, real) in cases.zip expected do
    let model := Tests.Programs.modelLine c
    unless model == real do
      failures := failures.push s!"{c.label}: the model gives {model.take 80}, \
        the machine {real.take 80}"
  report "programs" cases.size failures

def main : IO UInt32 := do
  let a ← checkEncoding
  let b ← checkHardware
  let c ← checkPrograms
  return if a && b && c then 0 else 1
