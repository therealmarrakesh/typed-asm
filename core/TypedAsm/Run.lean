import TypedAsm.Machine
import TypedAsm.Linux
import TypedAsm.Elf

/-!
# Running a program in the model

What the example programs share: running on the machine with code in
memory, reporting how the run ended and what it wrote, and the command line
of their executables.
-/

namespace TypedAsm

/-- Like `runMem`, but also returns the last state reached. That state holds
what the program wrote, which an `exit` outcome does not carry. -/
def runMemFinal (sys : Syscall) : Nat → State → State × Outcome
  | 0, s => (s, .next s)
  | n + 1, s =>
    match stepMem sys s with
    | .next s' => runMemFinal sys n s'
    | o => (s, o)

/-- The bytes of a string. -/
def bytesOf (s : String) : List Byte :=
  s.toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat

def describe : Outcome → String
  | .next s => s!"still running at rip = {s.rip.toNat}"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

def exitsWith (code : BitVec 32) : Outcome → Bool
  | .exit c => c == code
  | _ => false

/-- Whether a run wrote exactly `out` and then exited with `code`. -/
def wroteAndExited (out : String) (code : BitVec 32) (r : State × Outcome) : Bool :=
  r.1.world.output == bytesOf out && exitsWith code r.2

/-- Where the model puts the memory of each request when a program is run
from the command line: 256 MiB apart, well away from the program and its
stack. A request for more than that runs into the next and is refused. -/
def defaultPlace : Nat → Option (BitVec 64) :=
  fun i => some (BitVec.ofNat 64 (0x100000000000 + 0x10000000 * i))

/-- A file with the given name and contents. -/
def fileOf (path : String) (bytes : List Byte) : File :=
  { path := bytesOf path, base := bytes.toArray }

/-- The files named after each `--file` on a command line, up to `--`. -/
private def fileArgs : List String → List String
  | "--" :: _ => []
  | "--file" :: path :: rest => path :: fileArgs rest
  | _ :: rest => fileArgs rest
  | [] => []

/-- What follows `--` on a command line: the arguments for the program. -/
private def programArgs : List String → List String
  | "--" :: rest => rest
  | _ :: rest => programArgs rest
  | [] => []

private partial def readAll (h : IO.FS.Stream) (acc : ByteArray) : IO ByteArray := do
  let chunk ← h.read 4096
  if chunk.isEmpty then return acc else readAll h (acc ++ chunk)

/-- The command line of an example's executable.

With no arguments it runs the program in the model, with instructions
decoded from memory. What the program writes goes to standard output, how
the run ended goes to standard error, and the executable's own exit status
is the program's. If `readsInput`, standard input is read to its end first
and given to the program as its input.

What follows `--` is given to the program as its arguments, after its own
name, if the example says how to start it with arguments (`startArgs`).
Each `--file NAME` makes that file of this machine visible to the program
under exactly that name, and so does each argument that names a file here.
What the program writes to files stays in the
model: nothing on this machine is created or changed. The time the program
is told is this machine's, and the random bytes it is given are drawn afresh
on each run.

With `--elf FILE` it writes the program as a Linux executable. -/
def exeMain (entry : Nat) (image data : List Byte) (start : State) (args : List String)
    (writable : Bool := false) (readsInput : Bool := false) (fuel : Nat := 1000000000)
    (startArgs : Option (List (List Byte) → State) := none) (name : String := "program") :
    IO UInt32 := do
  match args with
  | ["--elf", path] =>
    let bytes := Elf.file entry image data (writable := writable)
    IO.FS.writeBinFile path (ByteArray.mk (bytes.map fun b => b.toNat.toUInt8).toArray)
    IO.println s!"wrote {bytes.length} bytes to {path}"
    return 0
  | _ =>
    let given := programArgs args
    let start := match startArgs with
      | some f => f ((name :: given).map bytesOf)
      | none => start
    let start ← if readsInput then do
        let input ← readAll (← IO.getStdin) ByteArray.empty
        let bytes := input.toList.map fun b => BitVec.ofNat 8 b.toNat
        pure { start with world := { start.world with input := [.bytes bytes] } }
      else pure start
    let mut files : Array File := #[]
    let named ← given.filterM fun (path : String) => do
      let file : System.FilePath := path
      return (← file.pathExists) && !(← file.isDir)
    for path in (fileArgs args ++ named).eraseDups do
      let bytes ← IO.FS.readBinFile path
      files := files.push (fileOf path (bytes.toList.map fun b => BitVec.ofNat 8 b.toNat))
    let seed ← IO.rand 0 (2 ^ 32)
    let now ← IO.monoNanosNow
    let start := { start with
      world := { start.world with
        place := defaultPlace
        files := files
        random := fun i => BitVec.ofNat 8 (((seed + i) * 2654435761) >>> 13)
        time := fun i =>
          let t := now + 1000 * i
          (BitVec.ofNat 64 (t / 1000000000), BitVec.ofNat 64 (t % 1000000000)) } }
    let (final, outcome) := runMemFinal linux fuel start
    let out ← IO.getStdout
    out.write (ByteArray.mk (final.world.output.map fun b => b.toNat.toUInt8).toArray)
    out.flush
    IO.eprintln (describe outcome)
    match outcome with
    | .exit code => return code.toNat.toUInt32
    | _ => return 255

end TypedAsm
