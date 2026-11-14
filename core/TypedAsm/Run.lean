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

private partial def readAll (h : IO.FS.Stream) (acc : ByteArray) : IO ByteArray := do
  let chunk ← h.read 4096
  if chunk.isEmpty then return acc else readAll h (acc ++ chunk)

/-- The command line of an example's executable.

With no arguments it runs the program in the model, with instructions
decoded from memory. What the program writes goes to standard output, how
the run ended goes to standard error, and the executable's own exit status
is the program's. If `readsInput`, standard input is read to its end first
and given to the program as its input.

With `--elf FILE` it writes the program as a Linux executable. -/
def exeMain (entry : Nat) (image data : List Byte) (start : State) (args : List String)
    (writable : Bool := false) (readsInput : Bool := false) (fuel : Nat := 1000000000) :
    IO UInt32 := do
  match args with
  | ["--elf", path] =>
    let bytes := Elf.file entry image data (writable := writable)
    IO.FS.writeBinFile path (ByteArray.mk (bytes.map fun b => b.toNat.toUInt8).toArray)
    IO.println s!"wrote {bytes.length} bytes to {path}"
    return 0
  | _ =>
    let start ← if readsInput then do
        let input ← readAll (← IO.getStdin) ByteArray.empty
        let bytes := input.toList.map fun b => BitVec.ofNat 8 b.toNat
        pure { start with world := { start.world with input := [.bytes bytes] } }
      else pure start
    let (final, outcome) := runMemFinal linux fuel start
    let out ← IO.getStdout
    out.write (ByteArray.mk (final.world.output.map fun b => b.toNat.toUInt8).toArray)
    out.flush
    IO.eprintln (describe outcome)
    match outcome with
    | .exit code => return code.toNat.toUInt32
    | _ => return 255

end TypedAsm
