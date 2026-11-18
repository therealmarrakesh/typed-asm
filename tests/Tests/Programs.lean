import Tests.Encoding
import SumProgram
import SwapProgram
import FrameProgram
import OpsProgram
import IndexProgram
import EchoProgram
import TableProgram
import DispatchProgram
import ListProgram
import FactProgram
import BufferProgram
import KeepProgram
import AllocProgram
import CatProgram
import StatProgram
import ArgsProgram
import OwnProgram
import DoubleProgram
import FreshProgram
import PairProgram
import LendProgram
import PickProgram
import LengthsProgram
import RegsProgram
import HelloProgram

/-!
# Whole programs, against a real machine

Each case is one of the example programs with arguments, something on
standard input and some files. The model's run is compared with what the
same program did as a Linux executable on a real processor: the bytes it
wrote to standard output and its exit status.
-/

open TypedAsm

namespace Tests.Programs

/-- One run of a program. -/
structure Case where
  /-- What the case is called in reports, and its directory when captured. -/
  label : String
  program : Runnable
  /-- The arguments after the program's own name. -/
  args : List String := []
  /-- What there is to read on standard input. -/
  input : List Byte := []
  /-- The files there are, by name. -/
  files : List (String × List Byte) := []

/-- Bytes of every value, in no simple order. -/
def pattern (n : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (i * 7 + i / 251)

def cases : List Case := [
  { label := "sum", program := Sum.program },
  { label := "swap", program := Swap.program },
  { label := "frame", program := Frame.program },
  { label := "ops", program := Ops.program },
  { label := "index", program := Index.program },
  { label := "table", program := Table.program },
  { label := "dispatch", program := Dispatch.program },
  { label := "list", program := List3.program },
  { label := "fact", program := Fact.program },
  { label := "own", program := Own.program },
  { label := "lend", program := Lend.program },
  { label := "echo-empty", program := Echo.program },
  { label := "echo-line", program := Echo.program, input := bytesOf "hello, world\n" },
  { label := "echo-bytes", program := Echo.program, input := pattern 5000 },
  { label := "buffer-empty", program := Buffer.program },
  { label := "buffer-exact", program := Buffer.program, input := bytesOf "0123456789abcdef" },
  { label := "buffer-bytes", program := Buffer.program, input := pattern 1000 },
  { label := "keep-empty", program := Keep.program },
  { label := "keep-short", program := Keep.program, input := bytesOf "abc" },
  { label := "keep-long", program := Keep.program, input := pattern 100 },
  { label := "alloc-empty", program := Alloc.program },
  { label := "alloc-one", program := Alloc.program, input := bytesOf "one piece\n" },
  { label := "alloc-many", program := Alloc.program, input := pattern 1000 },
  { label := "cat-none", program := Cat.program },
  { label := "cat-one", program := Cat.program, args := ["a.txt"],
    files := [("a.txt", bytesOf "first file\n")] },
  { label := "cat-three", program := Cat.program, args := ["a.txt", "b.bin", "a.txt"],
    files := [("a.txt", bytesOf "first file\n"), ("b.bin", pattern 700)] },
  { label := "cat-missing", program := Cat.program, args := ["a.txt", "missing", "b.bin"],
    files := [("a.txt", bytesOf "first file\n"), ("b.bin", pattern 700)] },
  { label := "cat-empty-file", program := Cat.program, args := ["empty"],
    files := [("empty", [])] },
  { label := "stat-short", program := Stat.program,
    files := [("input.txt", bytesOf "thirty-seven bytes of text, counted.\n")] },
  { label := "stat-long", program := Stat.program, files := [("input.txt", pattern 300)] },
  { label := "stat-missing", program := Stat.program },
  { label := "args-none", program := Args.program },
  { label := "args-one", program := Args.program, args := ["one"] },
  { label := "args-several", program := Args.program,
    args := ["one", "two words", "", "héllo", "--flag=3"] },
  { label := "double-empty", program := Double.program },
  { label := "double-short", program := Double.program, input := pattern 100 },
  { label := "double-page", program := Double.program, input := pattern 4096 },
  { label := "double-more", program := Double.program, input := pattern 5000 },
  -- at least eight bytes of input: with fewer, what the program writes shows
  -- where the kernel put its page, which no two runs agree on
  { label := "fresh-short", program := Fresh.program, input := pattern 100 },
  { label := "fresh-page", program := Fresh.program, input := pattern 4096 },
  { label := "fresh-more", program := Fresh.program, input := pattern 5000 },
  { label := "pair", program := Pair.program },
  { label := "pick-none", program := Pick.program },
  { label := "pick-two", program := Pick.program, args := ["a", "b"] },
  { label := "pick-many", program := Pick.program, args := ["a", "b", "c", "d"] },
  { label := "lengths-none", program := Lengths.program },
  { label := "lengths-one", program := Lengths.program, args := ["hello"] },
  { label := "lengths-several", program := Lengths.program,
    args := ["one", "two words", "", "héllo", "--flag=3"] },
  { label := "regs", program := Regs.program },
  { label := "hello", program := Hello.program }]

/-- A run as it is recorded: the exit status as Linux reports it, then what
was written to standard output. -/
def line (status : Nat) (output : List Byte) : String :=
  s!"{status} {Tests.Encoding.hex output}"

/-- What the model does with a case, as a recorded line; or how the run
ended, if not by exiting. -/
def modelLine (c : Case) : String :=
  let files := c.files.toArray.map fun (name, bytes) => fileOf name bytes
  let (final, outcome) := c.program.run c.args c.input files
  match outcome with
  | .exit code => line (code.toNat % 256) final.world.output
  | o => describe o

end Tests.Programs
