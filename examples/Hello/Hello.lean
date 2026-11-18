import HelloProgram
import TypedAsm.U.Say
import TypedAsm.Runs

/-!
# Hello: typing, safety, and what it writes

The program is in `HelloProgram.lean`. This file checks it and states what
the check shows: it is safe, it ends only with status nought, and what it
writes is its message. One check, run by Lean's kernel, decides that the
program's code is typed and that the state the kernel loads it into starts
as its entry asks. The page the message is on is never written, so its
block says its bytes; and the program is typed against a system that lets a
`write` through only if it offers exactly those bytes on descriptor 1.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Hello

/-! ## The check -/

/-- The page the message is on says its bytes: the message, then nought to
the end of the page. -/
def said : List (BitVec 64 × List (BitVec 8)) :=
  [(Asm.addr code base .message, message ++ List.replicate (4096 - 14) 0)]

/-- The program for the checker: its instructions, and what is asked at a
system call: to end with status nought, and at a `write` to offer the
message on descriptor 1. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preOut said (· == 0) (fun fd b => fd == 1 && b == message) }

/-- One label: where it starts, with nothing known of any register and no
stack. -/
def labels : List U.Label := [⟨entry, inProgram 0⟩]

/-- **The check.** -/
theorem checked : wholeOk code .start 0 pg labels 12 = true := by decide +kernel

theorem saidOk : saidCheck (denBlocks (blocksOf code .start)) said = true := by decide +kernel

/-! ## What it shows -/

/-- The state `HelloProgram` starts the program in with given arguments is
the one the check is of, in the world it has. -/
theorem start_eq (args : List (List Byte)) :
    startArgs args = startIn code .start 0 args (startArgs args).world := by
  unfold startArgs prepared startIn startState entry base
  rfl

/-- **Hello is safe on the machine that decodes its instructions from
memory; it ends only with status nought; and wherever it reaches a `write`,
the descriptor is 1 and the bytes offered are the message.** Whatever its
arguments and whatever the world outside it holds. -/
theorem safe_exits_writes (args : List (List Byte)) (w : World) :
    SafeMem linux (startIn code .start 0 args w) ∧
      ExitsOnly fetch (· = 0) (startIn code .start 0 args w) ∧
      WritesOnly fetch (fun fd bytes => fd = 1 ∧ bytes = message) (startIn code .start 0 args w) :=
  whole_outputs checked (Q := fun c => c = 0) (q := fun c => c == 0) (fun c h => by simpa using h)
    (R := fun fd bs => fd = 1 ∧ bs = message) (r := fun fd b => fd == 1 && b == message)
    (fun fd bs h => by simpa using h) saidOk rfl rfl (LawsHold.nil _) args w

/-- Everything the program ever adds to the output is the message, or the
first so many bytes of it where the kernel took fewer than it was offered. -/
theorem output_is_message (args : List (List Byte)) (w : World) {s' : State}
    (hs : Steps fetch linux (startIn code .start 0 args w) s') :
    ∃ new, s'.world.writes = new ++ w.writes ∧ ∀ x ∈ new, ∃ n, x = message.take n := by
  obtain ⟨new, e, hall⟩ := (safe_exits_writes args w).2.2.output s' hs
  refine ⟨new, e, fun x hx => ?_⟩
  obtain ⟨_, _, n, ⟨_, rfl⟩, rfl⟩ := hall x hx
  exact ⟨n, rfl⟩

/-- **So the program as `lake exe hello` runs it is safe**, on the machine
that decodes its instructions from memory, whatever its arguments. -/
theorem safe (args : List (List Byte)) : SafeMem linux (startArgs args) :=
  start_eq args ▸ (safe_exits_writes args (startArgs args).world).1

/-- It ends only with status nought. -/
theorem exits (args : List (List Byte)) : ExitsOnly fetch (· = 0) (startArgs args) :=
  start_eq args ▸ (safe_exits_writes args (startArgs args).world).2.1

/-- And at a `write` offers its message, on descriptor 1. -/
theorem writes (args : List (List Byte)) :
    WritesOnly fetch (fun fd bytes => fd = 1 ∧ bytes = message) (startArgs args) :=
  start_eq args ▸ (safe_exits_writes args (startArgs args).world).2.2

end Hello
