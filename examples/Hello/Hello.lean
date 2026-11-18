import HelloProgram
import TypedAsm.U.Checked
import TypedAsm.Runs

/-!
# Hello: typing, safety, and what it writes

The program is in `HelloProgram.lean`. This file checks it and states what
the check shows: it is safe, it ends only with status nought, and what it
writes is its message. One check, run as compiled code, decides that the
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

asm_checked code start .start stack 0 program pg labels labels
  exits (· == 0) writes (fun fd b => fd == 1 && b == message) said said

/-! ## What it shows besides -/

/-- Everything the program ever adds to the output is the message, or the
first so many bytes of it where the kernel took fewer than it was offered. -/
theorem output_is_message (args : List (List Byte)) (w : World) {s' : State}
    (hs : Steps fetch linux (startIn code .start 0 args w) s') :
    ∃ new, s'.world.writes = new ++ w.writes ∧ ∀ x ∈ new, ∃ n, x = message.take n := by
  obtain ⟨new, e, hall⟩ := (safe_exits_writes_in args w).2.2.output s' hs
  refine ⟨new, e, fun x hx => ?_⟩
  obtain ⟨_, bytes, n, hr, rfl⟩ := hall x hx
  have hb : bytes = message := eq_of_beq (Bool.and_eq_true _ _ ▸ hr).2
  exact ⟨n, hb ▸ rfl⟩

end Hello
