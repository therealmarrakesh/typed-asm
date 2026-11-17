import TableProgram
import TypedAsm.U.Checked

/-!
# Table: typing and safety

The program is in `TableProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Table

/-! ## What the labels want -/

/-- A pointer to the record: sixteen bytes that may be written. -/
def pair : TyS := .ptr (.mk 16 .nil) true 0

/-- The blocks the program says its segments are: the table, eight bytes
holding a pointer to the record, not to be written; and the record. That
the table's eight bytes are the record's address is read from the program's
bytes. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start
    [(Asm.addr code base .table, { shape := .mk 8 (.cons 0 pair .nil), writable := false }),
     (Asm.addr code base .record, plainBlock 16 true)]

/-- The program for the checker: its instructions, and that the table is
one of the blocks said. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks (Asm.addr code base .table) }

/-- One label: the start, with nothing known. -/
def labels : List U.Label := [⟨entry, inProgram 0⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 0 program pg labels labels blocks blocks fuel 40

end Table
