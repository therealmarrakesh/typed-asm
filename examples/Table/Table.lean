import TableProgram
import TypedAsm.Tactic

/-!
# Table: typing and safety

The program is in `TableProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Table

-- Where the data is loaded: the table first, then the record.
asm_label dataBase .table
-- Where the record is.
asm_label recordAddr .record

/-! ## The typing -/

/-- A pointer to a writable record of sixteen plain bytes: two numbers. -/
def pair : Ty := .ptr (.raw 16) true 0

inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

/-- The table: eight bytes, holding a pointer to the record. -/
def tableLayout : Layout := ⟨⟨8, [(0, pair)]⟩, false, none, 0⟩

def recordLayout : Layout := ⟨.raw 16, true, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, tableLayout), (recordAddr, recordLayout)]

asm_typing At blocks blocks

/-! ## Safety -/

-- The table's entry is a pointer to the record because the data says so:
-- that is read from the program's bytes.
asm_safety At.start

end Table
