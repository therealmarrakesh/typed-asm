import DispatchProgram
import TypedAsm.U.Checked

/-!
# Dispatch: typing and safety

The program is in `DispatchProgram.lean`. This file says what its labels want
and checks it: one check, run by Lean's kernel, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.
Nothing is proved by hand.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Dispatch

/-! ## What the labels want -/

/-- A pointer to a function: to code wanting what a function's label wants.
Its return address is on the stack, it gives back the registers a function
must as it found them, and it holds whatever else its caller does. -/
def fn : TyS := codeOf inFunction

/-- The blocks the program says its segments are: the table, two pointers
to functions, not to be written. That each of its entries is the address of
a function is read from the program's bytes, and that the code there is a
function's is the labels' typing. -/
def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start
    [(Asm.addr code base .table,
      { shape := .mk 16 (.cons 0 fn (.cons 8 fn .nil)), writable := false })]

/-- The program for the checker: its instructions, and that the table is
one of the blocks said. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks (Asm.addr code base .table) }

/-- The labels: the start, and the two functions. A function is called
through the table at an index the program has compared with the table's
length, and through a register loaded from the table: what the program
knows of that register is known still after each call. -/
def labels : List U.Label :=
  [⟨entry, inProgram 1⟩,
   ⟨Asm.addr code base .double, inFunction⟩,
   ⟨Asm.addr code base .square, inFunction⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 1 program pg labels labels blocks blocks fuel 40

end Dispatch
