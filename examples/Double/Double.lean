import DoubleProgram
import TypedAsm.Tactic

/-!
# Double: typing and safety

The program is in `DoubleProgram.lean`. This file types it and proves it
safe. It is kept separate so that running the program does not link the
tactics.
-/

open TypedAsm

namespace Double

/-! ## The typing -/

/-- A page of plain bytes. -/
abbrev words : Shape := .raw 4096

/-- `double` called with exactly `p` in `rdi` takes the page at `p` and gives
it back, still a page of plain bytes. It uses no stack. -/
def doubleSig (p : BitVec 64) : FnSig where
  args := fun r => if r = .rdi then .eq p else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0
  takes := [(p, words)]
  gives := [(p, words)]

/-- Back from the call: `rbx` still holds the page's address, and the page
is the program's again. -/
def backCtx (p : BitVec 64) : Ctx :=
  ⟨fun r => if r = .rbx then .eq p else .int, [], 8, Flags.Any, [(p, words)], 0⟩

/-- Inside the function: `rdi` holds the page's address, the page is the
function's, and after it come whatever blocks the caller owns besides. -/
def inside (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) : Ctx :=
  ⟨fun r => if r = .rdi then .eq p else if calleeSaved r then saved r else .int,
    .slot (.code ret) :: rest, room, Flags.Any, (p, words) :: ret.owned.drop 1, ret.above⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | back (p : BitVec 64) : At .back (backCtx p)
  | double (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (doubleSig p).CallerOk saved ret rest room →
    At .double ((doubleSig p).entry saved ret rest room)
  | loop (p : BitVec 64) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    (doubleSig p).CallerOk saved ret rest room → At .loop (inside p saved ret rest room)

asm_typing At

/-! ## Safety -/

asm_safety At.start

end Double

