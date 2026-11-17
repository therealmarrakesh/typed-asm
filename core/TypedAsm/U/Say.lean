import TypedAsm.U.Whole

/-!
# Saying what a label wants

A label's context said by what differs from nothing being known: which
registers hold what, and what is known of the values named. The rest is the
same for every label of its sort: every other register holds whatever it
holds, and the stack is as the program, or the function, has it.
-/

namespace TypedAsm.U

open TypedAsm

/-- Every register holding whatever it holds: each a value of the family. -/
def anyRegs : Regs Val :=
  ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3, .bvar 0 4, .bvar 0 5, .bvar 0 6, .bvar 0 7,
    .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13, .bvar 0 14, .bvar 0 15⟩

/-- What a register holds where the label is reached. -/
def Val.was (r : Reg) : Val := anyRegs.get r

/-- A value the label's family ranges over besides: the `k`th. -/
def Val.named (k : Nat) : Val := .bvar 0 (17 + k)

instance : Coe (BitVec 64) Val := ⟨.lit⟩
instance (n : Nat) : OfNat Val n := ⟨.lit (BitVec.ofNat 64 n)⟩
instance : Add Val := ⟨.add⟩
instance : Neg Val := ⟨.un (.neg .w64)⟩
instance : _root_.Sub Val := ⟨fun a b => .add a (.un (.neg .w64) b)⟩
instance : HShiftLeft Val Nat Val := ⟨.shl⟩

/-- Registers, with those listed holding what is said. -/
def regsWith (base : Regs Val) : List (Reg × Val) → Regs Val
  | [] => base
  | p :: ps => regsWith (base.set p.1 p.2) ps

/-- The registers a function gives back as it found them. -/
def keptRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- **What a function returns with**, written one family in from its
entry: the registers it keeps as they were at entry, the stack pointer past
the return address, the bytes it was given below the stack pointer and the
eight that held the return address held still, and whatever else was held,
held. The other registers hold whatever they hold, but for those said. -/
def returnsWith (results : List (Reg × Val) := []) (room : Nat := 0) : TyS :=
  .code
    (regsWith
      (regsWith anyRegs (keptRegs.map fun r => (r, .bvar 1 (allRegs.idxOf r))))
      ((.rsp, .add (.bvar 1 4) (.lit 8)) :: results))
    (.bvar 0) [(.add (.bvar 1 4) (.lit (-(BitVec.ofNat 64 room))), ⟨room + 8, []⟩)] .nil (.bvar 1)

/-- **A label where a function is entered**: the return address at the
stack pointer, known to be code wanting what the function returns with; so
many bytes below the stack pointer the function's to use; whatever else its
caller holds; and the registers and facts said. -/
def inFunction (regs : List (Reg × Val) := []) (known : List (Val × TyS) := [])
    (room : Nat := 0) (results : List (Reg × Val) := []) : CtxS where
  regs := regsWith anyRegs regs
  flags := .bvar 0
  held := [(.add (.bvar 0 4) (.lit (-(BitVec.ofNat 64 room))), ⟨room + 8, [(room, .bvar 0 16)]⟩)]
  known := (.bvar 0 16, returnsWith results room) :: known
  rest := .bvar 0

/-- **A label in the program's own code, outside any function**: the stack
it started with held whole, the stack pointer so many bytes below where it
started; and the registers and facts said. -/
def inProgram (n : Nat) (pushed : Nat := 0) (regs : List (Reg × Val) := [])
    (known : List (Val × TyS) := []) : CtxS :=
  if n = 0 then { entryPat with regs := regsWith anyRegs regs, known := known }
  else
    { entryPatStack (stackSize n) with
      regs := regsWith
        (anyRegs.set .rsp (.add (.bvar 0 16) (.lit (BitVec.ofNat 64 (stackSize n - pushed))))) regs
      known := known }

/-- What a program says of something in one of its segments: that its
address is that of a byte of the segment's block. -/
def staticIn (blocks : List (BitVec 64 × Layout)) (a : BitVec 64) : List (Val × TyS) :=
  match blocks.find? fun b =>
      decide (b.1 ≤ a) && decide (a.toNat < b.1.toNat + b.2.shape.size) with
  | some b => [(.lit a, .ptr (.mk b.2.shape.size .nil) b.2.writable (a - b.1).toNat)]
  | none => []

end TypedAsm.U
