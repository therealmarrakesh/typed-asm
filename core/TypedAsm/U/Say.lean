import TypedAsm.U.Whole

/-!
# Saying what a label wants

A label's context said by what differs from nothing being known: which
registers hold what, and what is known of the values named. The rest is the
same for every label of its sort: every other register holds whatever it
holds, and the stack is as the program, or the function, has it.
-/

namespace TypedAsm.U

attribute [local instance] IsLabel.dec

open TypedAsm

/-- Every register holding whatever it holds: each a value of the family. -/
def anyRegs : Regs Val :=
  ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3, .bvar 0 4, .bvar 0 5, .bvar 0 6, .bvar 0 7,
    .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13, .bvar 0 14, .bvar 0 15⟩

/-- What a register holds where the label is reached. -/
def Val.was (r : Reg) : Val := anyRegs.get r

/-- A value the label's family ranges over besides: the `k`th. -/
def Val.named (k : Nat) : Val := .bvar 0 (64 + k)

/-- What a register held when the function was entered, where the function
has pushed it since and may have changed it. -/
def Val.entered (r : Reg) : Val := .bvar 0 (32 + allRegs.idxOf r)

instance : Coe (BitVec 64) Val := ⟨.lit⟩
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

mutual

/-- A term said one family further in: each value of a family is then of
the family one further out. -/
def Val.lift : Val → Val
  | .lit v => .lit v
  | .var i => .var i
  | .bvar d i => .bvar (d + 1) i
  | .slot s => .slot s
  | .un u x => .un u x.lift
  | .bin u x y => .bin u x.lift y.lift
  | .tri u x y z => .tri u x.lift y.lift z.lift
  | .fop u fl x y => .fop u fl.lift x.lift y.lift
  | .app u x y => .app u x.lift y.lift

def FlagsT.lift : FlagsT → FlagsT
  | .lit f => .lit f
  | .var i => .var i
  | .bvar d => .bvar (d + 1)
  | .old => .old
  | .src u fl x y z => .src u fl.lift x.lift y.lift z.lift

end

/-- A term less so many: a number added where that is a number. -/
def Val.lessBy (a n : Val) : Val :=
  match n with
  | .lit k => .add a (.lit (-k))
  | n => a.less n

/-- A term and so many more: the term itself where that is none. -/
def Val.upBy (a : Val) (n : Nat) : Val := if n = 0 then a else a.plus (litNat n)

/-- A term less so many, a number where the term is. -/
def Val.downBy (a : Val) (n : Nat) : Val :=
  match a with
  | .lit x => .lit (x - BitVec.ofNat 64 n)
  | a => .add a (.lit (-(BitVec.ofNat 64 n)))

/-- **What has been put on the stack** since a program started or a
function was entered, one thing after another, the first put there first:
eight bytes holding whatever they hold; eight bytes holding a value; a
register a function keeps for its caller, as it was when the function was
entered (`Val.entered r`), which the function is to give back so; or so
many bytes holding whatever they hold. -/
inductive Pushed
  | any
  | val (v : Val)
  | saved (r : Reg)
  | bytes (n : Nat)
  deriving DecidableEq

/-- How many bytes of stack a thing put there takes. -/
def Pushed.size : Pushed → Nat
  | .bytes n => n
  | _ => 8

/-- How many bytes of stack all of them take. -/
def pushedBytes : List Pushed → Nat
  | [] => 0
  | p :: ps => p.size + pushedBytes ps

/-- The registers among them a function keeps for its caller. -/
def pushedSaved : List Pushed → List Reg
  | [] => []
  | .saved r :: ps => r :: pushedSaved ps
  | _ :: ps => pushedSaved ps

/-- The values among them, each with how far into the stack's region it
is: `top` is how far in the stack pointer was before any was put there, and
`c` how many bytes are there already. -/
def pushedSlots (top : Val) : Nat → List Pushed → List (Val × Val)
  | _, [] => []
  | c, .val v :: ps => (top.downBy (c + 8), v) :: pushedSlots top (c + 8) ps
  | c, .saved r :: ps => (top.downBy (c + 8), Val.entered r) :: pushedSlots top (c + 8) ps
  | c, p :: ps => pushedSlots top (c + p.size) ps

/-- **What a function returns with**, written one family in from a label
of the function: the registers it keeps as they were at entry, the stack
pointer past the return address, the bytes it was given below the stack
pointer and the eight that held the return address held still, the regions
it took given back, the regions it hands its caller, each at the address a
register holds at return, and whatever else was held, held. The other
registers hold whatever they hold, but for those said. How many bytes are
terms, said as at the label: a number, or what a value there comes to. A
region taken may be said to hold values when it is given back (`leaves`):
by the register it was taken at, how far in each value is, and the value.
`pushed` is what the function has put on the stack since it was entered:
the stack pointer is so far below where it was, and the registers saved
there are given back as they were. -/
def returnsWith (results : List (Reg × Val) := []) (room : Val := 0)
    (takes : List (Reg × Val) := []) (gives : List (Reg × Val) := [])
    (leaves : List (Reg × List (Val × Val)) := []) (pushed : List Pushed := []) : TyS :=
  .code
    (regsWith
      (regsWith anyRegs (keptRegs.map fun r =>
        (r, if (pushedSaved pushed).contains r then (Val.entered r).lift
          else .bvar 1 (allRegs.idxOf r))))
      ((.rsp, .add (.bvar 1 4) (.lit (BitVec.ofNat 64 (8 + pushedBytes pushed)))) :: results))
    (.bvar 0)
    ((((Val.bvar 1 4).upBy (pushedBytes pushed)).lessBy room.lift, ⟨room.lift.plus 8, []⟩) ::
      (takes.map fun t => (.bvar 1 (allRegs.idxOf t.1),
        ⟨t.2.lift, ((leaves.lookup t.1).getD []).map fun p => (p.1.lift, p.2.lift)⟩)) ++
      gives.map fun t => (.bvar 0 (allRegs.idxOf t.1), ⟨t.2.lift, []⟩))
    .nil (.bvar 1)

/-- **A label where a function is entered, or inside it**: the return
address known to be code wanting what the function returns with; so many
bytes below it the function's to use; what the function has put on the
stack since it was entered (`pushed`), the stack pointer below it; the
regions it takes from its caller and gives back, each at the address a
register holds at the label and so many bytes; the regions it hands its
caller when it returns; whatever else its caller holds; and the registers
and facts said. How many bytes are terms: a number, or what a value at the
label comes to. `leaves` says what values a region taken holds when the
function gives it back. -/
def inFunction (regs : List (Reg × Val) := []) (known : List (Val × TyS) := [])
    (room : Val := 0) (results : List (Reg × Val) := []) (takes : List (Reg × Val) := [])
    (gives : List (Reg × Val) := []) (leaves : List (Reg × List (Val × Val)) := [])
    (pushed : List Pushed := []) : CtxS where
  regs := regsWith anyRegs regs
  flags := .bvar 0
  held := (((Val.bvar 0 4).upBy (pushedBytes pushed)).lessBy room,
      ⟨room.plus 8, (room, .bvar 0 16) :: pushedSlots room 0 pushed⟩) ::
    takes.map fun t => (.bvar 0 (allRegs.idxOf t.1), ⟨t.2, []⟩)
  known := (.bvar 0 16, returnsWith results room takes gives leaves pushed) :: known
  rest := .bvar 0

/-- How many arguments the program was handed, its own name among them:
the value held where the stack pointer is when it starts. -/
def argCountV : Val := .bvar 0 18

/-- **A label in the program's own code, outside any function**, the
program having `n` slots of stack: the stack held whole, with the count of
arguments the program started with above it; what the program has put on
the stack since it started (`pushed`), the stack pointer below it; after
the count, the row of pointers to the arguments' text; the registers and
facts said; and whatever regions it holds besides. With nothing said it is
what the program starts with. -/
def inProgram (n : Nat) (pushed : List Pushed := []) (regs : List (Reg × Val) := [])
    (known : List (Val × TyS) := []) (held : List (Val × HeldS) := []) : CtxS :=
  { entryCtx (stackRoom n) with
    regs := regsWith
      ((entryCtx (stackRoom n)).regs.set .rsp
        (.add (.bvar 0 17) (litNat (stackRoom n - pushedBytes pushed)))) regs
    held := (.bvar 0 17, ⟨litNat (stackRoom n + 8),
        (litNat (stackRoom n), .bvar 0 18) :: pushedSlots (litNat (stackRoom n)) 0 pushed⟩) ::
      held
    known := (entryCtx (stackRoom n)).known ++ known }

/-- What a program starts with is that label with nothing said. -/
theorem inProgram_entry (n : Nat) : inProgram n = entryCtx (stackRoom n) := rfl

mutual

/-- How deep code wanting contexts is nested in a type. -/
def TyS.depth : TyS → Nat
  | .ptr S _ _ => S.depth
  | .nullable τ => τ.depth
  | .orErr τ => τ.depth
  | .arr _ τ => τ.depth
  | .code _ _ _ known _ => known.depth + 1
  | _ => 0

def ShapeS.depth : ShapeS → Nat
  | .mk _ vals => vals.depth

def ValsS.depth : ValsS → Nat
  | .nil => 0
  | .cons _ τ rest => max τ.depth rest.depth

def FactsS.depth : FactsS → Nat
  | .nil => 0
  | .cons _ τ rest => max τ.depth rest.depth

end

/-- The deepest of some facts' types. -/
def factsDepth (fs : List (Val × TyS)) : Nat := fs.foldl (fun d f => max d f.2.depth) 0

/-- **How far the check of a program goes, unless told to go further**: a
walk from a label that passes no instruction twice is no longer than the
program; and one type is compared with another no deeper than code is
nested in the types the program, its labels and its kinds say. A loop with
no label, gone round a number of times that is written out, is passed more
than once, and may need more. -/
def needFuel (pg : Prog) (labels : List Label) (ks : List (Nat × ShapeS)) : Nat :=
  pg.code.length + 2 +
    labels.foldl (fun d l => max d (factsDepth l.pat.known)) (factsDepth pg.statics) +
    ks.foldl (fun d k => max d k.2.depth) 0

/-- Things known, one after another, from a list. -/
def factsOf : List (Val × TyS) → FactsS
  | [] => .nil
  | f :: fs => .cons f.1 f.2 (factsOf fs)

/-- **A pointer to code wanting a context**: what a value is known to be
where it is the address of code that may be entered in any member of the
context's family. A pointer to a function is a pointer to code wanting what
the function's label wants. -/
def codeOf (E : CtxS) : TyS := .code E.regs E.flags E.held (factsOf E.known) E.rest

/-- What a program says of something in one of its segments: that its
address is that of a byte of the segment's block. -/
def staticIn (blocks : List (BitVec 64 × LayoutS)) (a : BitVec 64) : List (Val × TyS) :=
  match blocks.find? fun b =>
      decide (b.1 ≤ a) && decide (a.toNat < b.1.toNat + b.2.shape.size) with
  | some b => [(.lit a, .ptr b.2.shape b.2.writable (a - b.1).toNat)]
  | none => []

/-- What a program says of a block of a kind among its segments' blocks:
that its address is that of a block of the kind. -/
def staticRef (blocks : List (BitVec 64 × LayoutS)) (a : BitVec 64) : List (Val × TyS) :=
  match blocks.find? fun b => b.1 == a with
  | some b =>
    match b.2.tag with
    | some t => [(.lit a, .ref t b.2.writable 0)]
    | none => []
  | none => []

/-- A block of plain bytes. -/
def plainBlock (size : Nat) (writable : Bool) : LayoutS :=
  { shape := .mk size .nil, writable := writable }

/-- A segment's pages as the blocks said of it, in the order of their
addresses, and blocks of plain bytes for what lies between and after. -/
def cutSeg (g : Nat × Perm × List Byte) : Nat → List (BitVec 64 × LayoutS) →
    List (BitVec 64 × LayoutS)
  | cur, [] =>
    if cur < g.1 + pageBytes g.2.2.length then
      [(BitVec.ofNat 64 cur, plainBlock (g.1 + pageBytes g.2.2.length - cur) g.2.1.writable)]
    else []
  | cur, x :: xs =>
    (if cur < x.1.toNat then
      [(BitVec.ofNat 64 cur, plainBlock (x.1.toNat - cur) g.2.1.writable)] else []) ++
      x :: cutSeg g (x.1.toNat + x.2.size) xs

/-- The typed values of a row: `n` of them, eight bytes each, from byte
`o`, of each of which `τ` is known. -/
def rowVals (τ : TyS) : Nat → Nat → ValsS
  | _, 0 => .nil
  | o, n + 1 => .cons o τ (rowVals τ (o + 8) n)

/-- A block that is a row of `n` values, of each of which `τ` is known. -/
def rowBlock (n : Nat) (τ : TyS) (writable : Bool) : LayoutS :=
  { shape := .mk (8 * n) (rowVals τ 0 n), writable := writable }

/-- What a program says of a row among its segments' blocks: that its
address is that of so many values of which `τ` is known. -/
def staticRow (a : BitVec 64) (n : Nat) (τ : TyS) : List (Val × TyS) :=
  [(.lit a, .arr (.lit (BitVec.ofNat 64 n)) τ)]

/-- A block of text that is not written: the bytes given, which are to end
in one of nought, and are said. -/
def textBlock (bytes : List Byte) : LayoutS :=
  { shape := .mk 0 .nil, writable := false, text := bytes.length, said := some bytes }

/-- What a program says of text in one of its blocks: that its address is
that of the text's first byte, with more after it. -/
def staticText (a : BitVec 64) : List (Val × TyS) := [(.lit a, .str (.lit 1))]

variable {L : Type} [IsLabel L]

/-- **A program's first blocks, some of them said**: each segment's pages
cut into the blocks said of it, which are to be given in the order of their
addresses, with plain bytes between. -/
def blocksWith (code : List (Asm L)) (l : L) (says : List (BitVec 64 × LayoutS)) :
    List (BitVec 64 × LayoutS) :=
  (Asm.imageFast (Asm.base code) code l).flatMap fun g =>
    cutSeg g g.1 (says.filter fun x =>
      decide (g.1 ≤ x.1.toNat) && decide (x.1.toNat < g.1 + pageBytes g.2.2.length))

/-- The address of a program's instruction, counted from nought in the
order they are written. -/
def instrAddr (code : List (Asm L)) (i : Nat) : BitVec 64 :=
  ((Asm.table (Asm.base code) code).map (·.1)).getD i 0

end TypedAsm.U
