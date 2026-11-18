import TypedAsm.U.Labels
import TypedAsm.Print

/-!
# Why a program is refused

Where a check fails: the places its walks stop short, and at each what was
missing, said of the program. Which instruction it is; what it reads or
writes, and where; what the machine could do there if the program ran; what
a register holds and which earlier instruction left it so; and, where a
label is reached in a context it does not allow, each thing the label wants
that is not so.

It is worked out from the parts the check itself is made of: the same
finding of memory, the same comparison of contexts. It proves nothing and
nothing rests on it: it is for the person writing the labels.
-/

namespace TypedAsm.U

open TypedAsm

/-! ## Terms, to be read -/

/-- A number, to be read: small ones as they are, those just below two to
the sixty-fourth as what they are below nought, others in sixteens. -/
def litSay (v : BitVec 64) : String :=
  if v.toNat < 65536 then toString v.toNat
  else if 18446744073709551616 - v.toNat ≤ 65536 then s!"-{18446744073709551616 - v.toNat}"
  else "0x" ++ String.ofList (Nat.toDigits 16 v.toNat)

/-- The names a walk's terms use for the context it started from: the
`width` from `base` on; and where it started. -/
structure Frame where
  base : Nat := 0
  width : Nat := 0
  addr : BitVec 64 := 0

/-- The names of a walk, and of the walks that led to it, the nearest
first: the code a call returns to is walked from names of its own, and what
is wanted of it is said by those of the walk the call is in. -/
abbrev Names := List Frame

def addrSay (a : BitVec 64) : String := "0x" ++ String.ofList (Nat.toDigits 16 a.toNat)

/-- A value of a label's family, by what it is by the custom the labels are
said by; `at_` says which label, where it is not the walk's own. -/
def nameSay (j : Nat) (at_ : String := "") : String :=
  match allRegs[j]? with
  | some r => s!"{r.name64} at the label" ++ at_
  | none =>
    (if j = 16 then "the return address"
    else if j = 17 then "the start of the stack"
    else if j = 18 then "the count of arguments"
    else if 32 ≤ j ∧ j < 48 then
      match allRegs[j - 32]? with
      | some r => s!"{r.name64} as the function was entered"
      | none => s!"value {j} of the label"
    else if 64 ≤ j then s!"named value {j - 64}"
    else s!"value {j} of the label") ++ at_

/-- Where the explanation puts a value of the label reached that nothing in
the context reached fixes. -/
def unfixed : Nat := 1000000000

/-- A name, to be read: of the walk's own start, of a walk that led to it,
or made on the way. -/
def namesVar (i : Nat) : Bool → Names → String
  | _, [] => s!"[a value met on the way, #{i}]"
  | own, f :: fs =>
    if f.base ≤ i ∧ i < f.base + f.width then
      nameSay (i - f.base) (if own then "" else s!" walked from {addrSay f.addr}")
    else if i < f.base then namesVar i false fs
    else s!"[a value met on the way, #{i}]"

def Names.var (nm : Names) (i : Nat) : String :=
  if unfixed ≤ i then s!"[{nameSay (i - unfixed)}, of the label reached: nothing fixes it]"
  else namesVar i true nm

/-- Round brackets about what has a space in it. -/
def paren (t : String) : String := if t.toList.contains ' ' then "(" ++ t ++ ")" else t

/-- The terms of a sum after the first, each with whether it is taken away. -/
def moreSay : List (Bool × String) → String
  | [] => ""
  | (neg, t) :: ts => (if neg then " - " else " + ") ++ t ++ moreSay ts

/-- A sum, to be read: its terms, each added or taken away, and the number
added. -/
def sumFin (p : List (Bool × String) × BitVec 64) : String :=
  match p.1 with
  | [] => litSay p.2
  | (neg, t) :: ts =>
    (if neg then "-" else "") ++ t ++ moreSay ts ++
      (if p.2 = 0 then "" else if p.2.msb then s!" - {(-p.2).toNat}" else s!" + {litSay p.2}")

/-- A term as a sum: its terms, each to be read, and the number added. -/
def Val.sum (nm : Names) : Val → List (Bool × String) × BitVec 64
  | .lit v => ([], v)
  | .var i => ([(false, nm.var i)], 0)
  | .bvar d i =>
    ([(false, if d = 0 then nameSay i else s!"[value {i} of the family {d} out]")], 0)
  | .slot _ => ([(false, "[an operand]")], 0)
  | .bin .add a b => ((a.sum nm).1 ++ (b.sum nm).1, (a.sum nm).2 + (b.sum nm).2)
  | .un (.shl k) a => ([(false, paren (sumFin (a.sum nm)) ++ s!" << {k}")], 0)
  | .un (.neg _) a => ([(true, paren (sumFin (a.sum nm)))], 0)
  | .un _ a => ([(false, s!"f({sumFin (a.sum nm)})")], 0)
  | .bin (.imul _) a b =>
    ([(false, paren (sumFin (a.sum nm)) ++ " * " ++ paren (sumFin (b.sum nm)))], 0)
  | .bin _ a b => ([(false, s!"f({sumFin (a.sum nm)}, {sumFin (b.sum nm)})")], 0)
  | .tri _ a b c =>
    ([(false, s!"f({sumFin (a.sum nm)}, {sumFin (b.sum nm)}, {sumFin (c.sum nm)})")], 0)
  | .fop _ _ a b => ([(false, s!"f({sumFin (a.sum nm)}, {sumFin (b.sum nm)})")], 0)
  | .app f a b => ([(false, s!"fn{f}({sumFin (a.sum nm)}, {sumFin (b.sum nm)})")], 0)

/-- A term, to be read: sums gathered, and each name by what it is. -/
def Val.say (v : Val) (nm : Names := []) : String := sumFin (v.sum nm)

/-- What is known of a value, to be read, in brief. -/
def TyS.say (nm : Names := []) : TyS → String
  | .any => "anything"
  | .ptr (.mk n _) w off =>
    s!"a pointer {off} bytes into a block of {n}" ++ (if w then " that may be written" else "")
  | .ref t _ off => s!"a pointer {off} bytes into a block of kind {t}"
  | .nullable _ => "nought, or something known"
  | .orErr _ => "an error number, or something known"
  | .str _ => "a pointer to text"
  | .atom i => s!"what name {i} stands for"
  | .code .. => "code wanting a family of contexts"
  | .range lo hi => s!"from {litSay lo} round to {litSay hi}"
  | .arr c _ => s!"the address of {c.say nm} values in a row"
  | .upTo t strict => (if strict then "below " else "at most ") ++ t.say nm

/-- A region held, to be read. -/
def regionSay (g : Val × HeldS) (nm : Names := []) : String :=
  s!"{g.2.size.say nm} bytes at {g.1.say nm}" ++
    (if g.2.slots.isEmpty then ""
     else " holding " ++
       ", ".intercalate (g.2.slots.map fun p => s!"{p.2.say nm} at {p.1.say nm}"))

/-- The regions held, to be read. -/
def heldSay (h : List (Val × HeldS)) (nm : Names := []) : String :=
  if h.isEmpty then "nothing" else "; ".intercalate (h.map (regionSay · nm))

/-! ## Which instruction left a register as it is -/

/-- An instruction stepped over on the way: where it is, and the context
before it. -/
structure Was where
  addr : BitVec 64
  i : Instr
  before : CtxS

/-- **Which instruction left a register holding what it holds**: the last
on the way, the nearest first, before which it held something else. -/
def gave (path : List Was) (Γ : CtxS) (r : Reg) : String :=
  match path.find? fun w => w.before.regs.get r != Γ.regs.get r with
  | some w => s!"left so by `{w.i.toAsm}` at {addrSay w.addr}"
  | none => "as it was at the label"

/-- A register, what it holds, and what left it so. -/
def regSay (path : List Was) (Γ : CtxS) (r : Reg) (nm : Names := []) : String :=
  s!"{r.name64} holds {(Γ.regs.get r).say nm}, {gave path Γ r}"

/-- The registers an address is made of. -/
def memRegs : Mem → List Reg
  | .sib b i _ => b.toList ++ (i.map fun x => x.1.toReg).toList
  | .rip _ => []

/-- A place a walk stopped short, and why. -/
structure Refusal where
  /-- The label the walk started from. -/
  label : BitVec 64
  /-- Where it stopped. -/
  addr : BitVec 64
  why : String
  /-- What was missing, thing by thing. -/
  detail : List String := []
  deriving Repr

/-- What is said where a walk reaches an instruction again, and where it
has gone too far. -/
def againSay : String := "is reached a second time with no label passed on the way"
def farSay : String := "with no label and no end reached"

/-- Whether the walk was cut short here: an instruction reached again
(`1`), or too far gone (`2`); and not refused of itself (`0`). -/
def Refusal.cut (f : Refusal) : Nat :=
  if f.why == againSay then 1 else if f.why.endsWith farSay then 2 else 0

/-- An address, to be read: which instruction of the program it is, and
the instruction. -/
def whereSay (pg : Prog) (a : BitVec 64) : String :=
  match pg.code.findIdx? fun e => e.1 = a, pg.code.find? fun e => e.1 = a with
  | some n, some e => s!"instruction {n}, `{e.2.1.toAsm}` ({addrSay a})"
  | _, _ => addrSay a

/-- A refusal, to be read. -/
def Refusal.text (pg : Prog) (f : Refusal) : String :=
  s!"walking from {whereSay pg f.label}: at {whereSay pg f.addr}: {f.why}" ++
    String.join (f.detail.map fun d => "\n    " ++ d)

/-- The refusals worth reading: of a walk cut short, the first instruction
it reached again, or where none, the first place it had gone too far; and
all else. -/
def tidy : List Refusal → List Refusal → List Refusal
  | _, [] => []
  | seen, f :: fs =>
    if f.cut = 0 then f :: tidy seen fs
    else if seen.any fun g => g.label == f.label && g.cut ≤ f.cut then tidy seen fs
    else if f.cut = 2 && fs.any fun g => g.label == f.label && g.cut = 1 then tidy seen fs
    else f :: tidy (f :: seen) fs

/-! ## Why a context may not be regarded as another -/

/-- **Each thing a context wanted asks that the context reached does not
give**: register by register, region by region, fact by fact; by the same
comparison the check makes. -/
def regardWhy (nm : Names) (sm : List (Val × TyS) → Val → Val → Bool) (ent : TyS → TyS → Bool)
    (path : List Was) (Γ Δ : CtxS) : List String :=
  (allRegs.filterMap fun r =>
    if sm Γ.known (Γ.regs.get r) (Δ.regs.get r) then none
    else some s!"{regSay path Γ r nm}; wanted there: {(Δ.regs.get r).say nm}") ++
  (if Γ.flags == Δ.flags then [] else ["the flags are not the ones wanted"]) ++
  (match partsS sm Γ.known Γ.held Δ.held with
   | none =>
     (Δ.held.filterMap fun d =>
       if (hostOf sm Γ.known d Γ.held).isSome then none
       else some s!"wanted held: {regionSay d nm}; not found in what is held") ++
     ["what is held: " ++ heldSay Γ.held nm]
   | some P =>
     (if apartS Γ.known P then [] else ["two regions wanted overlap in what is held"]) ++
     (if coverS Γ.held P then []
      else ["more is held than is wanted, and what is wanted does not range over the rest: " ++
        heldSay Γ.held nm])) ++
  (Δ.known.filterMap fun f =>
    if factFrom ent Γ.known f then none
    else
      match f.1.lit?, f.2 with
      | some a, .code .. =>
        some s!"the code at {addrSay a} is not typed for what is wanted of it: why, follows"
      | _, _ =>
        some s!"wanted known of {f.1.say nm}: {f.2.say nm}; not shown by what is known") ++
  (if Δ.rest == Γ.rest then [] else ["what else is held is not what is wanted"])

/-- **Why a context reached may not be made a member of a family**: as the
check makes it ready, and then each thing wanted that is not so. Where the
family wants code at an address typed, a return address say, and it is
not, `whyJ` says why: the faults of the walk from there. -/
def closeWhy (nm : Names) (sm : List (Val × TyS) → Val → Val → Bool)
    (ent : Nat → TyS → TyS → Bool)
    (justify : Nat → BitVec 64 → CtxS → Bool) (whyJ : Nat → BitVec 64 → CtxS → List Refusal)
    (path : List Was) (P Γ : CtxS) (k : Nat) : List String × List Refusal :=
  if !(joinAll Γ.held.length Γ).under k then
    (["the context reached mentions a name it may not"], [])
  else
    match nameSlots (joinAll Γ.held.length Γ) (wantedCode P (joinAll Γ.held.length Γ)) k with
    | none => (["a value the family names lies outside what is held, or is not placed"], [])
    | some Γ' =>
      let kn := k + (wantedCode P (joinAll Γ.held.length Γ)).length
      let o := (matchOpen P Γ').opening
      let fixed := (matchOpen P Γ').bs.map (·.1)
      -- what the label wants, with each value nothing fixes shown as that
      let Δ := P.open { o with b := fun j => if fixed.contains j then o.b j else .var (unfixed + j) }
      (regardWhy nm sm (ent kn) path (Γ'.addKnown (learnedFacts justify kn Γ' Δ)) Δ,
       (askedCode Γ' Δ).flatMap fun x =>
         if justify kn x.1 (x.2.1.addKnown (carried Γ')) then []
         else whyJ kn x.1 (x.2.1.addKnown (carried Γ')))

/-! ## Why an instruction is not typed -/

/-- **Why the instruction at an address is not stepped over**, in a
context: what it would need, and what the machine could do there. -/
def stepWhy (nm : Names) (pg : Prog) (path : List Was) (Γ : CtxS) (k : Nat) (a : BitVec 64) :
    String × List String :=
  match pg.code.find? fun e => e.1 = a with
  | none =>
    ("no instruction of the program is here",
      ["on the machine: whatever bytes are here would be run as instructions"])
  | some (_, i, len) =>
    if i = .syscall then
      if !pg.pre Γ then
        ("the system call here is not seen to meet what is asked of the program",
          ["the status it ends with, or the bytes it writes, are not shown to be as wanted",
            regSay path Γ .rax nm, regSay path Γ .rdi nm, regSay path Γ .rsi nm, regSay path Γ .rdx nm])
      else
        match Γ.regs.rax.lit? with
        | none =>
          ("which system call this is, is not a number written out",
            [regSay path Γ .rax nm,
              "on the machine: any call might be made, with whatever the registers hold"])
        | some nr =>
          match linuxKind nr with
          | none =>
            (s!"system call {nr.toNat} is not one the model of the kernel has", [])
          | some (.fills b room) =>
            (s!"system call {nr.toNat} stores bytes at the address in {b.name64}",
              [regSay path Γ b nm,
                match room with
                | .inl r => "as many as: " ++ regSay path Γ r nm
                | .inr n => s!"as many as {n}",
                "they are not shown to lie in memory the code holds, or in a block that may " ++
                  "be written and holds no typed value there",
                "on the machine: the kernel could write over memory the program relies on"])
          | some .map =>
            ("memory is asked for in a form the model of the kernel does not have",
              ["wanted: rdi nought, rsi a number written out, rdx 3, r10 0x22",
                regSay path Γ .rdi nm, regSay path Γ .rsi nm, regSay path Γ .rdx nm, regSay path Γ .r10 nm])
          | some .unmap =>
            ("memory is given back that is not held whole",
              ["wanted: a region held at the address in rdi, of as many whole pages as rsi says",
                regSay path Γ .rdi nm, regSay path Γ .rsi nm,
                "what is held: " ++ heldSay Γ.held nm,
                "on the machine: memory still in use would be gone, and the next use of it " ++
                  "would fault"])
          | some _ => ("the context after the system call mentions a name it may not", [])
    else
      match i.sem with
      | none => (s!"`{i.toAsm}` is not an instruction the checker has a description of", [])
      | some s =>
        match readAny pg.kinds Γ k (a + len) s.rd with
        | none =>
          (s!"`{i.toAsm}` reads memory that is not shown to be the program's",
            (match s.rd with
             | some (m, n) =>
               [s!"{n} bytes at {(eaS Γ.regs (a + len) m).say nm}"] ++
                 (memRegs m).map (regSay path Γ · nm)
             | none => []) ++
            ["wanted: bytes of a region the code holds, of a block a value is known to point " ++
                "into, of text, or of a row of values",
              "what is held: " ++ heldSay Γ.held nm,
              "on the machine: it could read memory the program does not have, and fault"])
        | some (cell, extra) =>
          let Γ₁ : CtxS := { Γ with known := extra ++ Γ.known }
          let σ := fillOf Γ s.srcs (a + len) (eaTerm Γ (a + len) s.ea) cell
          if !s.guard.okS Γ₁ Γ.flags (s.ga.fillN σ) (s.gb.fillN σ) (s.gc.fillN σ) then
            (s!"`{i.toAsm}` may fault of itself",
              ["a divisor not shown to be other than nought, or a quotient not shown to fit",
                s!"of: {(s.ga.fillN σ).say nm}, {(s.gb.fillN σ).say nm}, {(s.gc.fillN σ).say nm}",
                "on the machine: a divide error"])
          else
            match writeAny pg.kinds Γ₁ (a + len) (s.store.fillN σ) s.wr with
            | none =>
              (s!"`{i.toAsm}` writes memory that is not shown to be the program's to write",
                (match s.wr with
                 | some (m, n) =>
                   [s!"{n} bytes at {(eaS Γ.regs (a + len) m).say nm}"] ++
                     (memRegs m).map (regSay path Γ · nm)
                 | none => []) ++
                ["wanted: bytes of a region the code holds, or of a block that may be " ++
                    "written, where what is stored is of the type the block says",
                  "what is held: " ++ heldSay Γ.held nm,
                  "on the machine: it could write over memory the program relies on, or fault"])
            | some _ =>
              (s!"the context after `{i.toAsm}` mentions a name it may not, or its branch " ++
                "is on flags not defined", [])

/-! ## The places a walk stops short -/

/-- Where the instruction just stepped over is: the one that ends at `next`. -/
def stepAddr (pg : Prog) (i : Instr) (next : BitVec 64) : BitVec 64 :=
  match pg.code.find? fun e => e.2.1 == i && e.1 + e.2.2 == next with
  | some e => e.1
  | none => next

/-- The places a walk stops short: as `Walk.closes` judges it, with the
reasons kept. -/
def Walk.faults (pg : Prog) (ent : Nat → TyS → TyS → Bool)
    (justify : Nat → BitVec 64 → CtxS → Bool) (whyJ : Nat → BitVec 64 → CtxS → List Refusal)
    (labels : List Label) (from_ : BitVec 64) (nm : Names) (fuel : Nat) :
    List Was → Nat → Walk → List Refusal
  | path, k, .stop a Γ =>
    match labels.find? fun l => l.addr == a with
    | some l =>
      if (closeCtx (sameBy pg.fns pg.laws) ent justify l.pat Γ k).isSome then []
      else
        let w := closeWhy nm (sameBy pg.fns pg.laws) ent justify whyJ path l.pat Γ k
        ⟨from_, a, "arrives at a label in a context the label does not allow", w.1⟩ :: w.2
    | none =>
      if (walk pg (fun _ => false) true 1 k a Γ).moved then
        -- the instruction here can be stepped over: the walk was cut short
        if path.any fun w => w.addr == a then
          let round := a :: (path.takeWhile fun w => w.addr != a).map (·.addr)
          let low := round.foldl (fun m x => if x.toNat < m.toNat then x else m) a
          [⟨from_, a, againSay,
            ["a loop is to have a label where it is jumped back to, saying what is so each " ++
              "time round",
              s!"the first instruction of this loop is {whereSay pg low}"]⟩]
        else
          [⟨from_, a, s!"is {fuel} instructions on " ++ farSay, []⟩]
      else
        let w := stepWhy nm pg path Γ k a
        [⟨from_, a, w.1, w.2⟩]
  | path, k, .arrive t Γ =>
    match Γ.known.find? fun f => f.1.same t && f.2.isCode with
    | some (tv, .code regs flags held known rest) =>
      if tv.under k &&
          (match closeCtx (sameBy pg.fns pg.laws) ent justify (codeCtx regs flags held known rest)
              Γ k with
           | some (Γ', _) => Γ'.known.contains (tv, .code regs flags held known rest)
           | none => false) then []
      else
        let w := closeWhy nm (sameBy pg.fns pg.laws) ent justify whyJ path
          (codeCtx regs flags held known rest) Γ k
        ⟨from_, (path.head?.map (·.addr)).getD 0,
          s!"goes to {t.say nm}, known to be code, in a context that code does not allow",
          w.1⟩ ::
          w.2
    | _ =>
      [⟨from_, (path.head?.map (·.addr)).getD 0, s!"goes to {t.say nm}, not known to be code",
        ["a return or a jump through a value: the value must be known to be code wanting a " ++
            "family the context is a member of",
          "on the machine: control could go anywhere"]⟩]
  | path, _, .step i Γ next k rest =>
    rest.faults pg ent justify whyJ labels from_ nm fuel (⟨stepAddr pg i next, i, Γ⟩ :: path)
      (k + 1)
  | path, _, .sys k rest => rest.faults pg ent justify whyJ labels from_ nm fuel path (k + 2)
  | path, _, .sys2 k a b =>
    a.faults pg ent justify whyJ labels from_ nm fuel path (k + 2) ++
      b.faults pg ent justify whyJ labels from_ nm fuel path (k + 2)
  | _, _, .ends => []
  | _, _, .vacuous => []
  | path, k, .branch c fl taken fall =>
    (if fl.decides c then []
     else [⟨from_, (path.head?.map (·.addr)).getD 0, "branches on flags that are not defined",
       ["on the machine: either way might be taken"]⟩]) ++
      taken.faults pg ent justify whyJ labels from_ nm fuel path k ++
      fall.faults pg ent justify whyJ labels from_ nm fuel path k

/-- **Why an address is not code wanting a family**, as `justifyF` judges
it, in at most so many goes: the faults of the walk from there, started at
a member of the family at names of its own. -/
def justifyWhy (pg : Prog) (labels : List Label) (stops : BitVec 64 → Bool) (fuelW : Nat) :
    Nat → Names → Nat → BitVec 64 → CtxS → List Refusal
  | 0, _, _, a, _ => [⟨a, a, "the code here was not looked into: too deep", []⟩]
  | f + 1, outer, k, a, E =>
    if !(E.under k && ((E.open (freshOpening k)).addKnown pg.statics).under (k + E.width)) then
      [⟨a, a, "what is wanted of the code here mentions a name it may not", []⟩]
    else
      match labels.find? fun l => l.addr == a with
      | some l =>
        let w := closeWhy (⟨k, E.width, a⟩ :: outer) (sameBy pg.fns pg.laws) (entF fuelW)
          (justifyF pg labels stops fuelW f)
          (justifyWhy pg labels stops fuelW f (⟨k, E.width, a⟩ :: outer)) [] l.pat
          ((E.open (freshOpening k)).addKnown pg.statics) (k + E.width)
        ⟨a, a, "the code here is a label, wanted for a family the label does not allow", w.1⟩ ::
          w.2
      | none =>
        let W := walk pg stops true fuelW (k + E.width) a
          (evalFor pg.fns ((E.open (freshOpening k)).addKnown pg.statics) (k + E.width))
        (if W.moved then []
         else
           let w := stepWhy (⟨k, E.width, a⟩ :: outer) pg []
             (evalFor pg.fns ((E.open (freshOpening k)).addKnown pg.statics) (k + E.width))
             (k + E.width) a
           [⟨a, a, w.1, w.2⟩]) ++
          W.faults pg (entF fuelW) (justifyF pg labels stops fuelW f)
            (justifyWhy pg labels stops fuelW f (⟨k, E.width, a⟩ :: outer)) labels a
            (⟨k, E.width, a⟩ :: outer) fuelW [] (k + E.width)

/-- **Why a program is refused**: for each label, where its walk stops
short, and what was missing there; and the same of the code each call
returns to. Nothing, where `checkProgram` accepts. -/
def explain (pg : Prog) (labels : List Label) (fuel : Nat) (k : Nat := 0) : List Refusal :=
  labels.flatMap fun l =>
    if !(l.pat.under k && ((l.start k).addKnown pg.statics).under (k + l.pat.width)) then
      [⟨l.addr, l.addr, "the label mentions a name it may not", []⟩]
    else
      let Γs := evalFor pg.fns ((l.start k).addKnown pg.statics) (k + l.pat.width)
      let stops := fun a => labels.any fun l' => l'.addr == a
      let W := walk pg stops true fuel (k + l.pat.width) l.addr Γs
      if W.moved then
        W.faults pg (entF fuel) (justifyF pg labels stops fuel fuel)
          (justifyWhy pg labels stops fuel fuel [⟨k, l.pat.width, l.addr⟩]) labels l.addr
          [⟨k, l.pat.width, l.addr⟩] fuel [] (k + l.pat.width)
      else
        let w := stepWhy [⟨k, l.pat.width, l.addr⟩] pg [] Γs (k + l.pat.width) l.addr
        [⟨l.addr, l.addr, w.1, w.2⟩]

/-- The same, to be read. -/
def explainText (pg : Prog) (labels : List Label) (fuel : Nat) : String :=
  match explain pg labels fuel with
  | [] => "nothing is refused"
  | fs => "\n".intercalate ((tidy [] fs).map (Refusal.text pg))

end TypedAsm.U
