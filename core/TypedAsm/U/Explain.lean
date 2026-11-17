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

/-- A term, to be read. In a walk from a label the names below sixteen are
what the registers held at the label. -/
def Val.say : Val → String
  | .lit v => litSay v
  | .var i =>
    match allRegs[i]? with
    | some r => s!"({r.name64} at the label)"
    | none => s!"(value {i})"
  | .bvar d i =>
    match d, allRegs[i]? with
    | 0, some r => s!"({r.name64} of the label's family)"
    | _, _ => s!"(value {i} of the family {d} out)"
  | .slot _ => "(an operand)"
  | .un (.shl k) a => s!"({a.say} << {k})"
  | .un (.neg _) a => s!"-{a.say}"
  | .un _ a => s!"f({a.say})"
  | .bin .add a b => s!"({a.say} + {b.say})"
  | .bin (.imul _) a b => s!"({a.say} * {b.say})"
  | .bin _ a b => s!"f({a.say}, {b.say})"
  | .tri _ a b c => s!"f({a.say}, {b.say}, {c.say})"
  | .fop _ _ a b => s!"f({a.say}, {b.say})"
  | .app f a b => s!"fn{f}({a.say}, {b.say})"

/-- What is known of a value, to be read, in brief. -/
def TyS.say : TyS → String
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
  | .arr c _ => s!"the address of {c.say} values in a row"
  | .upTo t strict => (if strict then "below " else "at most ") ++ t.say

/-- A region held, to be read. -/
def regionSay (g : Val × HeldS) : String :=
  s!"{g.2.size.say} bytes at {g.1.say}" ++
    (if g.2.slots.isEmpty then ""
     else " holding " ++ ", ".intercalate (g.2.slots.map fun p => s!"{p.2.say} at {p.1.say}"))

def addrSay (a : BitVec 64) : String := "0x" ++ String.ofList (Nat.toDigits 16 a.toNat)

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
def regSay (path : List Was) (Γ : CtxS) (r : Reg) : String :=
  s!"{r.name64} holds {(Γ.regs.get r).say}, {gave path Γ r}"

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

/-- A fault, to be read. -/
def Refusal.text (f : Refusal) : String :=
  s!"walking from {addrSay f.label}, at {addrSay f.addr}: {f.why}" ++
    String.join (f.detail.map fun d => "\n    " ++ d)

/-! ## Why a context may not be regarded as another -/

/-- **Each thing a context wanted asks that the context reached does not
give**: register by register, region by region, fact by fact; by the same
comparison the check makes. -/
def regardWhy (sm : List (Val × TyS) → Val → Val → Bool) (ent : TyS → TyS → Bool)
    (path : List Was) (Γ Δ : CtxS) : List String :=
  (allRegs.filterMap fun r =>
    if sm Γ.known (Γ.regs.get r) (Δ.regs.get r) then none
    else some s!"{regSay path Γ r}; wanted there: {(Δ.regs.get r).say}") ++
  (if Γ.flags == Δ.flags then [] else ["the flags are not the ones wanted"]) ++
  (match partsS sm Γ.known Γ.held Δ.held with
   | none =>
     (Δ.held.filterMap fun d =>
       if (hostOf sm Γ.known d Γ.held).isSome then none
       else some s!"wanted held: {regionSay d}; not found in what is held") ++
     ["what is held: " ++ "; ".intercalate (Γ.held.map regionSay)]
   | some P =>
     (if apartS Γ.known P then [] else ["two regions wanted overlap in what is held"]) ++
     (if coverS Γ.held P then []
      else ["more is held than is wanted, and what is wanted does not range over the rest: " ++
        "; ".intercalate (Γ.held.map regionSay)])) ++
  (Δ.known.filterMap fun f =>
    if factFrom ent Γ.known f then none
    else
      match f.1.lit?, f.2 with
      | some a, .code .. =>
        some s!"the code at {addrSay a} is not typed for what is wanted of it: why, follows"
      | _, _ => some s!"wanted known of {f.1.say}: {f.2.say}; not shown by what is known") ++
  (if Δ.rest == Γ.rest then [] else ["what else is held is not what is wanted"])

/-- **Why a context reached may not be made a member of a family**: as the
check makes it ready, and then each thing wanted that is not so. Where the
family wants code at an address typed, a return address say, and it is
not, `whyJ` says why: the faults of the walk from there. -/
def closeWhy (sm : List (Val × TyS) → Val → Val → Bool) (ent : Nat → TyS → TyS → Bool)
    (justify : Nat → BitVec 64 → CtxS → Bool) (whyJ : Nat → BitVec 64 → CtxS → List Refusal)
    (path : List Was) (P Γ : CtxS) (k : Nat) : List String × List Refusal :=
  if !(joinAll Γ.held.length Γ).under k then
    (["the context reached mentions a name it may not"], [])
  else
    match nameSlots (joinAll Γ.held.length Γ) (wantedCode P (joinAll Γ.held.length Γ)) k with
    | none => (["a value the family names lies outside what is held, or is not placed"], [])
    | some Γ' =>
      let kn := k + (wantedCode P (joinAll Γ.held.length Γ)).length
      let Δ := P.open (matchOpen P Γ').opening
      ((if (matchOpen P Γ').closed then []
        else ["the member of the family could not be read off the context reached"]) ++
        regardWhy sm (ent kn) path (Γ'.addKnown (learnedFacts justify kn Γ' Δ)) Δ,
       (askedCode Γ' Δ).flatMap fun x =>
         if justify kn x.1 (x.2.1.addKnown (carried Γ')) then []
         else whyJ kn x.1 (x.2.1.addKnown (carried Γ')))

/-! ## Why an instruction is not typed -/

/-- **Why the instruction at an address is not stepped over**, in a
context: what it would need, and what the machine could do there. -/
def stepWhy (pg : Prog) (path : List Was) (Γ : CtxS) (k : Nat) (a : BitVec 64) :
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
            regSay path Γ .rax, regSay path Γ .rdi, regSay path Γ .rsi, regSay path Γ .rdx])
      else
        match Γ.regs.rax.lit? with
        | none =>
          ("which system call this is, is not a number written out",
            [regSay path Γ .rax,
              "on the machine: any call might be made, with whatever the registers hold"])
        | some nr =>
          match linuxKind nr with
          | none =>
            (s!"system call {nr.toNat} is not one the model of the kernel has", [])
          | some (.fills b room) =>
            (s!"system call {nr.toNat} stores bytes at the address in {b.name64}",
              [regSay path Γ b,
                match room with
                | .inl r => "as many as: " ++ regSay path Γ r
                | .inr n => s!"as many as {n}",
                "they are not shown to lie in memory the code holds, or in a block that may " ++
                  "be written and holds no typed value there",
                "on the machine: the kernel could write over memory the program relies on"])
          | some .map =>
            ("memory is asked for in a form the model of the kernel does not have",
              ["wanted: rdi nought, rsi a number written out, rdx 3, r10 0x22",
                regSay path Γ .rdi, regSay path Γ .rsi, regSay path Γ .rdx, regSay path Γ .r10])
          | some .unmap =>
            ("memory is given back that is not held whole",
              ["wanted: a region held at the address in rdi, of as many whole pages as rsi says",
                regSay path Γ .rdi, regSay path Γ .rsi,
                "what is held: " ++ "; ".intercalate (Γ.held.map regionSay),
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
               [s!"{n} bytes at {(eaS Γ.regs (a + len) m).say}"] ++
                 (memRegs m).map (regSay path Γ)
             | none => []) ++
            ["wanted: bytes of a region the code holds, of a block a value is known to point " ++
                "into, of text, or of a row of values",
              "what is held: " ++ "; ".intercalate (Γ.held.map regionSay),
              "on the machine: it could read memory the program does not have, and fault"])
        | some (cell, extra) =>
          let Γ₁ : CtxS := { Γ with known := extra ++ Γ.known }
          let σ := fillOf Γ s.srcs (a + len) (eaTerm Γ (a + len) s.ea) cell
          if !s.guard.okS Γ₁ Γ.flags (s.ga.fillN σ) (s.gb.fillN σ) (s.gc.fillN σ) then
            (s!"`{i.toAsm}` may fault of itself",
              ["a divisor not shown to be other than nought, or a quotient not shown to fit",
                s!"of: {(s.ga.fillN σ).say}, {(s.gb.fillN σ).say}, {(s.gc.fillN σ).say}",
                "on the machine: a divide error"])
          else
            match writeAny pg.kinds Γ₁ (a + len) (s.store.fillN σ) s.wr with
            | none =>
              (s!"`{i.toAsm}` writes memory that is not shown to be the program's to write",
                (match s.wr with
                 | some (m, n) =>
                   [s!"{n} bytes at {(eaS Γ.regs (a + len) m).say}"] ++
                     (memRegs m).map (regSay path Γ)
                 | none => []) ++
                ["wanted: bytes of a region the code holds, or of a block that may be " ++
                    "written, where what is stored is of the type the block says",
                  "what is held: " ++ "; ".intercalate (Γ.held.map regionSay),
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
    (labels : List Label) (from_ : BitVec 64) : List Was → Nat → Walk → List Refusal
  | path, k, .stop a Γ =>
    match labels.find? fun l => l.addr == a with
    | some l =>
      if (closeCtx (sameBy pg.fns pg.laws) ent justify l.pat Γ k).isSome then []
      else
        let w := closeWhy (sameBy pg.fns pg.laws) ent justify whyJ path l.pat Γ k
        ⟨from_, a, "arrives at a label in a context the label does not allow", w.1⟩ :: w.2
    | none =>
      let w := stepWhy pg path Γ k a
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
        let w := closeWhy (sameBy pg.fns pg.laws) ent justify whyJ path
          (codeCtx regs flags held known rest) Γ k
        ⟨from_, (path.head?.map (·.addr)).getD 0,
          s!"goes to {t.say}, known to be code, in a context that code does not allow", w.1⟩ ::
          w.2
    | _ =>
      [⟨from_, (path.head?.map (·.addr)).getD 0, s!"goes to {t.say}, not known to be code",
        ["a return or a jump through a value: the value must be known to be code wanting a " ++
            "family the context is a member of",
          "on the machine: control could go anywhere"]⟩]
  | path, _, .step i Γ next k rest =>
    rest.faults pg ent justify whyJ labels from_ (⟨stepAddr pg i next, i, Γ⟩ :: path) (k + 1)
  | path, _, .sys k rest => rest.faults pg ent justify whyJ labels from_ path (k + 2)
  | path, _, .sys2 k a b =>
    a.faults pg ent justify whyJ labels from_ path (k + 2) ++
      b.faults pg ent justify whyJ labels from_ path (k + 2)
  | _, _, .ends => []
  | _, _, .vacuous => []
  | path, k, .branch c fl taken fall =>
    (if fl.decides c then []
     else [⟨from_, (path.head?.map (·.addr)).getD 0, "branches on flags that are not defined",
       ["on the machine: either way might be taken"]⟩]) ++
      taken.faults pg ent justify whyJ labels from_ path k ++
      fall.faults pg ent justify whyJ labels from_ path k

/-- **Why an address is not code wanting a family**, as `justifyF` judges
it, in at most so many goes: the faults of the walk from there, started at
a member of the family at names of its own. -/
def justifyWhy (pg : Prog) (labels : List Label) (stops : BitVec 64 → Bool) (fuelW : Nat) :
    Nat → Nat → BitVec 64 → CtxS → List Refusal
  | 0, _, a, _ => [⟨a, a, "the code here was not looked into: too deep", []⟩]
  | f + 1, k, a, E =>
    if !(E.under k && ((E.open (freshOpening k)).addKnown pg.statics).under (k + E.width)) then
      [⟨a, a, "what is wanted of the code here mentions a name it may not", []⟩]
    else
      match labels.find? fun l => l.addr == a with
      | some l =>
        let w := closeWhy (sameBy pg.fns pg.laws) (entF fuelW) (justifyF pg labels stops fuelW f)
          (justifyWhy pg labels stops fuelW f) [] l.pat
          ((E.open (freshOpening k)).addKnown pg.statics) (k + E.width)
        ⟨a, a, "the code here is a label, wanted for a family the label does not allow", w.1⟩ ::
          w.2
      | none =>
        let W := walk pg stops true fuelW (k + E.width) a
          (evalFor pg.fns ((E.open (freshOpening k)).addKnown pg.statics) (k + E.width))
        (if W.moved then []
         else
           let w := stepWhy pg [] (evalFor pg.fns ((E.open (freshOpening k)).addKnown pg.statics)
             (k + E.width)) (k + E.width) a
           [⟨a, a, w.1, w.2⟩]) ++
          W.faults pg (entF fuelW) (justifyF pg labels stops fuelW f)
            (justifyWhy pg labels stops fuelW f) labels a [] (k + E.width)

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
          (justifyWhy pg labels stops fuel fuel) labels l.addr [] (k + l.pat.width)
      else
        let w := stepWhy pg [] Γs (k + l.pat.width) l.addr
        [⟨l.addr, l.addr, w.1, w.2⟩]

/-- The same, to be read. -/
def explainText (pg : Prog) (labels : List Label) (fuel : Nat) : String :=
  match explain pg labels fuel with
  | [] => "nothing is refused"
  | fs => "\n".intercalate (fs.map Refusal.text)

end TypedAsm.U
