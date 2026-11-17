import TypedAsm.U.Labels

/-!
# Why a program is refused

Where a check fails, the places its walks stop short, and what was missing
at each. This proves nothing and nothing rests on it: it is for the person
writing the labels.
-/

namespace TypedAsm.U

open TypedAsm

/-- A place a walk stopped short, and why. -/
structure Fault where
  /-- The label the walk started from. -/
  label : BitVec 64
  /-- Where it stopped. -/
  addr : BitVec 64
  why : String
  deriving Repr

/-- The places a walk stops short: as `Walk.closes` judges it, with the
reason kept. -/
def Walk.faults (cc : CtxS → CtxS → Nat → Option (CtxS × OpenL)) (labels : List Label)
    (from_ : BitVec 64) : Nat → Walk → List Fault
  | k, .stop a Γ =>
    match labels.find? fun l => l.addr == a with
    | some l =>
      if (cc l.pat Γ k).isSome then []
      else [⟨from_, a, "arrives at a label in a context the label does not allow"⟩]
    | none => [⟨from_, a, "the instruction here is not typed in the context reached"⟩]
  | k, .arrive t Γ =>
    match Γ.known.find? fun f => f.1.same t && f.2.isCode with
    | some (tv, .code regs flags held known rest) =>
      if tv.under k &&
          (match cc (codeCtx regs flags held known rest) Γ k with
           | some (Γ', _) => Γ'.known.contains (tv, .code regs flags held known rest)
           | none => false) then []
      else [⟨from_, 0, "goes to a value known to be code, in a context that code does not allow"⟩]
    | _ => [⟨from_, 0, "goes to a value not known to be code"⟩]
  | _, .step _ _ _ k rest => rest.faults cc labels from_ (k + 1)
  | _, .sys k rest => rest.faults cc labels from_ (k + 1)
  | _, .sys2 k a b => a.faults cc labels from_ (k + 1) ++ b.faults cc labels from_ (k + 1)
  | _, .ends => []
  | _, .vacuous => []
  | k, .branch c fl taken fall =>
    (if fl.decides c then [] else [⟨from_, 0, "branches on flags that are not defined"⟩]) ++
      taken.faults cc labels from_ k ++ fall.faults cc labels from_ k

/-- **Why a program is refused**: for each label, where its walk stops
short. Nothing, where `checkProgram` accepts. -/
def explain (pg : Prog) (labels : List Label) (fuel : Nat) (k : Nat := 0) : List Fault :=
  labels.flatMap fun l =>
    if !(l.pat.under k && ((l.start k).addKnown pg.statics).under (k + l.pat.width)) then
      [⟨l.addr, l.addr, "the label mentions a name it may not"⟩]
    else
      let W := walk pg (fun a => labels.any fun l' => l'.addr == a) true fuel (k + l.pat.width)
        l.addr (evalFor pg.fns ((l.start k).addKnown pg.statics) (k + l.pat.width))
      (if W.moved then [] else [⟨l.addr, l.addr, "the walk does not leave the label"⟩]) ++
        W.faults (closeCtx (sameBy pg.fns pg.laws) (entF fuel) (justifyF pg labels
          (fun a => labels.any fun l' => l'.addr == a) fuel fuel)) labels l.addr (k + l.pat.width)

end TypedAsm.U
