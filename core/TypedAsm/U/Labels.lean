import TypedAsm.U.Walk
import TypedAsm.U.Subst
import TypedAsm.U.RegardS

/-!
# A program's labels

Each label of a program is an address and a context written for any values
of its names. A walk from one label that reaches another has there some
context of its own; terms are found for the other label's names, and it is
decided whether the context reached may be regarded as that label's with
those terms put in. How the terms are found is no part of what is proved:
only the deciding is.

A program each of whose labels walks to labels, or to the program's end,
with nothing left to be shown, is typed at every label for any number of
steps.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-! ## Finding terms for a label's names -/

def Inst.ofLists (vs : List (Nat × Val)) (fs : List (Nat × FlagsT)) (ts : List (Nat × TyS)) :
    Inst where
  val j := (vs.lookup j).getD (.lit 0)
  flags j := (fs.lookup j).getD (.lit Flags.unknown)
  ty j := (ts.lookup j).getD .any

/-- The term a name must be given for a pattern to be a value: the value,
where the pattern is the name; the value less a number, where the pattern is
the name and that number more. -/
def bindVal (pat got : Val) : List (Nat × Val) :=
  match pat with
  | .var j => [(j, got)]
  | .add (.var j) (.lit c) => [(j, .add got (.lit (-c)))]
  | _ => []

def bindSlots (ps gs : List (Nat × Val)) : List (Nat × Val) :=
  ps.flatMap fun p =>
    match gs.lookup p.1 with
    | some g => bindVal p.2 g
    | none => []

mutual

def bindTy : TyS → TyS → List (Nat × TyS)
  | .atom i, τ => [(i, τ)]
  | .nullable p, .nullable τ => bindTy p τ
  | .orErr p, .orErr τ => bindTy p τ
  | .ptr (.mk _ ps) _ _, .ptr (.mk _ ts) _ _ => bindVals ps ts
  | _, _ => []

def bindVals : ValsS → ValsS → List (Nat × TyS)
  | .cons _ p ps, .cons _ τ ts => bindTy p τ ++ bindVals ps ts
  | _, _ => []

end

/-- **Terms for a label's names**, read off the context reached: from the
registers, then from the regions at the addresses those give, then from
what is known of the values those give. -/
def matchCtx (Δ Γ : CtxS) : Inst :=
  let vs₁ := allRegs.flatMap fun r => bindVal (Δ.regs.get r) (Γ.regs.get r)
  let σ₁ := Inst.ofLists vs₁ [] []
  let vs₂ := Δ.held.flatMap fun d =>
    match Γ.held.find? fun g => g.1.same (d.1.subst σ₁) with
    | some g => bindSlots d.2.slots g.2.slots
    | none => []
  let vs := vs₁ ++ vs₂
  let fs : List (Nat × FlagsT) :=
    match Δ.flags with
    | .var j => [(j, Γ.flags)]
    | _ => []
  let σ₂ := Inst.ofLists vs fs []
  let ts := Δ.known.flatMap fun f =>
    match Γ.known.find? fun g => g.1.same (f.1.subst σ₂) with
    | some g => bindTy f.2 g.2
    | none => []
  Inst.ofLists vs fs ts

/-! ## A walk that leaves nothing to be shown -/

/-- Whether a walk leaves nothing to be shown: every instruction it stepped
over is seen not to fault of itself, every jump is decided, and every way
through it ends the program or stops at a label in a context that may be
regarded as the label's. -/
def Walk.closes (labels : List (BitVec 64 × CtxS)) : Walk → Bool
  | .stop a Γ =>
    match labels.find? fun e => e.1 == a with
    | some e => regardS Γ (e.2.subst (matchCtx e.2 Γ))
    | none => false
  | .arrive _ _ => false
  | .step i Γ _ _ rest => guardS i Γ.flags && rest.closes labels
  | .sys _ rest => rest.closes labels
  | .ends => true
  | .branch c Γ taken fall => Γ.flags.decides c && taken.closes labels && fall.closes labels

/-- Such a walk holds, where the code at each label is typed in the label's
context whatever its names stand for. -/
theorem Walk.holds_of_closes {n : Nat} {labels : List (BitVec 64 × CtxS)}
    (H : ∀ e ∈ labels, ∀ ρ', Ok fetch sys Ψ n e.1 (e.2.den ρ')) :
    (W : Walk) → (ρ : Env) → W.closes labels = true →
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ
  | .stop a Γ, ρ, h => by
    unfold Walk.closes at h
    cases hfind : labels.find? fun e => e.1 == a with
    | none => rw [hfind] at h; cases h
    | some e =>
      rw [hfind] at h
      have hmem := List.mem_of_find?_eq_some hfind
      have ha : e.1 = a := by simpa using List.find?_some hfind
      have hok := H e hmem (ρ.inst (matchCtx e.2 Γ))
      rw [← CtxS.den_subst, ha] at hok
      exact Ok.regard (regardS_sound ρ h) hok
  | .arrive _ _, _, h => nomatch h
  | .step i Γ next k rest, ρ, h => by
    simp only [Walk.closes, Bool.and_eq_true] at h
    exact ⟨fun d hd x => guardS_den ρ h.1 hd _ _ _ _,
      fun x => Walk.holds_of_closes H rest _ h.2⟩
  | .sys k rest, ρ, h => fun x => Walk.holds_of_closes H rest _ h
  | .ends, _, _ => trivial
  | .branch c Γ taken fall, ρ, h => by
    simp only [Walk.closes, Bool.and_eq_true] at h
    exact ⟨FlagsT.decides_den ρ Γ.flags c h.1.1, fun _ => Walk.holds_of_closes H taken ρ h.1.2,
      fun _ => Walk.holds_of_closes H fall ρ h.2⟩

/-- A walk in a program with no labels: every way through ends the program. -/
def Walk.auto (W : Walk) : Bool := W.closes []

theorem Walk.holds_of_auto {n : Nat} (W : Walk) (ρ : Env) (h : W.auto = true) :
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ :=
  Walk.holds_of_closes (fun _ hm => (List.not_mem_nil hm).elim) W ρ h

/-! ## A program -/

/-- **Whether a program is typed**: from each label, the walk gets
somewhere and leaves nothing to be shown. `k` is a number above every name
the labels use. -/
def checkProgram (code : List (BitVec 64 × Instr × BitVec 64)) (labels : List (BitVec 64 × CtxS))
    (fuel k : Nat) : Bool :=
  labels.all fun e =>
    e.2.under k &&
      (let W := walk code (fun a => labels.any fun e' => e'.1 == a) true fuel k e.1 e.2
       W.moved && W.closes labels)

/-- **A program that checks is typed at every label, for any number of
steps, whatever the labels' names stand for**: on any machine that fetches
its instructions at their addresses, under any system that does what Linux
is described to do. -/
theorem program_ok {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {code : List (BitVec 64 × Instr × BitVec 64)}
    {labels : List (BitVec 64 × CtxS)} {fuel k : Nat}
    (hcode : ∀ e ∈ code, fetch e.1 = some (e.2.1, e.2.2))
    (h : checkProgram code labels fuel k = true) :
    ∀ n, ∀ e ∈ labels, ∀ ρ, Ok fetch sys Ψ n e.1 (e.2.den ρ) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ => Ok.zero _ _
  | succ n ih =>
    intro e he ρ
    unfold checkProgram at h
    have := List.all_eq_true.mp h e he
    simp only [Bool.and_eq_true] at this
    obtain ⟨hu, hm, hc⟩ := this
    exact (walk_sound hD hkind hpre code _ hcode true fuel k e.1 e.2 ρ hu
      (Walk.holds_of_closes ih _ ρ hc)).2 hm

end TypedAsm.U
