import TypedAsm.U.Walk
import TypedAsm.U.Subst
import TypedAsm.U.JoinS

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

/-- The first region of a list that an extent lies within: its place,
counted from `i`, how far in the extent starts, and the region. -/
def hostExtent (base : Val) (size : Nat) : List (Val × HeldS) → Nat → Option (Nat × Nat × HeldS)
  | [], _ => none
  | g :: gs, i =>
    match offsetFrom base g.1 with
    | some o => if o + size ≤ g.2.size then some (i, o, g.2) else hostExtent base size gs (i + 1)
    | none => hostExtent base size gs (i + 1)

/-- Terms for the names a label's registers are. -/
def regInst (Δ Γ : CtxS) : List (Nat × Val) :=
  allRegs.flatMap fun r => bindVal (Δ.regs.get r) (Γ.regs.get r)

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
  let vs₁ := regInst Δ Γ
  let σ₁ := Inst.ofLists vs₁ [] []
  let vs₂ := Δ.held.flatMap fun d =>
    match hostExtent (d.1.subst σ₁) d.2.size Γ.held 0 with
    | some (_, o, G) =>
      d.2.slots.flatMap fun p =>
        match G.slots.lookup (o + p.1) with
        | some g => bindVal p.2 g
        | none => []
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

/-! ## Naming what the context reached does not say -/

/-- The bytes a label says hold a value and the context reached says
nothing of: in which region, and where. -/
def wanted (Δ Γ : CtxS) : List (Nat × Nat) :=
  let σ₁ := Inst.ofLists (regInst Δ Γ) [] []
  Δ.held.flatMap fun d =>
    match hostExtent (d.1.subst σ₁) d.2.size Γ.held 0 with
    | some (i, o, G) =>
      d.2.slots.filterMap fun p =>
        if G.slots.any fun q => q.1 == o + p.1 then none else some (i, o + p.1)
    | none => []

/-- A context with a region it holds said to hold, at eight of its bytes,
the value the name `k` stands for. -/
def CtxS.nameSlot (Γ : CtxS) (i o k : Nat) : Option CtxS :=
  match Γ.held[i]? with
  | some (b, S) =>
    if o + 8 ≤ S.size then some { Γ with held := Γ.held.set i (b, ⟨S.size, (o, .var k) :: S.slots⟩) }
    else none
  | none => none

theorem CtxS.nameSlot_ok {n : Nat} {a : BitVec 64} {Γ Γ' : CtxS} {i o k : Nat}
    (h : Γ.nameSlot i o k = some Γ') (hu : Γ.under k = true) (ρ : Env)
    (hok : ∀ x, Ok fetch sys Ψ n a (Γ'.den (ρ.setVal k x))) : Ok fetch sys Ψ n a (Γ.den ρ) := by
  unfold CtxS.nameSlot at h
  cases hi : Γ.held[i]? with
  | none => rw [hi] at h; cases h
  | some bS =>
    obtain ⟨b, S⟩ := bS
    rw [hi] at h
    simp only at h
    split at h
    · next ho =>
      cases h
      refine Ok.nameSlot (S := S.den ρ) (CtxS.held_den ρ Γ hi) ho fun x => ?_
      have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
      have hb : (b.den (ρ.setVal k x), S.den (ρ.setVal k x)) = (b.den ρ, S.den ρ) := by
        have h1 := CtxS.held_den (ρ.setVal k x) Γ hi
        rw [hΓ, CtxS.held_den ρ Γ hi] at h1
        exact (Option.some.inj h1).symm
      have e : CtxS.den (ρ.setVal k x)
            { Γ with held := Γ.held.set i (b, ⟨S.size, (o, .var k) :: S.slots⟩) }
          = { Γ.den ρ with
              held := (Γ.den ρ).held.set i (b.den ρ, ⟨S.size, (o, x) :: (S.den ρ).vals⟩) } := by
        refine ctx_ext
          (congrArg CtxOf.val hΓ : (Γ.den (ρ.setVal k x)).val = (Γ.den ρ).val)
          (congrArg CtxOf.flags hΓ : (Γ.den (ρ.setVal k x)).flags = (Γ.den ρ).flags) ?_
          (congrArg CtxOf.known hΓ : (Γ.den (ρ.setVal k x)).known = (Γ.den ρ).known)
        show (Γ.held.set i (b, ⟨S.size, (o, .var k) :: S.slots⟩)).map _ = _
        rw [List.map_set, ← congrArg CtxOf.held hΓ]
        congr 1
        show (b.den (ρ.setVal k x), (⟨S.size, (o, (ρ.setVal k x).val k) ::
          S.slots.map fun p => (p.1, p.2.den (ρ.setVal k x))⟩ : Held)) = _
        rw [Env.setVal_get_self, (Prod.mk.inj hb).1]
        have hS : (S.den (ρ.setVal k x)).vals = (S.den ρ).vals := congrArg ShapeOf.vals (Prod.mk.inj hb).2
        show (_, (⟨S.size, (o, x) :: (S.den (ρ.setVal k x)).vals⟩ : Held)) = _
        rw [hS]
      have h2 := hok x
      rw [e] at h2
      exact h2
    · cases h

/-- The same, of each of a list of places, with a new name for each. -/
def nameSlots (Γ : CtxS) : List (Nat × Nat) → Nat → Option CtxS
  | [], _ => some Γ
  | w :: ws, k =>
    match Γ.nameSlot w.1 w.2 k with
    | some Γ' => if Γ'.under (k + 1) then nameSlots Γ' ws (k + 1) else none
    | none => none

theorem nameSlots_ok {n : Nat} {a : BitVec 64} :
    (ws : List (Nat × Nat)) → (Γ Γ' : CtxS) → (k : Nat) → nameSlots Γ ws k = some Γ' →
    Γ.under k = true → (∀ ρ', Ok fetch sys Ψ n a (Γ'.den ρ')) →
    ∀ ρ, Ok fetch sys Ψ n a (Γ.den ρ)
  | [], Γ, Γ', _, h, _, hok, ρ => by cases h; exact hok ρ
  | w :: ws, Γ, Γ', k, h, hu, hok, ρ => by
    unfold nameSlots at h
    cases h1 : Γ.nameSlot w.1 w.2 k with
    | none => rw [h1] at h; cases h
    | some Γ₁ =>
      rw [h1] at h
      simp only at h
      split at h
      · next hu₁ =>
        exact CtxS.nameSlot_ok h1 hu ρ fun x =>
          nameSlots_ok ws Γ₁ Γ' (k + 1) h hu₁ hok _
      · cases h

/-! ## A walk that leaves nothing to be shown -/

/-- Whether a walk leaves nothing to be shown: every instruction it stepped
over is seen not to fault of itself, every jump is decided, and every way
through it ends the program or stops at a label in a context that may be
regarded as the label's, once the regions it holds end to end are taken
as one and the values the label names and the context does not are named. `k` is a name no term of the walk yet mentions. -/
def Walk.closes (labels : List (BitVec 64 × CtxS)) : Nat → Walk → Bool
  | k, .stop a Γ =>
    match labels.find? fun e => e.1 == a with
    | some e =>
      (joinAll Γ.held.length Γ).under k &&
        (match nameSlots (joinAll Γ.held.length Γ) (wanted e.2 (joinAll Γ.held.length Γ)) k with
         | some Γ' => regardS Γ' (e.2.subst (matchCtx e.2 Γ'))
         | none => false)
    | none => false
  | _, .arrive _ _ => false
  | _, .step i Γ _ k rest => guardS i Γ.flags && rest.closes labels (k + 1)
  | _, .sys k rest => rest.closes labels (k + 1)
  | _, .ends => true
  | k, .branch c Γ taken fall =>
    Γ.flags.decides c && taken.closes labels k && fall.closes labels k

/-- Such a walk holds, where the code at each label is typed in the label's
context whatever its names stand for. -/
theorem Walk.holds_of_closes {n : Nat} {labels : List (BitVec 64 × CtxS)}
    (H : ∀ e ∈ labels, ∀ ρ', Ok fetch sys Ψ n e.1 (e.2.den ρ')) :
    (W : Walk) → (k : Nat) → (ρ : Env) → W.closes labels k = true →
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ
  | .stop a Γ, k, ρ, h => by
    unfold Walk.closes at h
    cases hfind : labels.find? fun e => e.1 == a with
    | none => rw [hfind] at h; cases h
    | some e =>
      rw [hfind] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hu, h⟩ := h
      have hmem := List.mem_of_find?_eq_some hfind
      have ha : e.1 = a := by simpa using List.find?_some hfind
      cases hn : nameSlots (joinAll Γ.held.length Γ) (wanted e.2 (joinAll Γ.held.length Γ)) k with
      | none => rw [hn] at h; cases h
      | some Γ' =>
        rw [hn] at h
        refine Ok.regard (joinAll_regards ρ Γ.held.length Γ) ?_
        refine nameSlots_ok _ _ Γ' k hn hu (fun ρ' => ?_) ρ
        have hok := H e hmem (ρ'.inst (matchCtx e.2 Γ'))
        rw [← CtxS.den_subst, ha] at hok
        exact Ok.regard (regardS_sound ρ' h) hok
  | .arrive _ _, _, _, h => nomatch h
  | .step i Γ next k rest, _, ρ, h => by
    simp only [Walk.closes, Bool.and_eq_true] at h
    exact ⟨fun d hd x => guardS_den ρ h.1 hd _ _ _ _,
      fun x => Walk.holds_of_closes H rest _ _ h.2⟩
  | .sys k rest, _, ρ, h => fun x => Walk.holds_of_closes H rest _ _ h
  | .ends, _, _, _ => trivial
  | .branch c Γ taken fall, k, ρ, h => by
    simp only [Walk.closes, Bool.and_eq_true] at h
    exact ⟨FlagsT.decides_den ρ Γ.flags c h.1.1, fun _ => Walk.holds_of_closes H taken k ρ h.1.2,
      fun _ => Walk.holds_of_closes H fall k ρ h.2⟩

/-- A walk in a program with no labels: every way through ends the program. -/
def Walk.auto (W : Walk) : Bool := W.closes [] 0

theorem Walk.holds_of_auto {n : Nat} (W : Walk) (ρ : Env) (h : W.auto = true) :
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ :=
  Walk.holds_of_closes (fun _ hm => (List.not_mem_nil hm).elim) W 0 ρ h

/-! ## A program -/

/-- **Whether a program is typed**: from each label, the walk gets
somewhere and leaves nothing to be shown. `k` is a number above every name
the labels use. -/
def checkProgram (code : List (BitVec 64 × Instr × BitVec 64)) (labels : List (BitVec 64 × CtxS))
    (fuel k : Nat) : Bool :=
  labels.all fun e =>
    e.2.under k &&
      (let W := walk code (fun a => labels.any fun e' => e'.1 == a) true fuel k e.1 e.2
       W.moved && W.closes labels k)

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
      (Walk.holds_of_closes ih _ k ρ hc)).2 hm

end TypedAsm.U
