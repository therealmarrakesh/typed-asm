import TypedAsm.U.Walk
import TypedAsm.U.JoinS
import TypedAsm.U.Open

/-!
# Addresses known to be code

A label of a program, a return address, a function, a pointer to code: each
is an address known to be code wanting a family of contexts. The family is
written as a context whose terms speak of what the family ranges over: its
values, its flags, and whatever else is held.

Control comes to such an address in some context of its own. A member of
the family is looked for: its values from the registers and from the
regions at the addresses those give; and, where the family ranges over
whatever else is held, all that the context holds besides. Then it is
decided whether the context reached may be regarded as that member. How the
member is found is no part of what is proved: only the deciding is.

A program each of whose labels walks to labels, to values known to be code,
or to the program's end, with nothing left to be shown, is typed at every
label, for every member of the label's family, for any number of steps.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

theorem lookup_mem {α : Type} : (l : List (Nat × α)) → (j : Nat) → (v : α) →
    l.lookup j = some v → (j, v) ∈ l
  | [], _, _, h => nomatch h
  | (i, w) :: rest, j, v, h => by
    unfold List.lookup at h
    split at h
    · next heq =>
      cases h
      rw [beq_iff_eq.mp heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem rest j v h)

/-- The first region of a list that an extent lies within: its place,
counted from `i`, how far in the extent starts, and the region. -/
def hostExtent (base : Val) (size : Nat) : List (Val × HeldS) → Nat → Option (Nat × Nat × HeldS)
  | [], _ => none
  | g :: gs, i =>
    match offsetFrom base g.1 with
    | some o => if o + size ≤ g.2.size then some (i, o, g.2) else hostExtent base size gs (i + 1)
    | none => hostExtent base size gs (i + 1)

/-! ## Naming what the context reached does not say -/

/-- The bytes that regions wanted say hold a value and the context reached
says nothing of: in which region of the context, and where. The regions
wanted are given with their addresses as terms of the context reached. -/
def wantedHeld (held : List (Val × HeldS)) (Γ : CtxS) : List (Nat × Nat) :=
  held.flatMap fun d =>
    match hostExtent d.1 d.2.size Γ.held 0 with
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

theorem CtxS.nameSlot_ok (Q : Ctx → Prop)
    (hname : ∀ {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}, Γ.held[i]? = some (b, S) →
      ∀ {o : Nat}, o + 8 ≤ S.size →
      (∀ x, Q { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) → Q Γ)
    {Γ Γ' : CtxS} {i o k : Nat}
    (h : Γ.nameSlot i o k = some Γ') (hu : Γ.under k = true) (ρ : Env)
    (hok : ∀ x, Q (Γ'.den (ρ.setVal k x))) : Q (Γ.den ρ) := by
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
      refine hname (S := S.den ρ) (CtxS.held_den ρ Γ hi) ho fun x => ?_
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
        have hj : i < (Γ.held.map fun b =>
            (b.1.den (ρ.setVal k x), b.2.den (ρ.setVal k x))).length := by
          rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hi).1
        show (Γ.held.set i (b, ⟨S.size, (o, .var k) :: S.slots⟩)).map
              (fun b => (b.1.den (ρ.setVal k x), b.2.den (ρ.setVal k x)))
            ++ restDen (ρ.setVal k x) Γ.rest = (Γ.den ρ).held.set i _
        rw [← congrArg CtxOf.held hΓ]
        show _ = ((Γ.held.map fun b => (b.1.den (ρ.setVal k x), b.2.den (ρ.setVal k x)))
          ++ restDen (ρ.setVal k x) Γ.rest).set i _
        rw [List.set_append_left _ _ hj, List.map_set]
        congr 2
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

theorem nameSlots_ok (Q : Ctx → Prop)
    (hname : ∀ {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}, Γ.held[i]? = some (b, S) →
      ∀ {o : Nat}, o + 8 ≤ S.size →
      (∀ x, Q { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) → Q Γ) :
    (ws : List (Nat × Nat)) → (Γ Γ' : CtxS) → (k : Nat) → nameSlots Γ ws k = some Γ' →
    Γ.under k = true → (ρ : Env) →
    (∀ ρ', Env.SameBelow k ρ' ρ → Q (Γ'.den ρ')) →
    Q (Γ.den ρ)
  | [], Γ, Γ', k, h, _, ρ, hok => by cases h; exact hok ρ (Env.SameBelow.refl k ρ)
  | w :: ws, Γ, Γ', k, h, hu, ρ, hok => by
    unfold nameSlots at h
    cases h1 : Γ.nameSlot w.1 w.2 k with
    | none => rw [h1] at h; cases h
    | some Γ₁ =>
      rw [h1] at h
      simp only at h
      split at h
      · next hu₁ =>
        refine CtxS.nameSlot_ok Q hname h1 hu ρ fun x => ?_
        refine nameSlots_ok Q hname ws Γ₁ Γ' (k + 1) h hu₁ _ fun ρ' hag => ?_
        exact hok ρ' ((hag.mono (Nat.le_succ k)).trans (Env.SameBelow.setVal ρ k x))
      · cases h

/-! ## Terms for the values of a family -/

/-- The term a value of the nearest family must be given for a pattern to
be a value: the value, where the pattern is that name; the value less a
number, where the pattern is the name and that number more. -/
def bindB (pat got : Val) : List (Nat × Val) :=
  match pat with
  | .bvar 0 j => [(j, got)]
  | .add (.bvar 0 j) (.lit c) => [(j, .add got (.lit (-c)))]
  | _ => []

/-- What a member of a family is, as terms in lists. -/
structure OpenL where
  bs : List (Nat × Val) := []
  f : FlagsT := .lit Flags.unknown
  rest : List (Val × HeldS) := []
  tail : RestS := .none

def OpenL.opening (l : OpenL) : Opening :=
  { b := fun j => (l.bs.lookup j).getD (.lit 0), f := l.f, rest := l.rest, tail := l.tail }

def OpenL.closed (l : OpenL) : Bool :=
  (l.bs.all fun p => p.2.closedAt 0) && l.f.closedAt 0 && heldClosedAt 0 l.rest &&
    l.tail.closedAt 0

theorem OpenL.closed_opening {l : OpenL} (h : l.closed = true) : l.opening.Closed := by
  simp only [OpenL.closed, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hb, hf⟩, hr⟩, ht⟩ := h
  constructor
  · intro j
    show ((l.bs.lookup j).getD (.lit 0)).closedAt 0 = true
    cases hl : l.bs.lookup j with
    | none => rfl
    | some v => exact hb _ (lookup_mem _ _ _ hl)
  · exact hf
  · exact hr
  · exact ht

/-- A list of pieces of a region, by where they start. -/
def insertPiece (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertPiece x ys

def sortPieces : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: xs => insertPiece x (sortPieces xs)

/-- The stretches of a region of `size` bytes, from byte `cur` on, that
pieces listed by where they start leave out. -/
def gaps (size : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | cur, [] => if cur < size then [(cur, size - cur)] else []
  | cur, (o, n) :: rest => (if cur < o then [(cur, o - cur)] else []) ++ gaps size (o + n) rest

/-- A stretch of a region, as a region: its bytes, and the values the
region says lie wholly in it. -/
def stretch (g : Val × HeldS) (x : Nat × Nat) : Val × HeldS :=
  (.add g.1 (.lit (BitVec.ofNat 64 x.1)),
    ⟨x.2, g.2.slots.filterMap fun p =>
      if x.1 ≤ p.1 ∧ p.1 + 8 ≤ x.1 + x.2 then some (p.1 - x.1, p.2) else none⟩)

/-- Where each region wanted lies in the context reached: in which region,
how far in, and how long. -/
def placed (held : List (Val × HeldS)) (Γ : CtxS) : List (Nat × Nat × Nat) :=
  held.filterMap fun d =>
    match hostExtent d.1 d.2.size Γ.held 0 with
    | some (i, off, _) => some (i, off, d.2.size)
    | none => none

/-- **What the context reached holds besides the regions wanted**: the
stretches of each of its regions that they leave out. Where a family ranges
over whatever else is held, this is what that is. -/
def leftover (held : List (Val × HeldS)) (Γ : CtxS) : List (Val × HeldS) :=
  let ps := placed held Γ
  (List.range Γ.held.length).flatMap fun i =>
    match Γ.held[i]? with
    | some g =>
      (gaps g.2.size 0 (sortPieces ((ps.filter fun p => p.1 == i).map fun p => p.2))).map
        (stretch g)
    | none => []

/-- **A member of a family**, read off the context reached: its values from
the registers, then from the regions at the addresses those give; and,
where the family ranges over whatever else is held, all that the context
holds besides. -/
def matchOpen (P Γ : CtxS) : OpenL :=
  let bs₁ := allRegs.flatMap fun r => bindB (P.regs.get r) (Γ.regs.get r)
  let o₁ : Opening := { b := fun j => (bs₁.lookup j).getD (.lit 0), f := Γ.flags }
  let wantedRegions := P.held.map fun d => (d.1.open o₁ 0, d.2)
  let bs₂ := wantedRegions.flatMap fun d =>
    match hostExtent d.1 d.2.size Γ.held 0 with
    | some (_, off, G) =>
      d.2.slots.flatMap fun p =>
        match G.slots.lookup (off + p.1) with
        | some g => bindB p.2 g
        | none => []
    | none => []
  match P.rest with
  | .bvar 0 => ⟨bs₁ ++ bs₂, Γ.flags, leftover wantedRegions Γ, Γ.rest⟩
  | _ => ⟨bs₁ ++ bs₂, Γ.flags, [], .none⟩

/-- The bytes a family's contexts say hold a value and the context reached
says nothing of. -/
def wantedCode (P Γ : CtxS) : List (Nat × Nat) :=
  let bs₁ := allRegs.flatMap fun r => bindB (P.regs.get r) (Γ.regs.get r)
  let o₁ : Opening := { b := fun j => (bs₁.lookup j).getD (.lit 0), f := Γ.flags }
  wantedHeld (P.held.map fun d => (d.1.open o₁ 0, d.2)) Γ

/-! ## Knowing that an address is code -/

/-- `JustSound n j`: wherever `j` says an address is code wanting a family,
the code there is typed for every member of the family, for `n` steps. -/
def JustSound (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat)
    (j : Nat → BitVec 64 → CtxS → Bool) : Prop :=
  ∀ k a E, j k a E = true → ∀ (ρ : Env) (fam : Fam),
    Ok fetch sys Ψ n a (E.den { ρ with bound := fam :: ρ.bound })

/-- The things a member of a family knows of addresses written out, that
they are code, and the context reached does not: each with its address and
the family wanted there. -/
def askedCode (Γ Δ : CtxS) : List (BitVec 64 × CtxS × (Val × TyS)) :=
  Δ.known.filterMap fun f =>
    match f.1.lit?, f.2 with
    | some a, .code r fl h kn rs =>
      if Γ.known.contains f then none else some (a, codeCtx r fl h kn rs, f)
    | _, _ => none

theorem askedCode_spec {Γ Δ : CtxS} {x : BitVec 64 × CtxS × (Val × TyS)}
    (hx : x ∈ askedCode Γ Δ) :
    x.2.2.1.lit? = some x.1 ∧
      ∃ r fl h kn rs, x.2.2.2 = .code r fl h kn rs ∧ x.2.1 = codeCtx r fl h kn rs := by
  obtain ⟨f, _, hf⟩ := List.mem_filterMap.mp hx
  split at hf
  · next a r fl h kn rs hlit hty =>
    split at hf
    · cases hf
    · cases hf
      exact ⟨hlit, r, fl, h, kn, rs, hty, rfl⟩
  · cases hf

/-! ## Regarding the context reached as a member of a family -/

/-- The things a member of a family knows of addresses, that they are
code, which the context reached does not know and which are justified. -/
def learnedFacts (justify : Nat → BitVec 64 → CtxS → Bool) (kj : Nat) (Γ Δ : CtxS) :
    List (Val × TyS) :=
  ((askedCode Γ Δ).filter fun x => justify kj x.1 x.2.1).map fun x => x.2.2

/-- **The context reached, made ready to be regarded as a member of a
family**: its regions that lie end to end taken as one; the values the
family names and it does not, named; and the addresses the member knows to
be code and it does not, known to be so where that is justified. Nothing
unless it may then be regarded as the member found, which is given with it.
`k` is a name no term yet mentions. -/
def closeCtx (ent : Nat → TyS → TyS → Bool) (justify : Nat → BitVec 64 → CtxS → Bool)
    (P Γ : CtxS) (k : Nat) :
    Option (CtxS × OpenL) :=
  if (joinAll Γ.held.length Γ).under k then
    match nameSlots (joinAll Γ.held.length Γ) (wantedCode P (joinAll Γ.held.length Γ)) k with
    | some Γ' =>
      if (matchOpen P Γ').closed &&
          regardS (ent (k + (wantedCode P (joinAll Γ.held.length Γ)).length))
            (Γ'.addKnown (learnedFacts justify
              (k + (wantedCode P (joinAll Γ.held.length Γ)).length) Γ'
              (P.open (matchOpen P Γ').opening)))
            (P.open (matchOpen P Γ').opening) then
        some (Γ'.addKnown (learnedFacts justify
              (k + (wantedCode P (joinAll Γ.held.length Γ)).length) Γ'
              (P.open (matchOpen P Γ').opening)), matchOpen P Γ')
      else none
    | none => none
  else none

/-- `CloseSound n cc`: where `cc` succeeds, whatever holds of the context
made ready, given that it may be regarded as the member, holds of the
context reached: for anything that holds of a context when it holds of one
the context may be regarded as; when it holds whatever value a region holds
at bytes the context says nothing of; and when it holds with more known
that is so. -/
def CloseSound (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat)
    (cc : CtxS → CtxS → Nat → Option (CtxS × OpenL)) : Prop :=
  ∀ (Q : Ctx → Prop),
    (∀ {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}, Γ.held[i]? = some (b, S) →
      ∀ {o : Nat}, o + 8 ≤ S.size →
      (∀ x, Q { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) → Q Γ) →
    (∀ {Γ Δ : Ctx}, Regards fetch sys Ψ Γ Δ → Q Δ → Q Γ) →
    (∀ {Γ : Ctx} (fs : List Fact),
      (∀ f ∈ fs, ∀ k, k ≤ n + 1 → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → HasTy fetch sys Ψ' k f.2 f.1) →
      Q { Γ with known := fs ++ Γ.known } → Q Γ) →
    ∀ {P Γ Γ' : CtxS} {o : OpenL} {k : Nat}, cc P Γ k = some (Γ', o) → ∀ ρ : Env,
    (∀ ρ', Env.SameBelow k ρ' ρ →
      Regards fetch sys Ψ (Γ'.den ρ') (P.den { ρ' with bound := famOf ρ' o.opening :: ρ'.bound }) →
      Q (Γ'.den ρ')) →
    Q (Γ.den ρ)

theorem closeCtx_sound {n : Nat} {ent : Nat → TyS → TyS → Bool}
    (he : ∀ kf, EntSound fetch sys (ent kf)) {justify : Nat → BitVec 64 → CtxS → Bool}
    (hj : JustSound fetch sys Ψ n justify) : CloseSound fetch sys Ψ n (closeCtx ent justify) := by
  intro Q hname hreg hlearn P Γ Γ'' o k h ρ hQ
  unfold closeCtx at h
  split at h
  · next hu =>
    cases hn : nameSlots (joinAll Γ.held.length Γ)
        (wantedCode P (joinAll Γ.held.length Γ)) k with
    | none => rw [hn] at h; cases h
    | some Γ₁ =>
      rw [hn] at h
      simp only at h
      split at h
      · next hc =>
        cases h
        simp only [Bool.and_eq_true] at hc
        refine hreg (joinAll_regards ρ Γ.held.length Γ) ?_
        refine nameSlots_ok Q hname _ _ Γ₁ k hn hu ρ fun ρ' hag => ?_
        refine hlearn ((learnedFacts justify
            (k + (wantedCode P (joinAll Γ.held.length Γ)).length) Γ₁
            (P.open (matchOpen P Γ₁).opening)).map fun f => (f.1.den ρ', f.2.den ρ')) ?_ ?_
        · intro f hf k' hk' Ψ' he hwf
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
          obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
          obtain ⟨hlit, r, fl, hd, kn, rs, hty, hE⟩ := askedCode_spec hx1
          show HasTy fetch sys Ψ' k' (x.2.2.2.den ρ') (x.2.2.1.den ρ')
          rw [Val.lit?_den hlit, hty, code_den]
          refine hasTy_code_of_ok (fun z => ?_) k' hk' Ψ' he hwf
          rw [← hE]
          exact hj _ _ _ hx2 ρ' z
        · have e : CtxS.den ρ' (Γ₁.addKnown (learnedFacts justify
                (k + (wantedCode P (joinAll Γ.held.length Γ)).length) Γ₁
                (P.open (matchOpen P Γ₁).opening)))
              = { Γ₁.den ρ' with known :=
                  ((learnedFacts justify (k + (wantedCode P (joinAll Γ.held.length Γ)).length) Γ₁
                    (P.open (matchOpen P Γ₁).opening)).map fun f => (f.1.den ρ', f.2.den ρ'))
                    ++ (Γ₁.den ρ').known } :=
            ctx_ext rfl rfl rfl (List.map_append)
          rw [← e]
          refine hQ ρ' hag ?_
          rw [← CtxS.den_open ρ' _ (OpenL.closed_opening hc.1)]
          exact regardS_sound (he _) ρ' hc.2
      · cases h
  · cases h

/-! ## Families at names of their own -/

/-- A member of a family at names of its own: the `k`th and after for its
values, and the `k`th for its flags and for whatever else is held. -/
def freshOpening (k : Nat) : Opening :=
  { b := fun j => .var (k + j), f := .var k, rest := [], tail := .name k }

theorem freshOpening_closed (k : Nat) : (freshOpening k).Closed :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- A setting of the names in which those from the `k`th on stand for a
given member of a family, and those below are as they were. -/
def Env.withFam (ρ : Env) (k : Nat) (fam : Fam) : Env :=
  { ρ with
    val := fun i => if i < k then ρ.val i else fam.vals (i - k)
    flags := fun i => if i < k then ρ.flags i else fam.flags
    frame := fun i => if i < k then ρ.frame i else fam.rest }

theorem famOf_withFam (ρ : Env) (k : Nat) (fam : Fam) :
    famOf (ρ.withFam k fam) (freshOpening k) = fam := by
  have hv : (fun j => if k + j < k then ρ.val (k + j) else fam.vals (k + j - k)) = fam.vals :=
    funext fun j => by
      simp only [show ¬ k + j < k by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  show Fam.mk (fun j => if k + j < k then ρ.val (k + j) else fam.vals (k + j - k))
      (if k < k then ρ.flags k else fam.flags) ([] ++ (if k < k then ρ.frame k else fam.rest)) = fam
  rw [hv]
  simp only [Nat.lt_irrefl, ↓reduceIte, List.nil_append]

theorem sameBelow_withFam (ρ : Env) (k : Nat) (fam : Fam) :
    Env.SameBelow k (ρ.withFam k fam) ρ :=
  ⟨fun i hi => by show (if i < k then ρ.val i else _) = _; simp only [hi, ↓reduceIte],
    fun i hi => by show (if i < k then ρ.flags i else _) = _; simp only [hi, ↓reduceIte],
    fun i hi => by show (if i < k then ρ.frame i else _) = _; simp only [hi, ↓reduceIte],
    rfl, rfl, rfl, rfl⟩

/-- **Code typed from a member of a family at names of its own, whatever
those stand for, is typed for every member of the family.** -/
theorem ok_of_open {n : Nat} {a : BitVec 64} {E : CtxS} {k : Nat} (hE : E.under k = true)
    (h : ∀ ρ', Ok fetch sys Ψ n a ((E.open (freshOpening k)).den ρ')) (ρ : Env) (fam : Fam) :
    Ok fetch sys Ψ n a (E.den { ρ with bound := fam :: ρ.bound }) := by
  have h1 := h (ρ.withFam k fam)
  rw [show (E.open (freshOpening k)).den (ρ.withFam k fam)
      = E.den { ρ.withFam k fam with bound := famOf (ρ.withFam k fam) (freshOpening k) ::
          (ρ.withFam k fam).bound } from
    CtxS.den_open _ _ (freshOpening_closed k) E, famOf_withFam,
    CtxS.den_under ((sameBelow_withFam ρ k fam).push fam) E hE] at h1
  exact h1

/-! ## Labels -/

/-- A label of a program: an address, and the family of contexts its code
wants. -/
structure Label where
  addr : BitVec 64
  pat : CtxS

/-- The context a label's code is walked from: the member of its family at
names of its own. -/
def Label.start (l : Label) (k : Nat) : CtxS := l.pat.open (freshOpening k)

/-! ## A walk that leaves nothing to be shown -/

/-- Whether what is known of a value is that it is code wanting a family
of contexts. -/
def TyS.isCode : TyS → Bool
  | .code .. => true
  | _ => false

/-- Whether a walk leaves nothing to be shown: every instruction it stepped
over is seen not to fault of itself, every jump is decided, and every way
through it ends the program, or stops at a label in a context that may be
regarded as a member of the label's family, or goes to a value known to be
code wanting a family the context reached may be regarded as a member of.
`cc` is how a context is made ready and regarded; `k` is a name no term of
the walk yet mentions. -/
def Walk.closes (cc : CtxS → CtxS → Nat → Option (CtxS × OpenL)) (labels : List Label) :
    Nat → Walk → Bool
  | k, .stop a Γ =>
    match labels.find? fun l => l.addr == a with
    | some l => (cc l.pat Γ k).isSome
    | none => false
  | k, .arrive t Γ =>
    match Γ.known.find? fun f => f.1.same t && f.2.isCode with
    | some (tv, .code regs flags held known rest) =>
      tv.under k &&
        (match cc (codeCtx regs flags held known rest) Γ k with
         | some (Γ', _) => Γ'.known.contains (tv, .code regs flags held known rest)
         | none => false)
    | _ => false
  | _, .step _ _ _ k rest => rest.closes cc labels (k + 1)
  | _, .sys k rest => rest.closes cc labels (k + 1)
  | _, .sys2 k a b => a.closes cc labels (k + 1) && b.closes cc labels (k + 1)
  | _, .ends => true
  | _, .vacuous => true
  | k, .branch c fl taken fall =>
    fl.decides c && taken.closes cc labels k && fall.closes cc labels k

/-- Such a walk holds, where the code at each label is typed for every
member of the label's family. -/
theorem Walk.holds_of_closes {n : Nat} {labels : List Label}
    {cc : CtxS → CtxS → Nat → Option (CtxS × OpenL)} (hcc : CloseSound fetch sys Ψ n cc)
    (H : ∀ l ∈ labels, ∀ (ρ' : Env) (fam : Fam),
      Ok fetch sys Ψ n l.addr (l.pat.den { ρ' with bound := fam :: ρ'.bound })) :
    (W : Walk) → (k : Nat) → (ρ : Env) → W.closes cc labels k = true →
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ
  | .stop a Γ, k, ρ, h => by
    unfold Walk.closes at h
    cases hfind : labels.find? fun l => l.addr == a with
    | none => rw [hfind] at h; cases h
    | some l =>
      rw [hfind] at h
      have hmem := List.mem_of_find?_eq_some hfind
      have ha : l.addr = a := by simpa using List.find?_some hfind
      obtain ⟨⟨Γ', o⟩, hc⟩ := Option.isSome_iff_exists.mp h
      show Ok fetch sys Ψ n a (Γ.den ρ)
      refine hcc (Ok fetch sys Ψ n a) (fun hi _ ho h => Ok.nameSlot hi ho h)
        (fun hr hΔ => Ok.regard hr hΔ)
        (fun fs hfs h => Ok.learn fs (fun f hf k hk => hfs f hf k (by omega)) h) hc ρ
        fun ρ' _ hreg => ?_
      refine Ok.regard hreg ?_
      rw [← ha]
      exact H l hmem ρ' _
  | .arrive t Γ, k, ρ, h => by
    unfold Walk.closes at h
    split at h
    · next tv regs flags held known rest hfind =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨htv, h⟩ := h
      have hsame := (List.find?_some hfind)
      simp only [Bool.and_eq_true] at hsame
      have ht : t.den ρ = tv.den ρ := (Val.same_den ρ hsame.1).symm
      show Arrives fetch sys Ψ n (t.den ρ) (Γ.den ρ)
      rw [ht]
      cases hc : cc (codeCtx regs flags held known rest) Γ k with
      | none => rw [hc] at h; cases h
      | some Γo =>
        obtain ⟨Γ', o⟩ := Γo
        rw [hc] at h
        simp only [List.contains_iff_mem] at h
        refine hcc (Arrives fetch sys Ψ n (tv.den ρ))
          (fun hi _ ho h => Arrives.nameSlot hi ho h) (fun hr hΔ => Arrives.regard hr hΔ)
          (fun fs hfs h => Arrives.learn fs hfs h) hc ρ fun ρ' hag hreg => ?_
        rw [← Val.den_under hag tv htv]
        have hf : (tv.den ρ', Ty.code fun z => (codeCtx regs flags held known rest).den
            { ρ' with bound := z :: ρ'.bound }) ∈ (Γ'.den ρ').known := by
          rw [← code_den]
          exact List.mem_map.mpr ⟨_, h, rfl⟩
        exact Arrives.code _ hf hreg
    · cases h
  | .step i Γ next k rest, _, ρ, h => fun x => Walk.holds_of_closes hcc H rest _ _ h
  | .sys k rest, _, ρ, h => fun x => Walk.holds_of_closes hcc H rest _ _ h
  | .sys2 k a b, _, ρ, h => by
    simp only [Walk.closes, Bool.and_eq_true] at h
    exact fun x => ⟨Walk.holds_of_closes hcc H a _ _ h.1, Walk.holds_of_closes hcc H b _ _ h.2⟩
  | .ends, _, _, _ => trivial
  | .vacuous, _, _, _ => trivial
  | .branch c fl taken fall, k, ρ, h => by
    simp only [Walk.closes, Bool.and_eq_true] at h
    exact ⟨FlagsT.decides_den ρ fl c h.1.1,
      fun _ => Walk.holds_of_closes hcc H taken k ρ h.1.2,
      fun _ => Walk.holds_of_closes hcc H fall k ρ h.2⟩

/-- Nothing justified of any address. -/
def noJustify : Nat → BitVec 64 → CtxS → Bool := fun _ _ _ => false

/-- A walk in a program with no labels, nothing justified of any address:
every way through ends the program or goes to a value known to be code. -/
def Walk.auto (W : Walk) : Bool := W.closes (closeCtx (fun _ => noEnt) noJustify) [] 0

theorem Walk.holds_of_auto {n : Nat} (W : Walk) (ρ : Env) (h : W.auto = true) :
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ :=
  Walk.holds_of_closes (closeCtx_sound (fun _ => noEnt_sound) (justify := noJustify)
    fun _ _ _ hj => by cases hj)
    (fun _ hm => (List.not_mem_nil hm).elim) W 0 ρ h

/-! ## Justifying that an address is code -/

mutual

/-- One more than the largest of the nearest family's values a term speaks
of: how many values the family must range over for the term. -/
def Val.bmax (d : Nat) : Val → Nat
  | .lit _ => 0
  | .var _ => 0
  | .bvar d' j => if d' = d then j + 1 else 0
  | .slot _ => 0
  | .un _ a => a.bmax d
  | .bin _ a b => max (a.bmax d) (b.bmax d)
  | .tri _ a b c => max (max (a.bmax d) (b.bmax d)) (c.bmax d)
  | .fop _ fl a b => max (max (fl.bmax d) (a.bmax d)) (b.bmax d)

def FlagsT.bmax (d : Nat) : FlagsT → Nat
  | .src _ fl a b c => max (max (fl.bmax d) (a.bmax d)) (max (b.bmax d) (c.bmax d))
  | _ => 0

end

def heldBmax (d : Nat) (held : List (Val × HeldS)) : Nat :=
  held.foldl (fun m b => max m (max (b.1.bmax d) (b.2.slots.foldl (fun m p => max m (p.2.bmax d)) 0))) 0

mutual

def TyS.bmax (d : Nat) : TyS → Nat
  | .ptr S _ _ => S.bmax d
  | .nullable τ => τ.bmax d
  | .orErr τ => τ.bmax d
  | .str c => c.bmax d
  | .code regs flags held known _ =>
    max (max (allRegs.foldl (fun m r => max m ((regs.get r).bmax (d + 1))) 0) (flags.bmax (d + 1)))
      (max (heldBmax (d + 1) held) (known.bmax (d + 1)))
  | _ => 0

def ShapeS.bmax (d : Nat) : ShapeS → Nat
  | .mk _ vals => vals.bmax d

def ValsS.bmax (d : Nat) : ValsS → Nat
  | .nil => 0
  | .cons _ τ rest => max (τ.bmax d) (rest.bmax d)

def FactsS.bmax (d : Nat) : FactsS → Nat
  | .nil => 0
  | .cons v τ rest => max (max (v.bmax d) (τ.bmax d)) (rest.bmax d)

end

/-- How many values a family ranges over, from what its contexts speak of. -/
def CtxS.bmax (Γ : CtxS) : Nat :=
  max (max (allRegs.foldl (fun m r => max m ((Γ.regs.get r).bmax 0)) 0) (Γ.flags.bmax 0))
    (max (heldBmax 0 Γ.held) (Γ.known.foldl (fun m f => max m (max (f.1.bmax 0) (f.2.bmax 0))) 0))

/-- How many names a member of the family takes when given names of its
own: one for each value, and one at least, since its flags and whatever
else is held take the first. It is only where the walk's new names start
from: that they are new is checked each time, by computing. -/
def CtxS.width (Γ : CtxS) : Nat := max Γ.bmax 1

/-! ## What is always so of a program's static data -/

/-- What a program says of its static data is so: under the memory typing
and every one it grows to, at every step count, whatever names stand for. -/
def StaticsOk (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (st : List (Val × TyS)) : Prop :=
  ∀ (ρ : Env), ∀ f ∈ st, ∀ (n : Nat) (Ψ' : MemTy), Ψ.Ext Ψ' → Ψ'.WF →
    HasTy fetch sys Ψ' n (f.2.den ρ) (f.1.den ρ)

/-- A program with no static data says nothing of it. -/
theorem StaticsOk.nil : StaticsOk fetch sys Ψ [] := fun _ _ h => nomatch h

/-- **Code typed in a context that also knows what is always so of the
static data is typed in the context.** -/
theorem ok_statics {n : Nat} {a : BitVec 64} {Γ : CtxS} {st : List (Val × TyS)}
    (hs : StaticsOk fetch sys Ψ st) (ρ : Env)
    (h : Ok fetch sys Ψ n a ((Γ.addKnown st).den ρ)) : Ok fetch sys Ψ n a (Γ.den ρ) := by
  refine Ok.learn (st.map fun f => (f.1.den ρ, f.2.den ρ)) (fun f hf k _ Ψ' he hwf => ?_) ?_
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact hs ρ g hg k Ψ' he hwf
  · have e : (Γ.addKnown st).den ρ
        = { Γ.den ρ with known := (st.map fun f => (f.1.den ρ, f.2.den ρ)) ++ (Γ.den ρ).known } :=
      ctx_ext rfl rfl rfl List.map_append
    rw [← e]
    exact h

/-! ## Code wanting one family, known to be code wanting another -/

/-- **Whether a value known to be code wanting one family is thereby code
wanting another**, in at most so many goes: each member of the second, at
names of its own from `K` on, may be regarded as a member of the first. It
is the question asked where control arrives at code, asked of two families.
Nothing is taken as known of any address in answering it, so the answer
holds at every step count. -/
def entF : Nat → Nat → TyS → TyS → Bool
  | 0, _, _, _ => false
  | f + 1, K, .code r fl h kn rs, .code r' fl' h' kn' rs' =>
    (codeCtx r fl h kn rs).under K && (codeCtx r' fl' h' kn' rs').under K &&
      (closeCtx (entF f) noJustify (codeCtx r fl h kn rs)
        ((codeCtx r' fl' h' kn' rs').open (freshOpening K))
        (K + (codeCtx r' fl' h' kn' rs').width)).isSome
  | _ + 1, _, _, _ => false

theorem entF_sound : (f : Nat) → ∀ K, EntSound fetch sys (entF f K)
  | 0 => fun _ _ _ _ _ h => nomatch h
  | f + 1 => by
    intro K ρ v τ υ h Ψ₁ n hP
    cases τ with
    | code r fl hd kn rs =>
      cases υ with
      | code r' fl' hd' kn' rs' =>
        simp only [entF, Bool.and_eq_true] at h
        obtain ⟨⟨hPu, hΔu⟩, hcl⟩ := h
        obtain ⟨⟨Γ', o⟩, hcc⟩ := Option.isSome_iff_exists.mp hcl
        rw [code_den, hasTy_code] at hP ⊢
        intro x k hk Ψ₂ he hwf s hrip hw
        have key := closeCtx_sound (fetch := fetch) (sys := sys) (Ψ := Ψ₂) (n := k)
          (ent := entF f) (justify := noJustify) (entF_sound f) (fun _ _ _ hj => by cases hj)
          (fun C => ∀ s : State, s.rip = v → WellTyped fetch sys Ψ₂ k C s → SafeN fetch sys k s)
          (fun hi _ ho hall s hrip hw => hall _ s hrip (hw.nameSlot hi ho))
          (fun hr hQ s hrip hw => hQ s hrip (hr k Ψ₂ (MemTy.Ext.refl _) hwf s hw))
          (fun fs hfs hQ s hrip hw => hQ s hrip
            (hw.addKnown fs fun f hf => hfs f hf k (Nat.le_succ k) Ψ₂ (MemTy.Ext.refl _) hwf))
          hcc (ρ.withFam K x)
          (fun ρ' hag hreg s hrip hw => by
            have hs : Env.SameBelow K ρ' ρ :=
              (hag.mono (Nat.le_add_right K _)).trans (sameBelow_withFam ρ K x)
            have hw' := hreg k Ψ₂ (MemTy.Ext.refl _) hwf s hw
            rw [CtxS.den_under (hs.push _) _ hPu] at hw'
            exact hP _ k hk Ψ₂ he hwf s hrip hw')
        rw [CtxS.den_open _ _ (freshOpening_closed K), famOf_withFam,
          CtxS.den_under ((sameBelow_withFam ρ K x).push x) _ hΔu] at key
        exact key s hrip hw
      | _ => exact absurd h (by simp [entF])
    | _ => cases υ <;> exact absurd h (by simp [entF])

/-- **Whether an address is code wanting a family**, in at most so many
goes: it is a label, and each member of the family may be regarded as a
member of the label's; or the code there, walked from a member of the
family at names of its own, leaves nothing to be shown. -/
def justifyF (pg : Prog) (labels : List Label)
    (stops : BitVec 64 → Bool) (fuelW : Nat) : Nat → Nat → BitVec 64 → CtxS → Bool
  | 0, _, _, _ => false
  | f + 1, k, a, E =>
    E.under k && ((E.open (freshOpening k)).addKnown pg.statics).under (k + E.width) &&
      ((match labels.find? fun l => l.addr == a with
        | some l =>
          (closeCtx (entF fuelW) (justifyF pg labels stops fuelW f) l.pat ((E.open (freshOpening k)).addKnown pg.statics)
            (k + E.width)).isSome
        | none => false) ||
       (walk pg stops true fuelW (k + E.width) a ((E.open (freshOpening k)).addKnown pg.statics)).closes
          (closeCtx (entF fuelW) (justifyF pg labels stops fuelW f)) labels (k + E.width))

theorem justifyF_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {n : Nat} {pg : Prog} (hpre : PreSound fetch sys Ψ D pg.pre)
    {labels : List Label} {stops : BitVec 64 → Bool} {fuelW : Nat}
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch sys Ψ pg.statics)
    (H : ∀ l ∈ labels, ∀ (ρ' : Env) (fam : Fam),
      Ok fetch sys Ψ n l.addr (l.pat.den { ρ' with bound := fam :: ρ'.bound })) :
    (f : Nat) → JustSound fetch sys Ψ n (justifyF pg labels stops fuelW f)
  | 0 => fun _ _ _ hj => nomatch hj
  | f + 1 => by
    intro k a E hj ρ fam
    have hcc := closeCtx_sound (entF_sound fuelW)
      (justifyF_sound hD hkind hpre (stops := stops) (fuelW := fuelW) hcode hk hst H f)
    unfold justifyF at hj
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hj
    obtain ⟨⟨hE, hΔ⟩, hor⟩ := hj
    refine ok_of_open hE (fun ρ' => ok_statics hst ρ' ?_) ρ fam
    rcases hor with hl | hw
    · cases hfind : labels.find? fun l => l.addr == a with
      | none => rw [hfind] at hl; cases hl
      | some l =>
        rw [hfind] at hl
        have hmem := List.mem_of_find?_eq_some hfind
        have ha : l.addr = a := by simpa using List.find?_some hfind
        obtain ⟨⟨Γ', o⟩, hc⟩ := Option.isSome_iff_exists.mp hl
        refine hcc (Ok fetch sys Ψ n a) (fun hi _ ho h => Ok.nameSlot hi ho h)
          (fun hr hΔ => Ok.regard hr hΔ)
          (fun fs hfs h => Ok.learn fs (fun f hf k hk => hfs f hf k (by omega)) h) hc ρ'
          fun ρ'' _ hreg => ?_
        refine Ok.regard hreg ?_
        rw [← ha]
        exact H l hmem ρ'' _
    · exact (walk_sound hD hkind pg hpre stops hcode hk true fuelW (k + E.width) a
        ((E.open (freshOpening k)).addKnown pg.statics) ρ' hΔ (Walk.holds_of_closes hcc H _ (k + E.width) ρ' hw)).1

/-! ## A program -/

/-- **Whether a program is typed**: each label's family mentions no name
from the `k`th on, and from each label, started at names from the `k`th on,
the walk gets somewhere and leaves nothing to be shown. -/
def checkProgram (pg : Prog) (labels : List Label)
    (fuel k : Nat) : Bool :=
  labels.all fun l =>
    l.pat.under k && ((l.start k).addKnown pg.statics).under (k + l.pat.width) &&
      (let W := walk pg (fun a => labels.any fun l' => l'.addr == a) true fuel (k + l.pat.width) l.addr
        ((l.start k).addKnown pg.statics)
       W.moved &&
        W.closes (closeCtx (entF fuel) (justifyF pg labels (fun a => labels.any fun l' => l'.addr == a)
          fuel fuel)) labels (k + l.pat.width))

/-- **A program that checks is typed at every label, for every member of
the label's family, for any number of steps**: on any machine that fetches
its instructions at their addresses, under any system that does what Linux
is described to do. -/
theorem program_ok {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {pg : Prog} (hpre : PreSound fetch sys Ψ D pg.pre)
    {labels : List Label} {fuel k : Nat}
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch sys Ψ pg.statics)
    (h : checkProgram pg labels fuel k = true) :
    ∀ n, ∀ l ∈ labels, ∀ (ρ : Env) (fam : Fam),
      Ok fetch sys Ψ n l.addr (l.pat.den { ρ with bound := fam :: ρ.bound }) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ => Ok.zero _ _
  | succ n ih =>
    intro l hl ρ fam
    unfold checkProgram at h
    have := List.all_eq_true.mp h l hl
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨hfree, hu⟩, hm, hc⟩ := this
    have hcc := closeCtx_sound (entF_sound fuel) (justifyF_sound hD hkind hpre
      (stops := fun a => labels.any fun l' => l'.addr == a) (fuelW := fuel) hcode hk hst ih fuel)
    refine ok_of_open (k := k) hfree (fun ρ' => ok_statics hst ρ' ?_) ρ fam
    exact (walk_sound hD hkind pg hpre _ hcode hk true fuel (k + l.pat.width) l.addr
      ((l.start k).addKnown pg.statics) ρ' hu
      (Walk.holds_of_closes hcc ih _ (k + l.pat.width) ρ' hc)).2 hm

end TypedAsm.U
