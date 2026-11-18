import TypedAsm.U.Walk
import TypedAsm.U.JoinS
import TypedAsm.U.Open
import TypedAsm.U.Laws

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

/-! ## Naming what the context reached does not say -/

/-- The bytes that regions wanted say hold a value and the context reached
says nothing of: in which region of the context, and where. The regions
wanted are given with their addresses as terms of the context reached. -/
def wantedHeld (held : List (Val × HeldS)) (Γ : CtxS) : List (Nat × Val) :=
  held.flatMap fun d =>
    match hostExtent Γ.known d.1 d.2.size Γ.held with
    | some (i, o, G) =>
      d.2.slots.filterMap fun p =>
        if G.slots.any fun q => q.1.same (o.plus p.1) then none else some (i, o.plus p.1)
    | none => []

/-- A context with a region it holds said to hold, at eight of its bytes,
the value the name `k` stands for. -/
def CtxS.nameSlot (Γ : CtxS) (i : Nat) (o : Val) (k : Nat) : Option CtxS :=
  match Γ.held[i]? with
  | some (b, S) =>
    if fitsS Γ.known o 8 S.size && o.under k then
      some { Γ with held := Γ.held.set i (b, ⟨S.size, (o, .var k) :: S.slots⟩) }
    else none
  | none => none

theorem CtxS.nameSlot_ok (Q : Ctx → Prop)
    (hname : ∀ {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}, Γ.held[i]? = some (b, S) →
      ∀ {o : Nat}, (∀ (Ψ' : MemTy) (m : Nat),
        (∀ g ∈ Γ.known, HasTy fetch sys Ψ' m g.2 g.1) → o + 8 ≤ S.size) →
      (∀ x, Q { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) → Q Γ)
    {Γ Γ' : CtxS} {i : Nat} {o : Val} {k : Nat}
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
    · next hc =>
      cases h
      rw [Bool.and_eq_true] at hc
      obtain ⟨ho, hou⟩ := hc
      refine hname (S := S.den ρ) (CtxS.held_den ρ Γ hi) (o := o.nat ρ)
        (fun Ψ' m hg => by
          have := leS_den ho (knownS hg)
          simp only [Nat.add_zero] at this
          exact this) fun x => ?_
      have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
      have hb : (b.den (ρ.setVal k x), S.den (ρ.setVal k x)) = (b.den ρ, S.den ρ) := by
        have h1 := CtxS.held_den (ρ.setVal k x) Γ hi
        rw [hΓ, CtxS.held_den ρ Γ hi] at h1
        exact (Option.some.inj h1).symm
      have e : CtxS.den (ρ.setVal k x)
            { Γ with held := Γ.held.set i (b, ⟨S.size, (o, .var k) :: S.slots⟩) }
          = { Γ.den ρ with
              held := (Γ.den ρ).held.set i
                (b.den ρ, ⟨(S.den ρ).size, (o.nat ρ, x) :: (S.den ρ).vals⟩) } := by
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
        show (b.den (ρ.setVal k x), (⟨(S.den (ρ.setVal k x)).size,
          ((o.den (ρ.setVal k x)).toNat, (ρ.setVal k x).val k) ::
            (S.den (ρ.setVal k x)).vals⟩ : Held)) = _
        rw [Env.setVal_get_self, (Prod.mk.inj hb).1, (Prod.mk.inj hb).2,
          Val.den_setVal ρ k x _ hou]
        rfl
      have h2 := hok x
      rw [e] at h2
      exact h2
    · cases h

/-- The same, of each of a list of places, with a new name for each. -/
def nameSlots (Γ : CtxS) : List (Nat × Val) → Nat → Option CtxS
  | [], _ => some Γ
  | w :: ws, k =>
    match Γ.nameSlot w.1 w.2 k with
    | some Γ' => if Γ'.under (k + 1) then nameSlots Γ' ws (k + 1) else none
    | none => none

theorem nameSlots_ok (Q : Ctx → Prop)
    (hname : ∀ {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}, Γ.held[i]? = some (b, S) →
      ∀ {o : Nat}, (∀ (Ψ' : MemTy) (m : Nat),
        (∀ g ∈ Γ.known, HasTy fetch sys Ψ' m g.2 g.1) → o + 8 ≤ S.size) →
      (∀ x, Q { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) → Q Γ) :
    (ws : List (Nat × Val)) → (Γ Γ' : CtxS) → (k : Nat) → nameSlots Γ ws k = some Γ' →
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

/-- A list of pieces of a region, by where they start, as far as what is
known shows which starts first. -/
def insertPiece (K : List (Val × TyS)) (x : Val × Val) : List (Val × Val) → List (Val × Val)
  | [] => [x]
  | y :: ys => if leS K x.1 0 y.1 0 then x :: y :: ys else y :: insertPiece K x ys

def sortPieces (K : List (Val × TyS)) : List (Val × Val) → List (Val × Val)
  | [] => []
  | x :: xs => insertPiece K x (sortPieces K xs)

/-- The stretches of a region of `size` bytes, from byte `cur` on, that
pieces listed by where they start leave out. -/
def gaps (size : Val) : Val → List (Val × Val) → List (Val × Val)
  | cur, [] => if cur.same size then [] else [(cur, offTerm size cur)]
  | cur, (o, n) :: rest =>
    (if cur.same o then [] else [(cur, offTerm o cur)]) ++ gaps size (o.plus n) rest

/-- Where each region wanted lies in the context reached: in which region,
how far in, and how long. -/
def placed (held : List (Val × HeldS)) (Γ : CtxS) : List (Nat × Val × Val) :=
  held.filterMap fun d =>
    match hostExtent Γ.known d.1 d.2.size Γ.held with
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
      (gaps g.2.size (.lit 0)
        (sortPieces Γ.known ((ps.filter fun p => p.1 == i).map fun p => p.2))).map
        (stretch Γ.known g)
    | none => []

/-- The regions a family wants, with their addresses, their sizes and how
far in their values are as terms of the context reached, by what the
registers give. What the values are is left as the family says it. -/
def wantedRegions (P Γ : CtxS) : List (Val × HeldS) :=
  let bs₁ := allRegs.flatMap fun r => bindB (P.regs.get r) (Γ.regs.get r)
  let o₁ : Opening := { b := fun j => (bs₁.lookup j).getD (.lit 0), f := Γ.flags }
  P.held.map fun d => (d.1.open o₁ 0,
    ⟨d.2.size.open o₁ 0, d.2.slots.map fun p => (p.1.open o₁ 0, p.2)⟩)

/-- **A member of a family**, read off the context reached: its values from
the registers, then from the regions at the addresses those give; and,
where the family ranges over whatever else is held, all that the context
holds besides. -/
def matchOpen (P Γ : CtxS) : OpenL :=
  let bs₁ := allRegs.flatMap fun r => bindB (P.regs.get r) (Γ.regs.get r)
  let bs₂ := (wantedRegions P Γ).flatMap fun d =>
    match hostExtent Γ.known d.1 d.2.size Γ.held with
    | some (_, off, G) =>
      d.2.slots.flatMap fun p =>
        match G.slots.find? fun q => q.1.same (off.plus p.1) with
        | some g => bindB p.2 g.2
        | none => []
    | none => []
  match P.rest with
  | .bvar 0 => ⟨bs₁ ++ bs₂, Γ.flags, leftover (wantedRegions P Γ) Γ, Γ.rest⟩
  | _ => ⟨bs₁ ++ bs₂, Γ.flags, [], .none⟩

/-- The bytes a family's contexts say hold a value and the context reached
says nothing of. -/
def wantedCode (P Γ : CtxS) : List (Nat × Val) :=
  wantedHeld (wantedRegions P Γ) Γ

/-! ## Knowing that an address is code -/

/-- `JustSound n j`: wherever `j` says an address is code wanting a family,
the code there is typed for every member of the family, for `n` steps. -/
def JustSound (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat)
    (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64) (j : Nat → BitVec 64 → CtxS → Bool) : Prop :=
  ∀ k a E, j k a E = true → ∀ (ρ : Env) (fam : Fam), ρ.fn = fns →
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

/-- What a context knows that mentions no value of any family: it is so of
the same values whatever family a context is a member of. -/
def carried (Γ : CtxS) : List (Val × TyS) :=
  Γ.known.filter fun f => f.1.closedAt 0 && f.2.closedAt 0

/-- The things a member of a family knows of addresses, that they are
code, which the context reached does not know and which are justified: for
the family wanted there, with what the context reached knows besides. So
what a caller knows of a value a function keeps is known still where the
function returns. -/
def learnedFacts (justify : Nat → BitVec 64 → CtxS → Bool) (kj : Nat) (Γ Δ : CtxS) :
    List (Val × TyS) :=
  ((askedCode Γ Δ).filter fun x => justify kj x.1 (x.2.1.addKnown (carried Γ))).map
    fun x => x.2.2

/-- **The context reached, made ready to be compared**: its regions that
lie end to end taken as one, and each sum of low halves that is seen to be
the sum, taken as it. -/
def ready (Γ : CtxS) (k : Nat) : CtxS := narrowFor (joinAll Γ.held.length Γ) k

theorem ready_regards (ρ : Env) (Γ : CtxS) (k : Nat) :
    Regards fetch sys Ψ (Γ.den ρ) ((ready Γ k).den ρ) :=
  (joinAll_regards ρ Γ.held.length Γ).trans (narrowFor_regards ρ _ k)

/-- The context reached, its values named, with what it has learnt of
addresses that are code: regarded as the member of the family found, where
it may be. What was learnt is handed in, so that it is worked out once: it
is asked of the code a call returns to, which asks it of the next. -/
def closeWith (sm : List (Val × TyS) → Val → Val → Bool) (ent : TyS → TyS → Bool)
    (P Γ' : CtxS) (learnt : List (Val × TyS)) : Option (CtxS × OpenL) :=
  if (matchOpen P Γ').closed &&
      regardWith sm ent (Γ'.addKnown learnt) (P.open (matchOpen P Γ').opening) then
    some (Γ'.addKnown learnt, matchOpen P Γ')
  else none

/-- **The context reached, made ready to be regarded as a member of a
family**: its regions that lie end to end taken as one; the values the
family names and it does not, named; and the addresses the member knows to
be code and it does not, known to be so where that is justified. Nothing
unless it may then be regarded as the member found, which is given with it.
`k` is a name no term yet mentions. -/
def closeCtx (sm : List (Val × TyS) → Val → Val → Bool) (ent : Nat → TyS → TyS → Bool)
    (justify : Nat → BitVec 64 → CtxS → Bool) (P Γ : CtxS) (k : Nat) :
    Option (CtxS × OpenL) :=
  if (ready Γ k).under k then
    match nameSlots (ready Γ k) (wantedCode P (ready Γ k)) k with
    | some Γ' =>
      closeWith sm (ent (k + (wantedCode P (ready Γ k)).length)) P Γ'
        (learnedFacts justify (k + (wantedCode P (ready Γ k)).length) Γ'
          (P.open (matchOpen P Γ').opening))
    | none => none
  else none

/-- `CloseSound n cc`: where `cc` succeeds, whatever holds of the context
made ready, given that it may be regarded as the member, holds of the
context reached: for anything that holds of a context when it holds of one
the context may be regarded as; when it holds whatever value a region holds
at bytes the context says nothing of; and when it holds with more known
that is so wherever what the context knows is. -/
def CloseSound (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat)
    (fns : Nat → BitVec 64 → BitVec 64 → BitVec 64)
    (cc : CtxS → CtxS → Nat → Option (CtxS × OpenL)) : Prop :=
  ∀ (Q : Ctx → Prop),
    (∀ {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}, Γ.held[i]? = some (b, S) →
      ∀ {o : Nat}, (∀ (Ψ' : MemTy) (m : Nat),
        (∀ g ∈ Γ.known, HasTy fetch sys Ψ' m g.2 g.1) → o + 8 ≤ S.size) →
      (∀ x, Q { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) → Q Γ) →
    (∀ {Γ Δ : Ctx}, Regards fetch sys Ψ Γ Δ → Q Δ → Q Γ) →
    (∀ {Γ : Ctx} (fs : List Fact),
      (∀ f ∈ fs, ∀ k, k ≤ n + 1 → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
        (∀ g ∈ Γ.known, HasTy fetch sys Ψ' k g.2 g.1) → HasTy fetch sys Ψ' k f.2 f.1) →
      Q { Γ with known := fs ++ Γ.known } → Q Γ) →
    ∀ {P Γ Γ' : CtxS} {o : OpenL} {k : Nat}, cc P Γ k = some (Γ', o) → ∀ ρ : Env, ρ.fn = fns →
    (∀ ρ', Env.SameBelow k ρ' ρ →
      Regards fetch sys Ψ (Γ'.den ρ') (P.den { ρ' with bound := famOf ρ' o.opening :: ρ'.bound }) →
      Q (Γ'.den ρ')) →
    Q (Γ.den ρ)

theorem closeCtx_sound {n : Nat} {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64}
    {sm : List (Val × TyS) → Val → Val → Bool}
    (hsm : ∀ (ρ : Env), ρ.fn = fns → ∀ (K : List (Val × TyS)) (Ψ' : MemTy) (m : Nat),
      (∀ g ∈ K, HasTy fetch sys Ψ' m (g.2.den ρ) (g.1.den ρ)) →
      ∀ a b, sm K a b = true → a.den ρ = b.den ρ)
    {ent : Nat → TyS → TyS → Bool}
    (he : ∀ kf, EntSound fetch sys (ent kf)) {justify : Nat → BitVec 64 → CtxS → Bool}
    (hj : JustSound fetch sys Ψ n fns justify) :
    CloseSound fetch sys Ψ n fns (closeCtx sm ent justify) := by
  intro Q hname hreg hlearn P Γ Γ'' o k h ρ hfn hQ
  unfold closeCtx at h
  split at h
  · next hu =>
    cases hn : nameSlots (ready Γ k)
        (wantedCode P (ready Γ k)) k with
    | none => rw [hn] at h; cases h
    | some Γ₁ =>
      rw [hn] at h
      simp only [closeWith] at h
      split at h
      · next hc =>
        cases h
        simp only [Bool.and_eq_true] at hc
        refine hreg (ready_regards ρ Γ k) ?_
        refine nameSlots_ok Q hname _ _ Γ₁ k hn hu ρ fun ρ' hag => ?_
        refine hlearn ((learnedFacts justify
            (k + (wantedCode P (ready Γ k)).length) Γ₁
            (P.open (matchOpen P Γ₁).opening)).map fun f => (f.1.den ρ', f.2.den ρ')) ?_ ?_
        · intro f hf k' hk' Ψ' he hwf hΓk
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
          obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
          obtain ⟨hlit, r, fl, hd, kn, rs, hty, hE⟩ := askedCode_spec hx1
          show HasTy fetch sys Ψ' k' (x.2.2.2.den ρ') (x.2.2.1.den ρ')
          rw [Val.lit?_den hlit, hty, code_den, hasTy_code, ← hE]
          intro z j hjlt Ψ'' he' hwf' s hs hw
          refine hj _ _ _ hx2 ρ' z (hag.fn.trans hfn) j (by omega) Ψ'' (he.trans he') hwf' s hs ?_
          have e : CtxS.den { ρ' with bound := z :: ρ'.bound } (x.2.1.addKnown (carried Γ₁))
              = { x.2.1.den { ρ' with bound := z :: ρ'.bound } with known :=
                  ((carried Γ₁).map fun f => (f.1.den { ρ' with bound := z :: ρ'.bound },
                    f.2.den { ρ' with bound := z :: ρ'.bound }))
                    ++ (x.2.1.den { ρ' with bound := z :: ρ'.bound }).known } :=
            ctx_ext rfl rfl rfl (List.map_append)
          rw [e]
          refine hw.addKnown _ fun c hc => ?_
          obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
          obtain ⟨hmem, hcl⟩ := List.mem_filter.mp hc₀
          rw [Bool.and_eq_true] at hcl
          show HasTy fetch sys Ψ'' j (c₀.2.den { ρ' with bound := z :: ρ'.bound })
            (c₀.1.den { ρ' with bound := z :: ρ'.bound })
          rw [Val.den_bound ρ' _ c₀.1 hcl.1, TyS.den_bound ρ' _ c₀.2 hcl.2]
          exact ((hΓk (c₀.1.den ρ', c₀.2.den ρ')
            (List.mem_map.mpr ⟨c₀, hmem, rfl⟩)).ext he').mono (Nat.le_of_lt hjlt)
        · have e : CtxS.den ρ' (Γ₁.addKnown (learnedFacts justify
                (k + (wantedCode P (ready Γ k)).length) Γ₁
                (P.open (matchOpen P Γ₁).opening)))
              = { Γ₁.den ρ' with known :=
                  ((learnedFacts justify (k + (wantedCode P (ready Γ k)).length) Γ₁
                    (P.open (matchOpen P Γ₁).opening)).map fun f => (f.1.den ρ', f.2.den ρ'))
                    ++ (Γ₁.den ρ').known } :=
            ctx_ext rfl rfl rfl (List.map_append)
          rw [← e]
          refine hQ ρ' hag ?_
          rw [← CtxS.den_open ρ' _ (OpenL.closed_opening hc.1)]
          exact regardWith_sound (he _) ρ'
            (fun Ψ' m hg a b hs => hsm ρ' (hag.fn.trans hfn) _ Ψ' m hg a b hs) hc.2
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
    rfl, rfl, rfl, rfl, rfl⟩

/-- **Code typed from a member of a family at names of its own, whatever
those stand for, is typed for every member of the family.** -/
theorem ok_of_open {n : Nat} {a : BitVec 64} {E : CtxS} {k : Nat} (hE : E.under k = true)
    {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64}
    (h : ∀ ρ', ρ'.fn = fns → Ok fetch sys Ψ n a ((E.open (freshOpening k)).den ρ')) (ρ : Env)
    (fam : Fam) (hfn : ρ.fn = fns) :
    Ok fetch sys Ψ n a (E.den { ρ with bound := fam :: ρ.bound }) := by
  have h1 := h (ρ.withFam k fam) hfn
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

/-- **A program's labels, to be found quickly**: in order, and a table
from an address to how far along the first label there is. It is made once
for a program. -/
structure LabelIx where
  arr : Array Label
  byAddr : Trie

/-- The index of some labels. -/
def labelIx (labels : List Label) : LabelIx :=
  ⟨labels.toArray, Trie.ofAddrs (labels.map (·.addr)) 0 .nil⟩

/-- The label at an address: found by the table, looked at, and taken only
if it is at the address. -/
def LabelIx.find (lx : LabelIx) (a : BitVec 64) : Option Label :=
  match lx.byAddr.find 64 a.toNat with
  | some i =>
    match lx.arr[i]? with
    | some l => if l.addr = a then some l else none
    | none => none
  | none => none

theorem labelIx_find {labels : List Label} {a : BitVec 64} {l : Label}
    (h : (labelIx labels).find a = some l) : l ∈ labels ∧ l.addr = a := by
  unfold LabelIx.find at h
  split at h
  · split at h
    · next l₀ hl₀ =>
      split at h
      · next ha => cases h; exact ⟨List.mem_toArray.mp (Array.mem_of_getElem? hl₀), ha⟩
      · cases h
    · cases h
  · cases h

/-- Whether a walk leaves nothing to be shown: every instruction it stepped
over is seen not to fault of itself, every jump is decided, and every way
through it ends the program, or stops at a label in a context that may be
regarded as a member of the label's family, or goes to a value known to be
code wanting a family the context reached may be regarded as a member of.
`cc` is how a context is made ready and regarded; `k` is a name no term of
the walk yet mentions. -/
def Walk.closes (cc : CtxS → CtxS → Nat → Option (CtxS × OpenL))
    (findL : BitVec 64 → Option Label) :
    Nat → Walk → Bool
  | k, .stop a Γ =>
    match findL a with
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
  | _, .step _ _ _ k rest => rest.closes cc findL (k + 1)
  | _, .sys k rest => rest.closes cc findL (k + 2)
  | _, .sys2 k a b => a.closes cc findL (k + 2) && b.closes cc findL (k + 2)
  | _, .ends => true
  | _, .vacuous => true
  | k, .branch c fl taken fall =>
    fl.decides c && taken.closes cc findL k && fall.closes cc findL k

/-- Such a walk holds, where the code at each label is typed for every
member of the label's family. -/
theorem Walk.holds_of_closes {n : Nat} {labels : List Label}
    {findL : BitVec 64 → Option Label}
    (hfl : ∀ a l, findL a = some l → l ∈ labels ∧ l.addr = a)
    {fns : Nat → BitVec 64 → BitVec 64 → BitVec 64}
    {cc : CtxS → CtxS → Nat → Option (CtxS × OpenL)} (hcc : CloseSound fetch sys Ψ n fns cc)
    (H : ∀ l ∈ labels, ∀ (ρ' : Env) (fam : Fam), ρ'.fn = fns →
      Ok fetch sys Ψ n l.addr (l.pat.den { ρ' with bound := fam :: ρ'.bound })) :
    (W : Walk) → (k : Nat) → (ρ : Env) → ρ.fn = fns → W.closes cc findL k = true →
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ
  | .stop a Γ, k, ρ, hfn, h => by
    unfold Walk.closes at h
    cases hfind : findL a with
    | none => rw [hfind] at h; cases h
    | some l =>
      rw [hfind] at h
      obtain ⟨hmem, ha⟩ := hfl a l hfind
      obtain ⟨⟨Γ', o⟩, hc⟩ := Option.isSome_iff_exists.mp h
      show Ok fetch sys Ψ n a (Γ.den ρ)
      refine hcc (Ok fetch sys Ψ n a) (fun hi _ ho h => Ok.nameSlot hi ho h)
        (fun hr hΔ => Ok.regard hr hΔ)
        (fun fs hfs h => Ok.learnRel fs (fun f hf k hk => hfs f hf k (by omega)) h) hc ρ hfn
        fun ρ' hag hreg => ?_
      refine Ok.regard hreg ?_
      rw [← ha]
      exact H l hmem ρ' _ (hag.fn.trans hfn)
  | .arrive t Γ, k, ρ, hfn, h => by
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
          (fun fs hfs h => Arrives.learnRel fs hfs h) hc ρ hfn fun ρ' hag hreg => ?_
        rw [← Val.den_under hag tv htv]
        have hf : (tv.den ρ', Ty.code fun z => (codeCtx regs flags held known rest).den
            { ρ' with bound := z :: ρ'.bound }) ∈ (Γ'.den ρ').known := by
          rw [← code_den]
          exact List.mem_map.mpr ⟨_, h, rfl⟩
        exact Arrives.code _ hf hreg
    · cases h
  | .step i Γ next k rest, _, ρ, hfn, h => fun x => Walk.holds_of_closes hfl hcc H rest _ _ hfn h
  | .sys k rest, _, ρ, hfn, h => fun x y => Walk.holds_of_closes hfl hcc H rest _ _ hfn h
  | .sys2 k a b, _, ρ, hfn, h => by
    simp only [Walk.closes, Bool.and_eq_true] at h
    exact fun x y => ⟨Walk.holds_of_closes hfl hcc H a _ _ hfn h.1,
      Walk.holds_of_closes hfl hcc H b _ _ hfn h.2⟩
  | .ends, _, _, _, _ => trivial
  | .vacuous, _, _, _, _ => trivial
  | .branch c fl taken fall, k, ρ, hfn, h => by
    simp only [Walk.closes, Bool.and_eq_true] at h
    exact ⟨FlagsT.decides_den ρ fl c h.1.1,
      fun _ => Walk.holds_of_closes hfl hcc H taken k ρ hfn h.1.2,
      fun _ => Walk.holds_of_closes hfl hcc H fall k ρ hfn h.2⟩

/-- Nothing justified of any address. -/
def noJustify : Nat → BitVec 64 → CtxS → Bool := fun _ _ _ => false

/-- A walk in a program with no labels, nothing justified of any address:
every way through ends the program or goes to a value known to be code. -/
def Walk.auto (W : Walk) : Bool :=
  W.closes (closeCtx sameK (fun _ => noEnt) noJustify) (fun _ => none) 0

theorem Walk.holds_of_auto {n : Nat} (W : Walk) (ρ : Env) (h : W.auto = true) :
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ :=
  Walk.holds_of_closes (labels := []) (findL := fun _ => none) (fun _ _ hx => by cases hx)
    (fns := ρ.fn)
    (closeCtx_sound (fun ρ' _ _ _ _ _ _ _ hs => Val.same_den ρ' hs) (fun _ => noEnt_sound)
      (justify := noJustify) fun _ _ _ hj => by cases hj)
    (fun _ hm => (List.not_mem_nil hm).elim) W 0 ρ rfl h

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
  | .app _ a b => max (a.bmax d) (b.bmax d)

def FlagsT.bmax (d : Nat) : FlagsT → Nat
  | .src _ fl a b c => max (max (fl.bmax d) (a.bmax d)) (max (b.bmax d) (c.bmax d))
  | _ => 0

end

def heldBmax (d : Nat) (held : List (Val × HeldS)) : Nat :=
  held.foldl (fun m b => max m (max (max (b.1.bmax d) (b.2.size.bmax d))
    (b.2.slots.foldl (fun m p => max m (max (p.1.bmax d) (p.2.bmax d))) 0))) 0

mutual

def TyS.bmax (d : Nat) : TyS → Nat
  | .ptr S _ _ => S.bmax d
  | .nullable τ => τ.bmax d
  | .orErr τ => τ.bmax d
  | .str c => c.bmax d
  | .arr c τ _ => max (c.bmax d) (τ.bmax d)
  | .upTo t _ => t.bmax d
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
      (closeCtx sameK (entF f) noJustify (codeCtx r fl h kn rs)
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
          (fns := ρ.fn) (sm := sameK) (fun ρ' _ _ _ _ _ _ _ hs => Val.same_den ρ' hs)
          (ent := entF f) (justify := noJustify) (entF_sound f) (fun _ _ _ hj => by cases hj)
          (fun C => ∀ s : State, s.rip = v → WellTyped fetch sys Ψ₂ k C s → SafeN fetch sys k s)
          (fun hi _ ho hall s hrip hw => hall _ s hrip (hw.nameSlot hi (ho _ _ hw.known)))
          (fun hr hQ s hrip hw => hQ s hrip (hr k Ψ₂ (MemTy.Ext.refl _) hwf s hw))
          (fun fs hfs hQ s hrip hw => hQ s hrip
            (hw.addKnown fs fun f hf =>
              hfs f hf k (Nat.le_succ k) Ψ₂ (MemTy.Ext.refl _) hwf hw.known))
          hcc (ρ.withFam K x) rfl
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
def justifyF (pg : Prog) (ix : Index) (findL : BitVec 64 → Option Label)
    (stops : BitVec 64 → Bool) (fuelW : Nat) : Nat → Nat → BitVec 64 → CtxS → Bool
  | 0, _, _, _ => false
  | f + 1, k, a, E =>
    E.under k && ((E.open (freshOpening k)).addKnown pg.statics).under (k + E.width) &&
      ((match findL a with
        | some l =>
          (closeCtx (sameBy pg.fns pg.laws) (entF fuelW) (justifyF pg ix findL stops fuelW f) l.pat
            ((E.open (freshOpening k)).addKnown pg.statics) (k + E.width)).isSome
        | none => false) ||
       (walkFrom pg ix stops 0 true fuelW (k + E.width) a
          (evalFor pg.fns ((E.open (freshOpening k)).addKnown pg.statics) (k + E.width))).closes
          (closeCtx (sameBy pg.fns pg.laws) (entF fuelW) (justifyF pg ix findL stops fuelW f)) findL
          (k + E.width))

theorem justifyF_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {n : Nat} {pg : Prog} (hpre : PreSound fetch sys Ψ D pg.pre)
    {ix : Index} (hix : ∀ e ∈ ix.arr, e ∈ pg.code)
    {labels : List Label} {findL : BitVec 64 → Option Label}
    (hfl : ∀ a l, findL a = some l → l ∈ labels ∧ l.addr = a)
    {stops : BitVec 64 → Bool} {fuelW : Nat}
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch sys Ψ pg.statics) (hlaws : LawsHold pg.fns pg.laws)
    (H : ∀ l ∈ labels, ∀ (ρ' : Env) (fam : Fam), ρ'.fn = pg.fns →
      Ok fetch sys Ψ n l.addr (l.pat.den { ρ' with bound := fam :: ρ'.bound })) :
    (f : Nat) → JustSound fetch sys Ψ n pg.fns (justifyF pg ix findL stops fuelW f)
  | 0 => fun _ _ _ hj => nomatch hj
  | f + 1 => by
    intro k a E hj ρ fam hfn
    have hcc := closeCtx_sound (sm := sameBy pg.fns pg.laws)
      (fun ρ' hfn' _ _ _ hg _ _ hs => sameBy_den hfn' hlaws hg hs) (entF_sound fuelW)
      (justifyF_sound hD hkind hpre hix hfl (stops := stops) (fuelW := fuelW) hcode hk hst hlaws H f)
    unfold justifyF at hj
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hj
    obtain ⟨⟨hE, hΔ⟩, hor⟩ := hj
    refine ok_of_open hE (fun ρ' hfn' => ok_statics hst ρ' ?_) ρ fam hfn
    rcases hor with hl | hw
    · cases hfind : findL a with
      | none => rw [hfind] at hl; cases hl
      | some l =>
        rw [hfind] at hl
        obtain ⟨hmem, ha⟩ := hfl a l hfind
        obtain ⟨⟨Γ', o⟩, hc⟩ := Option.isSome_iff_exists.mp hl
        refine hcc (Ok fetch sys Ψ n a) (fun hi _ ho h => Ok.nameSlot hi ho h)
          (fun hr hΔ => Ok.regard hr hΔ)
          (fun fs hfs h => Ok.learnRel fs (fun f hf k hk => hfs f hf k (by omega)) h) hc ρ' hfn'
          fun ρ'' hag hreg => ?_
        refine Ok.regard hreg ?_
        rw [← ha]
        exact H l hmem ρ'' _ (hag.fn.trans hfn')
    · exact Ok.regard (evalFor_regards hfn' _ _)
        (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix 0 true fuelW (k + E.width) a
          (evalFor pg.fns ((E.open (freshOpening k)).addKnown pg.statics) (k + E.width)) ρ'
          (evalFor_under hΔ) (Walk.holds_of_closes hfl hcc H _ (k + E.width) ρ' hfn' hw)).1

/-! ## A program -/

/-- **Whether a program is typed**: each label's family mentions no name
from the `k`th on, and from each label, started at names from the `k`th on,
the walk gets somewhere and leaves nothing to be shown. -/
def checkWith (pg : Prog) (ix : Index) (lx : LabelIx) (labels : List Label) (fuel k : Nat) :
    Bool :=
  labels.all fun l =>
    l.pat.under k && ((l.start k).addKnown pg.statics).under (k + l.pat.width) &&
      (let W := walkFrom pg ix lx.byAddr.has 0 true fuel (k + l.pat.width) l.addr
        (evalFor pg.fns ((l.start k).addKnown pg.statics) (k + l.pat.width))
       W.moved &&
        W.closes (closeCtx (sameBy pg.fns pg.laws) (entF fuel)
          (justifyF pg ix lx.find lx.byAddr.has fuel fuel)) lx.find
          (k + l.pat.width))

/-- **Whether a program is typed**: `checkWith`, with the program's
instructions and the labels' addresses made ready to be found once. -/
def checkProgram (pg : Prog) (labels : List Label) (fuel k : Nat) : Bool :=
  checkWith pg pg.index (labelIx labels) labels fuel k

/-- **A program that checks is typed at every label, for every member of
the label's family, for any number of steps**: on any machine that fetches
its instructions at their addresses, under any system that does what Linux
is described to do. -/
theorem program_ok {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {pg : Prog} (hpre : PreSound fetch sys Ψ D pg.pre)
    {labels : List Label} {fuel k : Nat}
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch sys Ψ pg.statics) (hlaws : LawsHold pg.fns pg.laws)
    (h : checkProgram pg labels fuel k = true) :
    ∀ n, ∀ l ∈ labels, ∀ (ρ : Env) (fam : Fam), ρ.fn = pg.fns →
      Ok fetch sys Ψ n l.addr (l.pat.den { ρ with bound := fam :: ρ.bound }) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ => Ok.zero _ _
  | succ n ih =>
    intro l hl ρ fam hfn
    unfold checkProgram checkWith at h
    have := List.all_eq_true.mp h l hl
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨hfree, hu⟩, hm, hc⟩ := this
    have hcc := closeCtx_sound (sm := sameBy pg.fns pg.laws)
      (fun ρ' hfn' _ _ _ hg _ _ hs => sameBy_den hfn' hlaws hg hs) (entF_sound fuel)
      (justifyF_sound hD hkind hpre pg.index_mem (fun _ _ => labelIx_find)
        (stops := (labelIx labels).byAddr.has) (fuelW := fuel) hcode hk hst hlaws
        ih fuel)
    refine ok_of_open (k := k) hfree (fun ρ' hfn' => ok_statics hst ρ' ?_) ρ fam hfn
    exact Ok.regard (evalFor_regards hfn' _ _)
      ((walkFrom_sound hD hkind pg hpre _ hcode hk pg.index pg.index_mem 0 true fuel
        (k + l.pat.width) l.addr
        (evalFor pg.fns ((l.start k).addKnown pg.statics) (k + l.pat.width)) ρ' (evalFor_under hu)
        (Walk.holds_of_closes (fun _ _ => labelIx_find) hcc ih _ (k + l.pat.width) ρ' hfn' hc)).2 hm)

end TypedAsm.U
