import TypedAsm.U.Walk
import TypedAsm.U.JoinS
import TypedAsm.U.NameFree

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
    (∀ ρ', (∀ v : Val, v.under k = true → v.den ρ' = v.den ρ) → Q (Γ'.den ρ')) →
    Q (Γ.den ρ)
  | [], Γ, Γ', _, h, _, ρ, hok => by cases h; exact hok ρ fun _ _ => rfl
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
        refine hok ρ' fun v hv => ?_
        rw [hag v (Val.under_mono (Nat.le_succ k) v hv)]
        exact Val.den_setVal ρ k x v hv
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

/-! ## Regarding the context reached as a member of a family -/

/-- **The context reached, made ready to be regarded as a member of a
family**: its regions that lie end to end taken as one, and the values the
family names and it does not, named. Nothing unless it may then be
regarded as the member found. `k` is a name no term yet mentions. -/
def closeCtx (P Γ : CtxS) (k : Nat) : Option CtxS :=
  if (joinAll Γ.held.length Γ).under k then
    match nameSlots (joinAll Γ.held.length Γ) (wantedCode P (joinAll Γ.held.length Γ)) k with
    | some Γ' =>
      if (matchOpen P Γ').closed && regardS Γ' (P.open (matchOpen P Γ').opening) then some Γ'
      else none
    | none => none
  else none

/-- Where that succeeds, whatever holds of the context made ready, given
that it may be regarded as the member, holds of the context reached: for
anything that holds of a context when it holds of one the context may be
regarded as, and of a context when it holds whatever value a region holds
at bytes the context says nothing of. -/
theorem closeCtx_sound (Q : Ctx → Prop)
    (hname : ∀ {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}, Γ.held[i]? = some (b, S) →
      ∀ {o : Nat}, o + 8 ≤ S.size →
      (∀ x, Q { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) → Q Γ)
    (hreg : ∀ {Γ Δ : Ctx}, Regards fetch sys Ψ Γ Δ → Q Δ → Q Γ)
    {P Γ Γ' : CtxS} {k : Nat} (h : closeCtx P Γ k = some Γ') (ρ : Env)
    (hQ : ∀ ρ', (∀ v : Val, v.under k = true → v.den ρ' = v.den ρ) →
      Regards fetch sys Ψ (Γ'.den ρ')
        (P.den { ρ' with bound := famOf ρ' (matchOpen P Γ').opening :: ρ'.bound }) →
      Q (Γ'.den ρ')) :
    Q (Γ.den ρ) := by
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
        refine nameSlots_ok Q hname _ _ _ k hn hu ρ fun ρ' hag => ?_
        refine hQ ρ' hag ?_
        rw [← CtxS.den_open ρ' _ (OpenL.closed_opening hc.1)]
        exact regardS_sound ρ' hc.2
      · cases h
  · cases h

/-! ## Labels -/

/-- A label of a program: an address, and the family of contexts its code
wants, with how many values the family ranges over. -/
structure Label where
  addr : BitVec 64
  m : Nat
  pat : CtxS

/-- A member of a family at names of its own: the `k`th and after for its
values, and the `k`th for its flags and for whatever else is held. -/
def freshOpening (k : Nat) : Opening :=
  { b := fun j => .var (k + j), f := .var k, rest := [], tail := .name k }

theorem freshOpening_closed (k : Nat) : (freshOpening k).Closed :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- The context a label's code is walked from: the member of its family at
names of its own. -/
def Label.start (l : Label) (k : Nat) : CtxS := l.pat.open (freshOpening k)

/-- A setting of the names in which those from the `k`th on stand for a
given member of a family. -/
def Env.withFam (ρ : Env) (k : Nat) (fam : Fam) : Env :=
  { ρ with val := fun i => fam.vals (i - k), flags := fun _ => fam.flags, frame := fun _ => fam.rest }

theorem famOf_withFam (ρ : Env) (k : Nat) (fam : Fam) :
    famOf (ρ.withFam k fam) (freshOpening k) = fam := by
  have hv : (fun j => fam.vals (k + j - k)) = fam.vals :=
    funext fun j => by rw [Nat.add_sub_cancel_left]
  show Fam.mk (fun j => fam.vals (k + j - k)) fam.flags ([] ++ fam.rest) = fam
  rw [hv]
  rfl

/-- **A label's code typed from its starting context, whatever the names
stand for, is typed for every member of its family.** -/
theorem Label.ok_of_start {n : Nat} {l : Label} {k : Nat} (hfree : l.pat.nameFree = true)
    (h : ∀ ρ', Ok fetch sys Ψ n l.addr ((l.start k).den ρ')) (ρ : Env) (fam : Fam) :
    Ok fetch sys Ψ n l.addr (l.pat.den { ρ with bound := fam :: ρ.bound }) := by
  have h1 := h (ρ.withFam k fam)
  rw [show (l.start k).den (ρ.withFam k fam)
      = l.pat.den { ρ.withFam k fam with bound := famOf (ρ.withFam k fam) (freshOpening k) ::
          (ρ.withFam k fam).bound } from
    CtxS.den_open _ _ (freshOpening_closed k) l.pat, famOf_withFam] at h1
  rw [CtxS.den_nameFree (ρ₁ := { ρ with bound := fam :: ρ.bound })
    (ρ₂ := { ρ.withFam k fam with bound := fam :: (ρ.withFam k fam).bound }) ⟨rfl, rfl⟩ l.pat hfree]
  exact h1

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
`k` is a name no term of the walk yet mentions. -/
def Walk.closes (labels : List Label) : Nat → Walk → Bool
  | k, .stop a Γ =>
    match labels.find? fun l => l.addr == a with
    | some l => (closeCtx l.pat Γ k).isSome
    | none => false
  | k, .arrive t Γ =>
    match Γ.known.find? fun f => f.1.same t && f.2.isCode with
    | some (tv, .code regs flags held known rest) =>
      tv.under k &&
        (match closeCtx (codeCtx regs flags held known rest) Γ k with
         | some Γ' => Γ'.known.contains (tv, .code regs flags held known rest)
         | none => false)
    | _ => false
  | _, .step i Γ _ k rest => guardS i Γ.flags && rest.closes labels (k + 1)
  | _, .sys k rest => rest.closes labels (k + 1)
  | _, .ends => true
  | k, .branch c Γ taken fall =>
    Γ.flags.decides c && taken.closes labels k && fall.closes labels k

/-- Such a walk holds, where the code at each label is typed for every
member of the label's family. -/
theorem Walk.holds_of_closes {n : Nat} {labels : List Label}
    (H : ∀ l ∈ labels, ∀ (ρ' : Env) (fam : Fam),
      Ok fetch sys Ψ n l.addr (l.pat.den { ρ' with bound := fam :: ρ'.bound })) :
    (W : Walk) → (k : Nat) → (ρ : Env) → W.closes labels k = true →
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ
  | .stop a Γ, k, ρ, h => by
    unfold Walk.closes at h
    cases hfind : labels.find? fun l => l.addr == a with
    | none => rw [hfind] at h; cases h
    | some l =>
      rw [hfind] at h
      have hmem := List.mem_of_find?_eq_some hfind
      have ha : l.addr = a := by simpa using List.find?_some hfind
      obtain ⟨Γ', hc⟩ := Option.isSome_iff_exists.mp h
      show Ok fetch sys Ψ n a (Γ.den ρ)
      refine closeCtx_sound (Ok fetch sys Ψ n a) (fun hi _ ho h => Ok.nameSlot hi ho h)
        (fun hr hΔ => Ok.regard hr hΔ) hc ρ fun ρ' _ hreg => ?_
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
      cases hc : closeCtx (codeCtx regs flags held known rest) Γ k with
      | none => rw [hc] at h; cases h
      | some Γ' =>
        rw [hc] at h
        simp only [List.contains_iff_mem] at h
        refine closeCtx_sound (Arrives fetch sys Ψ n (tv.den ρ))
          (fun hi _ ho h => Arrives.nameSlot hi ho h) (fun hr hΔ => Arrives.regard hr hΔ) hc ρ
          fun ρ' hag hreg => ?_
        rw [← hag tv htv]
        have hf : (tv.den ρ', Ty.code fun z => (codeCtx regs flags held known rest).den
            { ρ' with bound := z :: ρ'.bound }) ∈ (Γ'.den ρ').known := by
          rw [← code_den]
          exact List.mem_map.mpr ⟨_, h, rfl⟩
        exact Arrives.code _ hf hreg
    · cases h
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

/-- A walk in a program with no labels: every way through ends the program
or goes to a value known to be code. -/
def Walk.auto (W : Walk) : Bool := W.closes [] 0

theorem Walk.holds_of_auto {n : Nat} (W : Walk) (ρ : Env) (h : W.auto = true) :
    W.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ :=
  Walk.holds_of_closes (fun _ hm => (List.not_mem_nil hm).elim) W 0 ρ h

/-! ## A program -/

/-- **Whether a program is typed**: each label's family mentions no names,
and from each label, started at names from the `k`th on, the walk gets
somewhere and leaves nothing to be shown. -/
def checkProgram (code : List (BitVec 64 × Instr × BitVec 64)) (labels : List Label)
    (fuel k : Nat) : Bool :=
  labels.all fun l =>
    l.pat.nameFree && (l.start k).under (k + l.m) &&
      (let W := walk code (fun a => labels.any fun l' => l'.addr == a) true fuel (k + l.m) l.addr
        (l.start k)
       W.moved && W.closes labels (k + l.m))

/-- **A program that checks is typed at every label, for every member of
the label's family, for any number of steps**: on any machine that fetches
its instructions at their addresses, under any system that does what Linux
is described to do. -/
theorem program_ok {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {code : List (BitVec 64 × Instr × BitVec 64)}
    {labels : List Label} {fuel k : Nat}
    (hcode : ∀ e ∈ code, fetch e.1 = some (e.2.1, e.2.2))
    (h : checkProgram code labels fuel k = true) :
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
    refine Label.ok_of_start (k := k) hfree (fun ρ' => ?_) ρ fam
    exact (walk_sound hD hkind hpre code _ hcode true fuel (k + l.m) l.addr (l.start k) ρ' hu
      (Walk.holds_of_closes ih _ (k + l.m) ρ' hc)).2 hm

end TypedAsm.U
