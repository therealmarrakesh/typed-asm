import TypedAsm.U.Closed

/-!
# A family of contexts, at particular values

That a value is code wanting a family of contexts is known as data: the
contexts as terms, in which the values the family ranges over are named by
how many families out they belong to, and which of that family's they are.
A family written inside another may so speak of the outer one's values.

To use the knowledge, each value of the family is given a term: the context
that results stands for the member of the family at the values the terms
stand for. Inside it, families further in are untouched, and what spoke of
families further out speaks of them still, one nearer.
-/

namespace TypedAsm.U

open TypedAsm

/-- What a member of a family is, as terms: one for each of its values, one
for its flags, and the regions that are whatever else is held: some written
out, and the rest as it may itself be said. -/
structure Opening where
  b : Nat → Val
  f : FlagsT
  rest : List (Val × HeldS) := []
  tail : RestS := .none

/-- The terms mention no family's values. -/
structure Opening.Closed (o : Opening) : Prop where
  b : ∀ j, (o.b j).closedAt 0 = true
  f : o.f.closedAt 0 = true
  rest : heldClosedAt 0 o.rest = true
  tail : o.tail.closedAt 0 = true

/-- The member of a family that given terms stand for. -/
def famOf (ρ : Env) (o : Opening) : Fam where
  vals j := (o.b j).den ρ
  flags := o.f.den ρ
  rest := (o.rest.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ o.tail

/-- A stack of families' values with one more put in at a depth. -/
theorem insert_getD (s : Fam) (zs : List Fam) : (pre : List Fam) → (d : Nat) →
    (pre ++ s :: zs).getD d {}
      = if d < pre.length then (pre ++ zs).getD d {}
        else if d = pre.length then s else (pre ++ zs).getD (d - 1) {}
  | [], 0 => rfl
  | [], d + 1 => rfl
  | p :: pre, 0 => rfl
  | p :: pre, d + 1 => by
    have ih := insert_getD s zs pre d
    show (pre ++ s :: zs).getD d {}
      = if d + 1 < pre.length + 1 then (pre ++ zs).getD d {}
        else if d + 1 = pre.length + 1 then s else (p :: (pre ++ zs)).getD d {}
    rw [ih]
    by_cases h1 : d < pre.length
    · have h2 : d + 1 < pre.length + 1 := by omega
      simp only [h1, h2, ↓reduceIte]
    · have h2 : ¬ d + 1 < pre.length + 1 := by omega
      by_cases h3 : d = pre.length
      · subst h3
        simp only [Nat.lt_irrefl, ↓reduceIte]
      · have h4 : ¬ d + 1 = pre.length + 1 := by omega
        simp only [h1, h2, h3, h4, ↓reduceIte]
        obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        rfl

mutual

/-- A term with each value of the family `n` out given a term. -/
def Val.open (o : Opening) (n : Nat) : Val → Val
  | .lit v => .lit v
  | .var i => .var i
  | .bvar d i => if d = n then o.b i else if n < d then .bvar (d - 1) i else .bvar d i
  | .slot s => .slot s
  | .un u x => .un u (x.open o n)
  | .bin u x y => .bin u (x.open o n) (y.open o n)
  | .tri u x y z => .tri u (x.open o n) (y.open o n) (z.open o n)
  | .fop u fl x y => .fop u (fl.open o n) (x.open o n) (y.open o n)

def FlagsT.open (o : Opening) (n : Nat) : FlagsT → FlagsT
  | .lit f => .lit f
  | .var i => .var i
  | .bvar d => if d = n then o.f else if n < d then .bvar (d - 1) else .bvar d
  | .old => .old
  | .src u fl x y z => .src u (fl.open o n) (x.open o n) (y.open o n) (z.open o n)

end

mutual

theorem Val.den_open (ρ : Env) (o : Opening) (ho : o.Closed) (pre zs : List Fam) :
    (a : Val) → (a.open o pre.length).den { ρ with bound := pre ++ zs }
      = a.den { ρ with bound := pre ++ famOf ρ o :: zs }
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar d i => by
    show Val.den _ (if d = pre.length then o.b i else if pre.length < d then .bvar (d - 1) i
        else .bvar d i)
      = ((pre ++ famOf ρ o :: zs).getD d {}).vals i
    rw [insert_getD]
    by_cases h1 : d = pre.length
    · have h2 : ¬ d < pre.length := by omega
      simp only [h1, ↓reduceIte, Nat.lt_irrefl]
      exact Val.den_bound ρ _ _ (ho.b i)
    · by_cases h2 : d < pre.length
      · have h3 : ¬ pre.length < d := by omega
        simp only [h1, h2, h3, ↓reduceIte]
        rfl
      · have h3 : pre.length < d := by omega
        simp only [h1, h2, h3, ↓reduceIte]
        rfl
  | .slot _ => rfl
  | .un u x => by simp only [Val.open, Val.den, Val.den_open ρ o ho pre zs x]
  | .bin u x y => by
    simp only [Val.open, Val.den, Val.den_open ρ o ho pre zs x, Val.den_open ρ o ho pre zs y]
  | .tri u x y z => by
    simp only [Val.open, Val.den, Val.den_open ρ o ho pre zs x, Val.den_open ρ o ho pre zs y,
      Val.den_open ρ o ho pre zs z]
  | .fop u fl x y => by
    simp only [Val.open, Val.den, FlagsT.den_open ρ o ho pre zs fl,
      Val.den_open ρ o ho pre zs x, Val.den_open ρ o ho pre zs y]

theorem FlagsT.den_open (ρ : Env) (o : Opening) (ho : o.Closed) (pre zs : List Fam) :
    (f : FlagsT) → (f.open o pre.length).den { ρ with bound := pre ++ zs }
      = f.den { ρ with bound := pre ++ famOf ρ o :: zs }
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar d => by
    show FlagsT.den _ (if d = pre.length then o.f else if pre.length < d then .bvar (d - 1)
        else .bvar d)
      = ((pre ++ famOf ρ o :: zs).getD d {}).flags
    rw [insert_getD]
    by_cases h1 : d = pre.length
    · have h2 : ¬ d < pre.length := by omega
      simp only [h1, ↓reduceIte, Nat.lt_irrefl]
      exact FlagsT.den_bound ρ _ _ ho.f
    · by_cases h2 : d < pre.length
      · have h3 : ¬ pre.length < d := by omega
        simp only [h1, h2, h3, ↓reduceIte]
        rfl
      · have h3 : pre.length < d := by omega
        simp only [h1, h2, h3, ↓reduceIte]
        rfl
  | .old => rfl
  | .src u fl x y z => by
    simp only [FlagsT.open, FlagsT.den, FlagsT.den_open ρ o ho pre zs fl,
      Val.den_open ρ o ho pre zs x, Val.den_open ρ o ho pre zs y, Val.den_open ρ o ho pre zs z]

end

/-- The regions of a list, opened. -/
def heldOpen (o : Opening) (n : Nat) (held : List (Val × HeldS)) : List (Val × HeldS) :=
  held.map fun r => (r.1.open o n, ⟨r.2.size, r.2.slots.map fun p => (p.1, p.2.open o n)⟩)

theorem heldDen_open (ρ : Env) (o : Opening) (ho : o.Closed) (pre zs : List Fam)
    (held : List (Val × HeldS)) :
    ((heldOpen o pre.length held).map fun b =>
        (b.1.den { ρ with bound := pre ++ zs }, b.2.den { ρ with bound := pre ++ zs }))
      = held.map fun b => (b.1.den { ρ with bound := pre ++ famOf ρ o :: zs },
          b.2.den { ρ with bound := pre ++ famOf ρ o :: zs }) := by
  unfold heldOpen
  rw [List.map_map]
  refine List.map_congr_left fun r _ => ?_
  show ((r.1.open o pre.length).den { ρ with bound := pre ++ zs },
      (⟨r.2.size, (r.2.slots.map fun p => (p.1, p.2.open o pre.length)).map
        fun p => (p.1, p.2.den { ρ with bound := pre ++ zs })⟩ : Held))
    = (r.1.den { ρ with bound := pre ++ famOf ρ o :: zs },
        (⟨r.2.size, r.2.slots.map fun p =>
          (p.1, p.2.den { ρ with bound := pre ++ famOf ρ o :: zs })⟩ : Held))
  rw [Val.den_open ρ o ho pre zs, List.map_map]
  congr 2
  exact List.map_congr_left fun p _ => by
    show (p.1, (p.2.open o pre.length).den { ρ with bound := pre ++ zs }) = _
    rw [Val.den_open ρ o ho pre zs]

/-- Whatever else is held, opened: the regions to be written out, and what
is left. -/
def RestS.openHeld (o : Opening) (n : Nat) : RestS → List (Val × HeldS) × RestS
  | .bvar d => if d = n then (o.rest, o.tail) else if n < d then ([], .bvar (d - 1)) else ([], .bvar d)
  | r => ([], r)

theorem restDen_open (ρ : Env) (o : Opening) (ho : o.Closed) (pre zs : List Fam) (r : RestS) :
    ((r.openHeld o pre.length).1.map fun b =>
        (b.1.den { ρ with bound := pre ++ zs }, b.2.den { ρ with bound := pre ++ zs }))
        ++ restDen { ρ with bound := pre ++ zs } (r.openHeld o pre.length).2
      = restDen { ρ with bound := pre ++ famOf ρ o :: zs } r := by
  cases r with
  | none => rfl
  | name j => rfl
  | bvar d =>
    show ((if d = pre.length then (o.rest, o.tail) else if pre.length < d then ([], .bvar (d - 1))
          else ([], RestS.bvar d)).1.map fun b =>
        (b.1.den { ρ with bound := pre ++ zs }, b.2.den { ρ with bound := pre ++ zs }))
        ++ restDen { ρ with bound := pre ++ zs }
          (if d = pre.length then (o.rest, o.tail) else if pre.length < d then ([], .bvar (d - 1))
            else ([], RestS.bvar d)).2
      = ((pre ++ famOf ρ o :: zs).getD d {}).rest
    rw [insert_getD]
    by_cases h1 : d = pre.length
    · have h2 : ¬ d < pre.length := by omega
      simp only [h1, ↓reduceIte, Nat.lt_irrefl]
      rw [heldDen_bound ρ _ _ ho.rest, RestS.den_bound ρ _ _ ho.tail]
      rfl
    · by_cases h2 : d < pre.length
      · have h3 : ¬ pre.length < d := by omega
        simp only [h1, h2, h3, ↓reduceIte]
        rfl
      · have h3 : pre.length < d := by omega
        simp only [h1, h2, h3, ↓reduceIte]
        rfl

mutual

/-- What is known, opened: code wanting a family is one family further in. -/
def TyS.open (o : Opening) (n : Nat) : TyS → TyS
  | .any => .any
  | .ptr S w off => .ptr (S.open o n) w off
  | .ref tag w off => .ref tag w off
  | .nullable τ => .nullable (τ.open o n)
  | .orErr τ => .orErr (τ.open o n)
  | .str c => .str (c.open o n)
  | .atom i => .atom i
  | .range lo hi => .range lo hi
  | .arr c τ => .arr (c.open o n) (τ.open o n)
  | .upTo t strict => .upTo (t.open o n) strict
  | .code regs flags held known rest =>
    .code (regs.map (Val.open o (n + 1))) (flags.open o (n + 1))
      (heldOpen o (n + 1) held ++ (rest.openHeld o (n + 1)).1) (known.open o (n + 1))
      (rest.openHeld o (n + 1)).2

def ShapeS.open (o : Opening) (n : Nat) : ShapeS → ShapeS
  | .mk size vals => .mk size (vals.open o n)

def ValsS.open (o : Opening) (n : Nat) : ValsS → ValsS
  | .nil => .nil
  | .cons k τ rest => .cons k (τ.open o n) (rest.open o n)

def FactsS.open (o : Opening) (n : Nat) : FactsS → FactsS
  | .nil => .nil
  | .cons v τ rest => .cons (v.open o n) (τ.open o n) (rest.open o n)

end

mutual

theorem TyS.den_open (ρ : Env) (o : Opening) (ho : o.Closed) (pre zs : List Fam) :
    (τ : TyS) → (τ.open o pre.length).den { ρ with bound := pre ++ zs }
      = τ.den { ρ with bound := pre ++ famOf ρ o :: zs }
  | .any => rfl
  | .ptr S w off => by simp only [TyS.open, TyS.den, ShapeS.den_open ρ o ho pre zs S]
  | .ref _ _ _ => rfl
  | .nullable τ => by simp only [TyS.open, TyS.den, TyS.den_open ρ o ho pre zs τ]
  | .orErr τ => by simp only [TyS.open, TyS.den, TyS.den_open ρ o ho pre zs τ]
  | .str c => by simp only [TyS.open, TyS.den, Val.den_open ρ o ho pre zs c]
  | .atom _ => rfl
  | .range _ _ => rfl
  | .arr c τ => by
    simp only [TyS.open, TyS.den, Val.den_open ρ o ho pre zs c, TyS.den_open ρ o ho pre zs τ]
  | .upTo t _ => by simp only [TyS.open, TyS.den, Val.den_open ρ o ho pre zs t]
  | .code regs flags held known rest => by
    show Ty.code _ = Ty.code _
    congr 1
    funext z
    refine ctx_ext ?_ ?_ ?_ ?_
    · funext r
      show ((regs.map (Val.open o (pre.length + 1))).get r).den { ρ with bound := (z :: pre) ++ zs }
        = (regs.get r).den { ρ with bound := (z :: pre) ++ famOf ρ o :: zs }
      rw [Regs.get_map]
      exact Val.den_open ρ o ho (z :: pre) zs _
    · exact FlagsT.den_open ρ o ho (z :: pre) zs flags
    · show ((heldOpen o (z :: pre).length held ++ (rest.openHeld o (z :: pre).length).1).map
            fun b => (b.1.den { ρ with bound := (z :: pre) ++ zs },
              b.2.den { ρ with bound := (z :: pre) ++ zs }))
          ++ restDen { ρ with bound := (z :: pre) ++ zs } (rest.openHeld o (z :: pre).length).2
        = (held.map fun b => (b.1.den { ρ with bound := (z :: pre) ++ famOf ρ o :: zs },
            b.2.den { ρ with bound := (z :: pre) ++ famOf ρ o :: zs }))
          ++ restDen { ρ with bound := (z :: pre) ++ famOf ρ o :: zs } rest
      rw [List.map_append, List.append_assoc, heldDen_open ρ o ho (z :: pre) zs held,
        restDen_open ρ o ho (z :: pre) zs rest]
    · exact FactsS.den_open ρ o ho (z :: pre) zs known

theorem ShapeS.den_open (ρ : Env) (o : Opening) (ho : o.Closed) (pre zs : List Fam) :
    (S : ShapeS) → (S.open o pre.length).den { ρ with bound := pre ++ zs }
      = S.den { ρ with bound := pre ++ famOf ρ o :: zs }
  | .mk size vals => by simp only [ShapeS.open, ShapeS.den, ValsS.den_open ρ o ho pre zs vals]

theorem ValsS.den_open (ρ : Env) (o : Opening) (ho : o.Closed) (pre zs : List Fam) :
    (vs : ValsS) → (vs.open o pre.length).den { ρ with bound := pre ++ zs }
      = vs.den { ρ with bound := pre ++ famOf ρ o :: zs }
  | .nil => rfl
  | .cons k τ rest => by
    simp only [ValsS.open, ValsS.den, TyS.den_open ρ o ho pre zs τ,
      ValsS.den_open ρ o ho pre zs rest]

theorem FactsS.den_open (ρ : Env) (o : Opening) (ho : o.Closed) (pre zs : List Fam) :
    (fs : FactsS) → (fs.open o pre.length).den { ρ with bound := pre ++ zs }
      = fs.den { ρ with bound := pre ++ famOf ρ o :: zs }
  | .nil => rfl
  | .cons v τ rest => by
    simp only [FactsS.open, FactsS.den, Val.den_open ρ o ho pre zs v,
      TyS.den_open ρ o ho pre zs τ, FactsS.den_open ρ o ho pre zs rest]

end

def FactsS.toList : FactsS → List (Val × TyS)
  | .nil => []
  | .cons v τ rest => (v, τ) :: rest.toList

theorem FactsS.den_toList (ρ : Env) :
    (fs : FactsS) → fs.den ρ = fs.toList.map fun f => (f.1.den ρ, f.2.den ρ)
  | .nil => rfl
  | .cons v τ rest => by
    simp only [FactsS.den, FactsS.toList, List.map_cons, FactsS.den_toList ρ rest]

/-- The contexts a value is known to be code wanting, as a context whose
terms may mention the family's values. -/
def codeCtx (regs : Regs Val) (flags : FlagsT) (held : List (Val × HeldS)) (known : FactsS)
    (rest : RestS) : CtxS :=
  ⟨regs, flags, held, known.toList, rest⟩

/-- What that knowledge stands for is code wanting what the context stands
for, at each of the family's values. -/
theorem code_den (ρ : Env) (regs : Regs Val) (flags : FlagsT) (held : List (Val × HeldS))
    (known : FactsS) (rest : RestS) :
    (TyS.code regs flags held known rest).den ρ
      = .code fun z => (codeCtx regs flags held known rest).den { ρ with bound := z :: ρ.bound } := by
  show Ty.code _ = Ty.code _
  congr 1
  funext z
  refine ctx_ext rfl rfl rfl ?_
  exact FactsS.den_toList _ known

/-- A context with each value of the nearest family given a term. -/
def CtxS.open (o : Opening) (Γ : CtxS) : CtxS where
  regs := Γ.regs.map (Val.open o 0)
  flags := Γ.flags.open o 0
  held := heldOpen o 0 Γ.held ++ (Γ.rest.openHeld o 0).1
  known := Γ.known.map fun f => (f.1.open o 0, f.2.open o 0)
  rest := (Γ.rest.openHeld o 0).2

/-- **It stands for the member of the family at the values the terms stand
for.** -/
theorem CtxS.den_open (ρ : Env) (o : Opening) (ho : o.Closed) (Γ : CtxS) :
    (Γ.open o).den ρ = Γ.den { ρ with bound := famOf ρ o :: ρ.bound } := by
  refine ctx_ext ?_ ?_ ?_ ?_
  · funext r
    show ((Γ.regs.map (Val.open o 0)).get r).den ρ = _
    rw [Regs.get_map]
    exact Val.den_open ρ o ho [] ρ.bound _
  · exact FlagsT.den_open ρ o ho [] ρ.bound _
  · show (heldOpen o 0 Γ.held ++ (Γ.rest.openHeld o 0).1).map (fun b => (b.1.den ρ, b.2.den ρ))
        ++ restDen ρ (Γ.rest.openHeld o 0).2
      = Γ.held.map _ ++ restDen { ρ with bound := famOf ρ o :: ρ.bound } Γ.rest
    rw [List.map_append, List.append_assoc]
    have h1 := heldDen_open ρ o ho [] ρ.bound Γ.held
    have h2 := restDen_open ρ o ho [] ρ.bound Γ.rest
    exact congr (congrArg _ h1) h2
  · show (Γ.known.map _).map _ = Γ.known.map _
    rw [List.map_map]
    exact List.map_congr_left fun f _ => by
      show ((f.1.open o 0).den ρ, (f.2.open o 0).den ρ)
        = (f.1.den { ρ with bound := famOf ρ o :: ρ.bound },
            f.2.den { ρ with bound := famOf ρ o :: ρ.bound })
      rw [show (f.1.open o 0).den ρ = _ from Val.den_open ρ o ho [] ρ.bound f.1,
        show (f.2.open o 0).den ρ = _ from TyS.den_open ρ o ho [] ρ.bound f.2]
      rfl

end TypedAsm.U
