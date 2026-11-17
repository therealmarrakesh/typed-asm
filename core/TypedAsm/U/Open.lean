import TypedAsm.U.Subst

/-!
# A family of contexts, at particular values

That a value is code wanting a family of contexts is known as data: the
contexts as terms, the values the family ranges over having names of their
own. To use it, each of those names is given a term: the context that
results stands for the member of the family at the values the terms stand
for.
-/

namespace TypedAsm.U

open TypedAsm

/-- A term for each of the values a family ranges over, and one for the
flags. -/
structure Opening where
  b : Nat → Val
  f : FlagsT

/-- The values of a family that given terms stand for: the first for the
flags. -/
def seqOf (ρ : Env) (o : Opening) : Seq
  | 0 => (o.f.den ρ).bits
  | j + 1 => (o.b j).den ρ

mutual

/-- A term with each of a family's values given a term. -/
def Val.open (o : Opening) : Val → Val
  | .lit v => .lit v
  | .var i => .var i
  | .bvar i => o.b i
  | .add x y => .add (x.open o) (y.open o)
  | .shl x k => .shl (x.open o) k
  | .out i k x y c fl next ea cell =>
    .out i k (x.open o) (y.open o) (c.open o) (fl.open o) next (ea.open o)
      (cell.open o)
  | .stored i x y c fl next ea cell =>
    .stored i (x.open o) (y.open o) (c.open o) (fl.open o) next (ea.open o)
      (cell.open o)
  | .goes i x y c fl next ea cell =>
    .goes i (x.open o) (y.open o) (c.open o) (fl.open o) next (ea.open o)
      (cell.open o)

def FlagsT.open (o : Opening) : FlagsT → FlagsT
  | .lit f => .lit f
  | .var i => .var i
  | .bvar => o.f
  | .out i x y c fl next ea cell =>
    .out i (x.open o) (y.open o) (c.open o) (fl.open o) next (ea.open o)
      (cell.open o)

end

mutual

theorem Val.den_open (ρ : Env) (o : Opening) :
    (a : Val) → (a.open o).den ρ = a.den { ρ with bound := seqOf ρ o }
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar _ => rfl
  | .add x y => by
    simp only [Val.open, Val.den, Val.den_open ρ o x, Val.den_open ρ o y]
  | .shl x s => by simp only [Val.open, Val.den, Val.den_open ρ o x]
  | .out i j x y c fl next ea cell => by
    simp only [Val.open, Val.den, Val.den_open ρ o x, Val.den_open ρ o y,
      Val.den_open ρ o c, FlagsT.den_open ρ o fl, Val.den_open ρ o ea,
      Val.den_open ρ o cell]
  | .stored i x y c fl next ea cell => by
    simp only [Val.open, Val.den, Val.den_open ρ o x, Val.den_open ρ o y,
      Val.den_open ρ o c, FlagsT.den_open ρ o fl, Val.den_open ρ o ea,
      Val.den_open ρ o cell]
  | .goes i x y c fl next ea cell => by
    simp only [Val.open, Val.den, Val.den_open ρ o x, Val.den_open ρ o y,
      Val.den_open ρ o c, FlagsT.den_open ρ o fl, Val.den_open ρ o ea,
      Val.den_open ρ o cell]

theorem FlagsT.den_open (ρ : Env) (o : Opening) :
    (f : FlagsT) → (f.open o).den ρ = f.den { ρ with bound := seqOf ρ o }
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar => (flagsOf_bits (o.f.den ρ)).symm
  | .out i x y c fl next ea cell => by
    simp only [FlagsT.open, FlagsT.den, Val.den_open ρ o x, Val.den_open ρ o y,
      Val.den_open ρ o c, FlagsT.den_open ρ o fl, Val.den_open ρ o ea,
      Val.den_open ρ o cell]

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
    (rest : Option Nat) : CtxS :=
  ⟨regs, flags, held, known.toList, rest⟩

/-- What that knowledge stands for is code wanting what the context stands
for, at each of the family's values. -/
theorem code_den (ρ : Env) (regs : Regs Val) (flags : FlagsT) (held : List (Val × HeldS))
    (known : FactsS) (rest : Option Nat) :
    (TyS.code regs flags held known rest).den ρ
      = .code fun z => (codeCtx regs flags held known rest).den { ρ with bound := z } := by
  show Ty.code _ = Ty.code _
  congr 1
  funext z
  refine ctx_ext rfl rfl rfl ?_
  exact FactsS.den_toList _ known

/-- A context with each of a family's values given a term. What is known
of values is left as it is: it mentions none of them. -/
def CtxS.open (o : Opening) (Γ : CtxS) : CtxS where
  regs := Γ.regs.map (Val.open o)
  flags := Γ.flags.open o
  held := Γ.held.map fun r => (r.1.open o, ⟨r.2.size, r.2.slots.map fun p => (p.1, p.2.open o)⟩)
  known := Γ.known.map fun f => (f.1.open o, f.2)
  rest := Γ.rest

/-- **It stands for the member of the family at the values the terms stand
for.** -/
theorem CtxS.den_open (ρ : Env) (o : Opening) (Γ : CtxS) :
    (Γ.open o).den ρ = Γ.den { ρ with bound := seqOf ρ o } := by
  refine ctx_ext ?_ ?_ ?_ ?_
  · funext r
    show ((Γ.regs.map (Val.open o)).get r).den ρ = _
    rw [Regs.get_map]
    exact Val.den_open ρ o _
  · exact FlagsT.den_open ρ o _
  · show (Γ.held.map _).map _ ++ restDen ρ Γ.rest = Γ.held.map _ ++ restDen _ Γ.rest
    have hrest : restDen ρ Γ.rest = restDen { ρ with bound := seqOf ρ o } Γ.rest := by
      cases Γ.rest <;> rfl
    rw [hrest, List.map_map]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    show ((r.1.open o).den ρ, (⟨r.2.size, (r.2.slots.map fun p => (p.1, p.2.open o)).map
        fun p => (p.1, p.2.den ρ)⟩ : Held))
      = (r.1.den { ρ with bound := seqOf ρ o },
          (⟨r.2.size, r.2.slots.map fun p => (p.1, p.2.den { ρ with bound := seqOf ρ o })⟩ : Held))
    rw [Val.den_open, List.map_map]
    congr 2
    exact List.map_congr_left fun p _ => by
      show (p.1, (p.2.open o).den ρ) = _
      rw [Val.den_open]
  · show (Γ.known.map _).map _ = Γ.known.map _
    rw [List.map_map]
    exact List.map_congr_left fun f _ => by
      show ((f.1.open o).den ρ, f.2.den ρ)
        = (f.1.den { ρ with bound := seqOf ρ o }, f.2.den { ρ with bound := seqOf ρ o })
      rw [Val.den_open, TyS.den_bound ρ (seqOf ρ o) f.2]

end TypedAsm.U
