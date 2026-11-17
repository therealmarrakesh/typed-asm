import TypedAsm.U.Fresh
import TypedAsm.U.Closed

/-!
# What is known that mentions nothing from outside

Knowledge written with no name, no value of a family outside it and
nothing left unwritten in it stands for the same thing whatever names stand
for. The shapes of a program's kinds, and what it says of its static data,
are to be so. Code wanting a family is so where it mentions only the
family's own values.
-/

namespace TypedAsm.U

open TypedAsm

/-- A setting with nothing left unwritten in it: what is known but not
written out, what an instruction computes with, and the flags before one,
as in the empty setting. -/
def Env.bare (ρ : Env) : Env :=
  { ρ with ty := ({} : Env).ty, slot := ({} : Env).slot, old := ({} : Env).old }

mutual

/-- Whether a term has nothing of an instruction's own description in it. -/
def Val.plain : Val → Bool
  | .lit _ => true
  | .var _ => true
  | .bvar _ _ => true
  | .slot _ => false
  | .un _ a => a.plain
  | .bin _ a b => a.plain && b.plain
  | .tri _ a b c => a.plain && b.plain && c.plain
  | .fop _ fl a b => fl.plain && a.plain && b.plain

def FlagsT.plain : FlagsT → Bool
  | .lit _ => true
  | .var _ => true
  | .bvar _ => true
  | .old => false
  | .src _ fl a b c => fl.plain && a.plain && b.plain && c.plain

end

mutual

theorem Val.den_bare (ρ : Env) : (a : Val) → a.plain = true → a.den ρ.bare = a.den ρ
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar _ _, _ => rfl
  | .slot _, h => nomatch h
  | .un o a, h => by
    simp only [Val.plain] at h
    simp only [Val.den, Val.den_bare ρ a h]
  | .bin o a b, h => by
    simp only [Val.plain, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_bare ρ a h.1, Val.den_bare ρ b h.2]
  | .tri o a b c, h => by
    simp only [Val.plain, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_bare ρ a h.1.1, Val.den_bare ρ b h.1.2, Val.den_bare ρ c h.2]
  | .fop o fl a b, h => by
    simp only [Val.plain, Bool.and_eq_true] at h
    simp only [Val.den, FlagsT.den_bare ρ fl h.1.1, Val.den_bare ρ a h.1.2, Val.den_bare ρ b h.2]

theorem FlagsT.den_bare (ρ : Env) : (f : FlagsT) → f.plain = true → f.den ρ.bare = f.den ρ
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar _, _ => rfl
  | .old, h => nomatch h
  | .src o fl a b c, h => by
    simp only [FlagsT.plain, Bool.and_eq_true] at h
    simp only [FlagsT.den, FlagsT.den_bare ρ fl h.1.1.1, Val.den_bare ρ a h.1.1.2,
      Val.den_bare ρ b h.1.2, Val.den_bare ρ c h.2]

end

/-- Whether the regions of a list have nothing of an instruction's own
description in them. -/
def heldPlain (held : List (Val × HeldS)) : Bool :=
  held.all fun b => b.1.plain && b.2.slots.all fun p => p.2.plain

theorem heldDen_bare (ρ : Env) (held : List (Val × HeldS)) (h : heldPlain held = true) :
    (held.map fun b => (b.1.den ρ.bare, b.2.den ρ.bare)) = held.map fun b => (b.1.den ρ, b.2.den ρ) := by
  refine List.map_congr_left fun b hb => ?_
  have hbk := List.all_eq_true.mp h b hb
  rw [Bool.and_eq_true] at hbk
  show (b.1.den ρ.bare, (⟨b.2.size, b.2.slots.map fun p => (p.1, p.2.den ρ.bare)⟩ : Held))
    = (b.1.den ρ, ⟨b.2.size, b.2.slots.map fun p => (p.1, p.2.den ρ)⟩)
  rw [Val.den_bare ρ _ hbk.1]
  congr 2
  exact List.map_congr_left fun p hp => by
    rw [Val.den_bare ρ _ (List.all_eq_true.mp hbk.2 p hp)]

theorem restDen_bare (ρ : Env) (r : RestS) : restDen ρ.bare r = restDen ρ r := by
  cases r <;> rfl

mutual

/-- Whether what is known has nothing left unwritten in it, and nothing of
an instruction's own description. -/
def TyS.plain : TyS → Bool
  | .ptr S _ _ => S.plain
  | .nullable τ => τ.plain
  | .orErr τ => τ.plain
  | .str c => c.plain
  | .arr c τ => c.plain && τ.plain
  | .atom _ => false
  | .code regs flags held known _ =>
    (regs.map (·.plain) == allTrue) && flags.plain && heldPlain held && known.plain
  | _ => true

def ShapeS.plain : ShapeS → Bool
  | .mk _ vals => vals.plain

def ValsS.plain : ValsS → Bool
  | .nil => true
  | .cons _ τ rest => τ.plain && rest.plain

def FactsS.plain : FactsS → Bool
  | .nil => true
  | .cons v τ rest => v.plain && τ.plain && rest.plain

end

mutual

theorem TyS.den_bare (ρ : Env) : (τ : TyS) → τ.plain = true → τ.den ρ.bare = τ.den ρ
  | .any, _ => rfl
  | .ptr S w off, h => by
    simp only [TyS.den, ShapeS.den_bare ρ S (by simpa only [TyS.plain] using h)]
  | .ref _ _ _, _ => rfl
  | .nullable τ, h => by
    simp only [TyS.den, TyS.den_bare ρ τ (by simpa only [TyS.plain] using h)]
  | .orErr τ, h => by
    simp only [TyS.den, TyS.den_bare ρ τ (by simpa only [TyS.plain] using h)]
  | .str c, h => by
    simp only [TyS.den, Val.den_bare ρ c (by simpa only [TyS.plain] using h)]
  | .atom _, h => nomatch h
  | .range _ _, _ => rfl
  | .arr c τ, h => by
    simp only [TyS.plain, Bool.and_eq_true] at h
    simp only [TyS.den, Val.den_bare ρ c h.1, TyS.den_bare ρ τ h.2]
  | .code regs flags held known rest, h => by
    simp only [TyS.plain, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩ := h
    show Ty.code _ = Ty.code _
    congr 1
    funext z
    refine ctx_ext ?_ ?_ ?_ ?_
    · funext r
      exact Val.den_bare { ρ with bound := z :: ρ.bound } _ (Regs.all_of_map regs hr r)
    · exact FlagsT.den_bare { ρ with bound := z :: ρ.bound } _ hf
    · show (held.map fun b => (b.1.den (Env.bare { ρ with bound := z :: ρ.bound }),
            b.2.den (Env.bare { ρ with bound := z :: ρ.bound })))
          ++ restDen (Env.bare { ρ with bound := z :: ρ.bound }) rest
        = (held.map fun b => (b.1.den { ρ with bound := z :: ρ.bound },
            b.2.den { ρ with bound := z :: ρ.bound }))
          ++ restDen { ρ with bound := z :: ρ.bound } rest
      rw [heldDen_bare _ held hh, restDen_bare]
    · exact FactsS.den_bare { ρ with bound := z :: ρ.bound } known hkn

theorem ShapeS.den_bare (ρ : Env) : (S : ShapeS) → S.plain = true → S.den ρ.bare = S.den ρ
  | .mk size vals, h => by
    simp only [ShapeS.den, ValsS.den_bare ρ vals (by simpa only [ShapeS.plain] using h)]

theorem ValsS.den_bare (ρ : Env) : (vs : ValsS) → vs.plain = true → vs.den ρ.bare = vs.den ρ
  | .nil, _ => rfl
  | .cons o τ rest, h => by
    simp only [ValsS.plain, Bool.and_eq_true] at h
    simp only [ValsS.den, TyS.den_bare ρ τ h.1, ValsS.den_bare ρ rest h.2]

theorem FactsS.den_bare (ρ : Env) : (fs : FactsS) → fs.plain = true → fs.den ρ.bare = fs.den ρ
  | .nil, _ => rfl
  | .cons v τ rest, h => by
    simp only [FactsS.plain, Bool.and_eq_true] at h
    simp only [FactsS.den, Val.den_bare ρ v h.1.1, TyS.den_bare ρ τ h.1.2,
      FactsS.den_bare ρ rest h.2]

end

/-- Whether what is known mentions nothing from outside: no name, no value
of a family outside it, nothing left unwritten. -/
def TyS.ground (τ : TyS) : Bool := τ.under 0 && τ.closedAt 0 && τ.plain

/-- The same, of a shape. -/
def ShapeS.ground (S : ShapeS) : Bool := S.under 0 && S.closedAt 0 && S.plain

theorem sameBelow_bare (ρ₁ ρ₂ : Env) :
    Env.SameBelow 0 { ρ₁.bare with bound := [] } { ρ₂.bare with bound := [] } :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩

/-- **What mentions nothing from outside stands for the same whatever
names stand for.** -/
theorem TyS.den_ground (ρ₁ ρ₂ : Env) (τ : TyS) (h : τ.ground = true) : τ.den ρ₁ = τ.den ρ₂ := by
  simp only [TyS.ground, Bool.and_eq_true] at h
  obtain ⟨⟨hu, hc⟩, hp⟩ := h
  rw [← TyS.den_bare ρ₁ τ hp, ← TyS.den_bare ρ₂ τ hp, ← TyS.den_bound ρ₁.bare [] τ hc,
    ← TyS.den_bound ρ₂.bare [] τ hc]
  exact TyS.den_under (sameBelow_bare ρ₁ ρ₂) τ hu

theorem ShapeS.den_ground (ρ₁ ρ₂ : Env) (S : ShapeS) (h : S.ground = true) :
    S.den ρ₁ = S.den ρ₂ := by
  simp only [ShapeS.ground, Bool.and_eq_true] at h
  obtain ⟨⟨hu, hc⟩, hp⟩ := h
  have b1 := ShapeS.den_agree ρ₁.bare 0 [] ρ₁.bare.bound
    (fun _ hd => absurd hd (Nat.not_lt_zero _)) S hc
  have b2 := ShapeS.den_agree ρ₂.bare 0 [] ρ₂.bare.bound
    (fun _ hd => absurd hd (Nat.not_lt_zero _)) S hc
  rw [← ShapeS.den_bare ρ₁ S hp, ← ShapeS.den_bare ρ₂ S hp, ← b1, ← b2]
  exact ShapeS.den_under (sameBelow_bare ρ₁ ρ₂) S hu

end TypedAsm.U
