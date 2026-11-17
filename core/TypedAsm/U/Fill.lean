import TypedAsm.U.Term

/-!
# An instruction's terms, with a context's put in

An instruction's description is written in terms that stand for the things
it computes with: the registers it uses, the bytes it reads, an address,
the flags before it. To take the instruction in a context, the context's
terms for those are put in. What results stands, in a setting of the
names, for what the description stood for with those things being what the
context's terms stand for.
-/

namespace TypedAsm.U

open TypedAsm

/-- The terms to put in: one for each thing an instruction computes with,
and one for the flags before it. -/
structure Filling where
  slot : Slot → Val
  old : FlagsT

/-- The setting in which an instruction's terms stand for what the terms
put in stand for. -/
def Env.filled (ρ : Env) (σ : Filling) : Env :=
  { ρ with slot := fun s => (σ.slot s).den ρ, old := σ.old.den ρ }

mutual

def Val.fill (σ : Filling) : Val → Val
  | .lit v => .lit v
  | .var i => .var i
  | .bvar d i => .bvar d i
  | .slot s => σ.slot s
  | .un o a => .un o (a.fill σ)
  | .bin o a b => .bin o (a.fill σ) (b.fill σ)
  | .tri o a b c => .tri o (a.fill σ) (b.fill σ) (c.fill σ)
  | .fop o fl a b => .fop o (fl.fill σ) (a.fill σ) (b.fill σ)
  | .app o a b => .app o (a.fill σ) (b.fill σ)

def FlagsT.fill (σ : Filling) : FlagsT → FlagsT
  | .lit f => .lit f
  | .var i => .var i
  | .bvar d => .bvar d
  | .old => σ.old
  | .src o fl a b c => .src o (fl.fill σ) (a.fill σ) (b.fill σ) (c.fill σ)

end

mutual

/-- **A term with a context's terms put in stands for what it stood for
with its slots being what those stand for.** -/
theorem Val.den_fill (ρ : Env) (σ : Filling) : (a : Val) → (a.fill σ).den ρ = a.den (ρ.filled σ)
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar _ _ => rfl
  | .slot _ => rfl
  | .un o a => by simp only [Val.fill, Val.den, Val.den_fill ρ σ a]
  | .bin o a b => by simp only [Val.fill, Val.den, Val.den_fill ρ σ a, Val.den_fill ρ σ b]
  | .tri o a b c => by
    simp only [Val.fill, Val.den, Val.den_fill ρ σ a, Val.den_fill ρ σ b, Val.den_fill ρ σ c]
  | .fop o fl a b => by
    simp only [Val.fill, Val.den, FlagsT.den_fill ρ σ fl, Val.den_fill ρ σ a, Val.den_fill ρ σ b]
  | .app o a b => by
    simp only [Val.fill, Val.den, Val.den_fill ρ σ a, Val.den_fill ρ σ b]
    rfl

theorem FlagsT.den_fill (ρ : Env) (σ : Filling) :
    (f : FlagsT) → (f.fill σ).den ρ = f.den (ρ.filled σ)
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar _ => rfl
  | .old => rfl
  | .src o fl a b c => by
    simp only [FlagsT.fill, FlagsT.den, FlagsT.den_fill ρ σ fl, Val.den_fill ρ σ a,
      Val.den_fill ρ σ b, Val.den_fill ρ σ c]

end

/-! ## Terms of an instruction's description only -/

mutual

/-- Whether a term speaks only of what an instruction computes with: of no
name, and of no family's value. An instruction's description is such. -/
def Val.slotOnly : Val → Bool
  | .lit _ => true
  | .slot _ => true
  | .un _ a => a.slotOnly
  | .bin _ a b => a.slotOnly && b.slotOnly
  | .tri _ a b c => a.slotOnly && b.slotOnly && c.slotOnly
  | .fop _ fl a b => fl.slotOnly && a.slotOnly && b.slotOnly
  | _ => false

def FlagsT.slotOnly : FlagsT → Bool
  | .lit _ => true
  | .old => true
  | .src _ fl a b c => fl.slotOnly && a.slotOnly && b.slotOnly && c.slotOnly
  | _ => false

end

mutual

/-- Such a term stands for the same in any two settings in which the things
an instruction computes with are the same. -/
theorem Val.den_slots {ρ₁ ρ₂ : Env} (hs : ρ₁.slot = ρ₂.slot) (ho : ρ₁.old = ρ₂.old) :
    (a : Val) → a.slotOnly = true → a.den ρ₁ = a.den ρ₂
  | .lit _, _ => rfl
  | .slot s, _ => by
    show ρ₁.slot s = ρ₂.slot s
    rw [hs]
  | .un o a, h => by
    simp only [Val.slotOnly] at h
    simp only [Val.den, Val.den_slots hs ho a h]
  | .bin o a b, h => by
    simp only [Val.slotOnly, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_slots hs ho a h.1, Val.den_slots hs ho b h.2]
  | .tri o a b c, h => by
    simp only [Val.slotOnly, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_slots hs ho a h.1.1, Val.den_slots hs ho b h.1.2,
      Val.den_slots hs ho c h.2]
  | .fop o fl a b, h => by
    simp only [Val.slotOnly, Bool.and_eq_true] at h
    simp only [Val.den, FlagsT.den_slots hs ho fl h.1.1, Val.den_slots hs ho a h.1.2,
      Val.den_slots hs ho b h.2]
  | .var _, h => nomatch h
  | .bvar _ _, h => nomatch h

theorem FlagsT.den_slots {ρ₁ ρ₂ : Env} (hs : ρ₁.slot = ρ₂.slot) (ho : ρ₁.old = ρ₂.old) :
    (f : FlagsT) → f.slotOnly = true → f.den ρ₁ = f.den ρ₂
  | .lit _, _ => rfl
  | .old, _ => ho
  | .src o fl a b c, h => by
    simp only [FlagsT.slotOnly, Bool.and_eq_true] at h
    simp only [FlagsT.den, FlagsT.den_slots hs ho fl h.1.1.1, Val.den_slots hs ho a h.1.1.2,
      Val.den_slots hs ho b h.1.2, Val.den_slots hs ho c h.2]
  | .var _, h => nomatch h
  | .bvar _, h => nomatch h

end

end TypedAsm.U
