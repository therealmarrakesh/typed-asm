import TypedAsm.U.Find

/-!
# Names not yet used

Where a step learns of a value it cannot write as a term of what it has,
bytes read whose value the context does not say, the value is given a name
no term yet mentions. What the terms there were stand for does not turn on
what the new name stands for; that is what "not yet mentioned" buys.
-/

namespace TypedAsm.U

open TypedAsm

/-- The names with the `k`th given a value. -/
def Env.setVal (ρ : Env) (k : Nat) (x : BitVec 64) : Env :=
  { ρ with val := fun i => if i = k then x else ρ.val i }

theorem Env.setVal_get_lt (ρ : Env) (k : Nat) (x : BitVec 64) {i : Nat} (h : i < k) :
    (ρ.setVal k x).val i = ρ.val i := by
  show (if i = k then x else ρ.val i) = ρ.val i
  simp only [show i ≠ k by omega, ↓reduceIte]

theorem Env.setVal_get_self (ρ : Env) (k : Nat) (x : BitVec 64) : (ρ.setVal k x).val k = x := by
  show (if k = k then x else ρ.val k) = x
  simp only [↓reduceIte]

mutual

/-- Whether a term mentions only names below `k`. -/
def Val.under (k : Nat) : Val → Bool
  | .lit _ => true
  | .var i => decide (i < k)
  | .bvar _ => true
  | .add a b => a.under k && b.under k
  | .shl a _ => a.under k
  | .out _ _ a b c fl _ ea cell =>
    a.under k && b.under k && c.under k && fl.under k && ea.under k && cell.under k
  | .stored _ a b c fl _ ea cell =>
    a.under k && b.under k && c.under k && fl.under k && ea.under k && cell.under k
  | .goes _ a b c fl _ ea cell =>
    a.under k && b.under k && c.under k && fl.under k && ea.under k && cell.under k

def FlagsT.under (k : Nat) : FlagsT → Bool
  | .lit _ => true
  | .var _ => true
  | .bvar => true
  | .out _ a b c fl _ ea cell =>
    a.under k && b.under k && c.under k && fl.under k && ea.under k && cell.under k

end

mutual

/-- A term that mentions only names below `k` stands for what it did,
whatever the `k`th is given. -/
theorem Val.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (a : Val) → a.under k = true → a.den (ρ.setVal k x) = a.den ρ
  | .lit _, _ => rfl
  | .bvar _, _ => rfl
  | .var i, h => by
    simp only [Val.under, decide_eq_true_eq] at h
    exact Env.setVal_get_lt ρ k x h
  | .add a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_setVal ρ k x a h.1, Val.den_setVal ρ k x b h.2]
  | .shl a s, h => by
    simp only [Val.under] at h
    simp only [Val.den, Val.den_setVal ρ k x a h]
  | .out i j a b c fl next ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_setVal ρ k x a ha, Val.den_setVal ρ k x b hb,
      Val.den_setVal ρ k x c hc, FlagsT.den_setVal ρ k x fl hf, Val.den_setVal ρ k x ea he,
      Val.den_setVal ρ k x cell hcell]
  | .stored i a b c fl next ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_setVal ρ k x a ha, Val.den_setVal ρ k x b hb,
      Val.den_setVal ρ k x c hc, FlagsT.den_setVal ρ k x fl hf, Val.den_setVal ρ k x ea he,
      Val.den_setVal ρ k x cell hcell]
  | .goes i a b c fl next ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_setVal ρ k x a ha, Val.den_setVal ρ k x b hb,
      Val.den_setVal ρ k x c hc, FlagsT.den_setVal ρ k x fl hf, Val.den_setVal ρ k x ea he,
      Val.den_setVal ρ k x cell hcell]

theorem FlagsT.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (f : FlagsT) → f.under k = true → f.den (ρ.setVal k x) = f.den ρ
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar, _ => rfl
  | .out i a b c fl next ea cell, h => by
    simp only [FlagsT.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [FlagsT.den, Val.den_setVal ρ k x a ha, Val.den_setVal ρ k x b hb,
      Val.den_setVal ρ k x c hc, FlagsT.den_setVal ρ k x fl hf, Val.den_setVal ρ k x ea he,
      Val.den_setVal ρ k x cell hcell]

end

mutual

/-- What is known of a value, as data, mentions no value: it stands for
the same whatever a value's name is given. -/
theorem TyS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (τ : TyS) → τ.den (ρ.setVal k x) = τ.den ρ
  | .any => rfl
  | .ptr S w off => by simp only [TyS.den, ShapeS.den_setVal ρ k x S]
  | .ref _ _ _ => rfl
  | .nullable τ => by simp only [TyS.den, TyS.den_setVal ρ k x τ]
  | .orErr τ => by simp only [TyS.den, TyS.den_setVal ρ k x τ]
  | .str _ => rfl
  | .atom _ => rfl

theorem ShapeS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (S : ShapeS) → S.den (ρ.setVal k x) = S.den ρ
  | .mk size vals => by simp only [ShapeS.den, ValsS.den_setVal ρ k x vals]

theorem ValsS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (vs : ValsS) → vs.den (ρ.setVal k x) = vs.den ρ
  | .nil => rfl
  | .cons o τ rest => by
    simp only [ValsS.den, TyS.den_setVal ρ k x τ, ValsS.den_setVal ρ k x rest]

end

/-- Whether a context mentions only names below `k`. -/
def CtxS.under (k : Nat) (Γ : CtxS) : Bool :=
  (Γ.regs.map (·.under k)) == ⟨true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true⟩ && Γ.flags.under k &&
  (Γ.held.all fun b => b.1.under k && b.2.slots.all fun p => p.2.under k) &&
  Γ.known.all fun f => f.1.under k

theorem CtxS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (Γ : CtxS) (h : Γ.under k = true) :
    Γ.den (ρ.setVal k x) = Γ.den ρ := by
  simp only [CtxS.under, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩ := h
  have hreg : ∀ r, (Γ.regs.get r).under k = true := fun r => by
    have h1 : (Γ.regs.map (·.under k)).get r = (Γ.regs.get r).under k := Regs.get_map _ _ r
    rw [← h1, hr]
    cases r <;> rfl
  refine ctx_ext ?_ ?_ ?_ ?_
  · funext r
    exact Val.den_setVal ρ k x _ (hreg r)
  · exact FlagsT.den_setVal ρ k x _ hf
  · show Γ.held.map _ ++ restDen (ρ.setVal k x) Γ.rest = Γ.held.map _ ++ restDen ρ Γ.rest
    have hrest : restDen (ρ.setVal k x) Γ.rest = restDen ρ Γ.rest := by cases Γ.rest <;> rfl
    rw [hrest]
    congr 1
    refine List.map_congr_left fun b hb => ?_
    have hbk := hh b hb
    show (b.1.den _, HeldS.den _ b.2) = (b.1.den ρ, HeldS.den ρ b.2)
    rw [Val.den_setVal ρ k x _ hbk.1]
    congr 1
    unfold HeldS.den
    congr 1
    exact List.map_congr_left fun p hp => by rw [Val.den_setVal ρ k x _ (hbk.2 p hp)]
  · show Γ.known.map _ = Γ.known.map _
    refine List.map_congr_left fun f hf' => ?_
    show (f.1.den _, f.2.den _) = (f.1.den ρ, f.2.den ρ)
    rw [Val.den_setVal ρ k x _ (hkn f hf'), TyS.den_setVal]

end TypedAsm.U
