import TypedAsm.U.SysStep
import TypedAsm.U.Publish

/-!
# Publishing a region, as a step on terms

A program says where a region it holds becomes a block others may point
into, and of what shape. The checker then sees that the region is held
whole, is of the shape's size, and holds at each typed place of the shape a
value that is of the type by what the context knows; and the context after
no longer holds the region, and knows its address to point to the block.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- Whether each typed value of a shape lies within so many bytes. -/
def ValsS.fitsIn (size : Nat) : ValsS → Bool
  | .nil => true
  | .cons o _ rest => decide (o + 8 ≤ size) && rest.fitsIn size

theorem ValsS.fitsIn_den (ρ : Env) {size : Nat} :
    (vs : ValsS) → vs.fitsIn size = true → ∀ q ∈ vs.den ρ, q.1 + 8 ≤ size
  | .nil, _, q, hq => nomatch hq
  | .cons o τ rest, h, q, hq => by
    simp only [ValsS.fitsIn, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact ValsS.fitsIn_den ρ rest h.2 q hq

/-- Whether a region holds, at each typed place of a shape, a value that is
of the type by what the context knows; a place that asks nothing needs
none. -/
def valsPub (Γ : CtxS) (S : HeldS) : ValsS → Bool
  | .nil => true
  | .cons o τ rest =>
    (τ == .any ||
      (match S.slotAt o with
       | some v => factFrom noEnt Γ.known (v, τ)
       | none => false)) && valsPub Γ S rest

theorem valsPub_sound (ρ : Env) {Γ : CtxS} {S : HeldS} :
    (vs : ValsS) → valsPub Γ S vs = true → ∀ q ∈ vs.den ρ, q.2 = .any ∨
      ∃ v, (q.1, v) ∈ (S.den ρ).vals ∧ ∀ (Ψ' : MemTy) (n : Nat),
        (∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) → HasTy fetch sys Ψ' n q.2 v
  | .nil, _, q, hq => nomatch hq
  | .cons o τ rest, h, q, hq => by
    simp only [valsPub, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · rcases h.1 with rfl | hs
      · exact .inl rfl
      · cases hv : S.slotAt o with
        | none => rw [hv] at hs; cases hs
        | some v =>
          rw [hv] at hs
          refine .inr ⟨v.den ρ, ?_, fun Ψ' n hg => factFrom_hasTy noEnt_sound ρ hs Ψ' n hg⟩
          show (o, v.den ρ) ∈ S.slots.map _
          exact List.mem_map.mpr ⟨(o, v), HeldS.slotAt_mem hv, rfl⟩
    · exact valsPub_sound ρ rest h.2 q hq

/-- What is known of a block's address besides its shape, as terms. -/
def tagFactsS (b : Val) : Option Nat → List (Val × TyS)
  | some t => [(b, .ref t true 0)]
  | none => []

/-- Whether a kind a block is to be of is, in the program's table, of the
block's shape. -/
def tagOk (kinds : Nat → Option ShapeS) (K : ShapeS) : Option Nat → Bool
  | some t => kinds t == some K
  | none => true

/-- **The context once the region at an address has become a block of a
shape**, and of a kind if one is given; nothing unless the region is held
whole, is of that size, and holds what the shape says. -/
def publishS (kinds : Nat → Option ShapeS) (Γ : CtxS) (b : Val) (K : ShapeS) (tag : Option Nat) :
    Option CtxS :=
  match findHeld b 0 Γ.held 0 with
  | some (j, base, S, o) =>
    if o == 0 && K.size == S.size && decide (0 < K.size) && K.vals.fitsIn K.size &&
        valsPub Γ S K.vals && tagOk kinds K tag then
      some { Γ with
        held := Γ.held.eraseIdx j
        known := (base, .ptr K true 0) :: (tagFactsS base tag ++ Γ.known) }
    else none
  | none => none

theorem publishS_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds)
    {Γ Γ' : CtxS} {b : Val} {K : ShapeS} {tag : Option Nat}
    (h : publishS kinds Γ b K tag = some Γ') :
    Publishes fetch sys Ψ (Γ.den ρ) (Γ'.den ρ) := by
  unfold publishS at h
  split at h
  · next j base S o hfind =>
    split at h
    · next hc =>
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨ho, hsz⟩, hpos⟩, hfit⟩, hvals⟩, htag⟩ := hc
      obtain ⟨i, hi, hl, _, _⟩ := findHeld_spec (ρ := ρ) Γ.held 0 hfind
      have hji : j = i := by omega
      subst hji
      have hjlt : j < (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)).length := by
        rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hl).1
      have hP := Publishes.region (fetch := fetch) (sys := sys) (Ψ := Ψ) (K := K.den ρ) tag
        (CtxS.held_den ρ Γ hl) (by rw [ShapeS.den_size]; exact hpos)
        (by rw [ShapeS.den_size]; exact hsz)
        (by rw [ShapeS.den_vals, ShapeS.den_size]; exact ValsS.fitsIn_den ρ K.vals hfit)
        (by rw [ShapeS.den_vals]; exact valsPub_sound ρ K.vals hvals)
        (fun t ht => by
          subst ht
          exact hk ρ t K (by simpa only [tagOk, beq_iff_eq] using htag))
      have e : CtxS.den ρ { Γ with
            held := Γ.held.eraseIdx j
            known := (base, .ptr K true 0) :: (tagFactsS base tag ++ Γ.known) }
          = { Γ.den ρ with
              held := (Γ.den ρ).held.eraseIdx j
              known := (base.den ρ, Ty.ptr (K.den ρ) true 0) ::
                (tagFacts (base.den ρ) tag ++ (Γ.den ρ).known) } := by
        refine ctx_ext rfl rfl ?_ ?_
        · show (Γ.held.eraseIdx j).map (fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest
            = ((Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest).eraseIdx j
          rw [List.eraseIdx_append_of_lt_length hjlt, map_eraseIdx]
        · show (base.den ρ, Ty.ptr (K.den ρ) true 0) ::
              (tagFactsS base tag ++ Γ.known).map (fun f => (f.1.den ρ, f.2.den ρ)) = _
          rw [List.map_append]
          cases tag <;> rfl
      rw [e]
      exact hP
    · cases h
  · cases h

end TypedAsm.U
