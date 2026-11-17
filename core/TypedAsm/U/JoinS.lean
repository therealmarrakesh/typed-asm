import TypedAsm.U.RegardS

/-!
# Regions end to end, taken as one

Before one context is compared with another, the regions it holds that lie
end to end are taken as one: a region the other holds may then be a part of
what were several. Which two to take is found by looking; that they may be
put first is decided as any regard is; and that they are then one is
`Regards.join`.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- One region followed by another, as one. -/
def HeldS.append (S T : HeldS) : HeldS :=
  ⟨S.size + T.size, S.slots ++ T.slots.map fun p => (S.size + p.1, p.2)⟩

theorem HeldS.append_den (ρ : Env) (S T : HeldS) :
    (S.append T).den ρ = (S.den ρ).append (T.den ρ) := by
  show (⟨S.size + T.size, (S.slots ++ T.slots.map fun p => (S.size + p.1, p.2)).map
      fun p => (p.1, p.2.den ρ)⟩ : Held)
    = ⟨S.size + T.size, (S.slots.map fun p => (p.1, p.2.den ρ)) ++
        (T.slots.map fun p => (p.1, p.2.den ρ)).map fun p => (S.size + p.1, p.2)⟩
  rw [List.map_append, List.map_map, List.map_map]
  rfl

/-- Two regions of a list, the second starting where the first ends. -/
def findPair (G : List (Val × HeldS)) : Option (Nat × Nat) :=
  (List.range G.length).findSome? fun i =>
    (List.range G.length).findSome? fun j =>
      match G[i]?, G[j]? with
      | some gi, some gj =>
        if i != j && offsetFrom gj.1 gi.1 == some gi.2.size then some (i, j) else none
      | _, _ => none

/-- A context with two regions that lie end to end taken as one, if it
holds two such. -/
def joinStep (Γ : CtxS) : Option CtxS :=
  match findPair Γ.held with
  | some (i, j) =>
    match Γ.held[i]?, Γ.held[j]? with
    | some gi, some gj =>
      let rest := (Γ.held.eraseIdx (max i j)).eraseIdx (min i j)
      if regardS Γ { Γ with held := gi :: gj :: rest } &&
          offsetFrom gj.1 gi.1 == some gi.2.size && decide (gi.2.size + gj.2.size < 2 ^ 64) then
        some { Γ with held := (gi.1, gi.2.append gj.2) :: rest }
      else none
    | _, _ => none
  | none => none

theorem joinStep_regards (ρ : Env) {Γ Γ' : CtxS} (h : joinStep Γ = some Γ') :
    Regards fetch sys Ψ (Γ.den ρ) (Γ'.den ρ) := by
  unfold joinStep at h
  split at h
  · next i j _ =>
    split at h
    · next gi gj _ _ =>
      simp only at h
      split at h
      · next hc =>
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨hreg, hoff⟩, hsz⟩ := hc
        refine (regardS_sound ρ hreg).trans ?_
        have hj := Regards.join (fetch := fetch) (sys := sys) (Ψ := Ψ)
          (Γ := CtxS.den ρ { Γ with held := gi :: gj ::
            (Γ.held.eraseIdx (max i j)).eraseIdx (min i j) })
          (b := gi.1.den ρ) (S₁ := gi.2.den ρ) (S₂ := gj.2.den ρ)
          (rest := ((Γ.held.eraseIdx (max i j)).eraseIdx (min i j)).map
            fun b => (b.1.den ρ, b.2.den ρ))
          (by
            show (gi.1.den ρ, gi.2.den ρ) :: (gj.1.den ρ, gj.2.den ρ) :: _ = _
            rw [offsetFrom_den hoff]
            rfl) hsz
        have e : CtxS.den ρ { Γ with held := (gi.1, gi.2.append gj.2) ::
              (Γ.held.eraseIdx (max i j)).eraseIdx (min i j) }
            = { CtxS.den ρ { Γ with held := gi :: gj ::
                  (Γ.held.eraseIdx (max i j)).eraseIdx (min i j) } with
                held := (gi.1.den ρ, (gi.2.den ρ).append (gj.2.den ρ)) ::
                  ((Γ.held.eraseIdx (max i j)).eraseIdx (min i j)).map
                    fun b => (b.1.den ρ, b.2.den ρ) } := by
          refine ctx_ext rfl rfl ?_ rfl
          show (gi.1.den ρ, (gi.2.append gj.2).den ρ) :: _ = _
          rw [HeldS.append_den]
        rw [e]
        exact hj
      · cases h
    · cases h
  · cases h

/-- All such taken as one, in at most so many goes. -/
def joinAll : Nat → CtxS → CtxS
  | 0, Γ => Γ
  | fuel + 1, Γ =>
    match joinStep Γ with
    | some Γ' => joinAll fuel Γ'
    | none => Γ

theorem joinAll_regards (ρ : Env) : (fuel : Nat) → (Γ : CtxS) →
    Regards fetch sys Ψ (Γ.den ρ) ((joinAll fuel Γ).den ρ)
  | 0, Γ => Regards.refl _
  | fuel + 1, Γ => by
    unfold joinAll
    cases h : joinStep Γ with
    | none => exact Regards.refl _
    | some Γ' => exact (joinStep_regards ρ h).trans (joinAll_regards ρ fuel Γ')

end TypedAsm.U
