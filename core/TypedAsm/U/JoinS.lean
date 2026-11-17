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
  ⟨S.size.plus T.size, S.slots ++ T.slots.map fun p => (S.size.plus p.1, p.2)⟩

/-- It is the two regions' one, where the sizes together do not wrap and
the second's values lie within it. -/
theorem HeldS.append_den (ρ : Env) (S T : HeldS) (hsz : S.size.nat ρ + T.size.nat ρ < 2 ^ 64)
    (hfit : ∀ p ∈ T.slots, p.1.nat ρ + 8 ≤ T.size.nat ρ) :
    (S.append T).den ρ = (S.den ρ).append (T.den ρ) := by
  have hsize : (S.size.plus T.size).nat ρ = S.size.nat ρ + T.size.nat ρ := by
    show ((S.size.plus T.size).den ρ).toNat = _
    rw [Val.plus_den, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hsz
  have hslots : (T.slots.map fun p => (S.size.plus p.1, p.2)).map (slotDen ρ)
      = (T.slots.map (slotDen ρ)).map fun p => (S.size.nat ρ + p.1, p.2) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have := hfit p hp
    show (((S.size.plus p.1).den ρ).toNat, p.2.den ρ) = (S.size.nat ρ + p.1.nat ρ, p.2.den ρ)
    rw [Val.plus_den, BitVec.toNat_add]
    have e1 : (S.size.den ρ).toNat = S.size.nat ρ := rfl
    have e2 : (p.1.den ρ).toNat = p.1.nat ρ := rfl
    rw [e1, e2, Nat.mod_eq_of_lt (by omega)]
  show (⟨(S.size.plus T.size).nat ρ,
      (S.slots ++ T.slots.map fun p => (S.size.plus p.1, p.2)).map (slotDen ρ)⟩ : Held)
    = ⟨S.size.nat ρ + T.size.nat ρ, S.slots.map (slotDen ρ) ++
        (T.slots.map (slotDen ρ)).map fun p => (S.size.nat ρ + p.1, p.2)⟩
  rw [hsize, List.map_append, hslots]

/-- Whether one region starts where another ends. -/
def follows (gi gj : Val × HeldS) : Bool := gj.1.same (gi.1.plus gi.2.size)

/-- Two regions of a list, the second starting where the first ends. -/
def findPair (G : List (Val × HeldS)) : Option (Nat × Nat) :=
  (List.range G.length).findSome? fun i =>
    (List.range G.length).findSome? fun j =>
      match G[i]?, G[j]? with
      | some gi, some gj => if i != j && follows gi gj then some (i, j) else none
      | _, _ => none

/-- A context with two regions that lie end to end taken as one, if it
holds two such, and their sizes together are shown not to wrap. -/
def joinStep (Γ : CtxS) : Option CtxS :=
  match findPair Γ.held with
  | some (i, j) =>
    match Γ.held[i]?, Γ.held[j]? with
    | some gi, some gj =>
      let rest := (Γ.held.eraseIdx (max i j)).eraseIdx (min i j)
      if regardS noEnt Γ { Γ with held := gi :: gj :: rest } && follows gi gj &&
          sumLe Γ.known [gi.2.size, gj.2.size] 0 [.lit (-1)] 0 then
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
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨hreg, hoff⟩, hsz⟩ := hc
        refine (regardS_sound noEnt_sound ρ hreg).trans ?_
        intro k Ψ' he hwf s hw
        have hsz' : gi.2.size.nat ρ + gj.2.size.nat ρ < 2 ^ 64 := by
          have := sumLe_den hsz (knownS hw.known)
          simp only [sumNat, Nat.add_zero] at this
          have hm : (Val.lit (-1)).nat ρ = 2 ^ 64 - 1 := rfl
          omega
        have hfit : ∀ p ∈ gj.2.slots, p.1.nat ρ + 8 ≤ gj.2.size.nat ρ := fun p hp =>
          hw.held.fits (gj.1.den ρ, gj.2.den ρ)
            (List.mem_cons_of_mem _ List.mem_cons_self) (slotDen ρ p)
            (List.mem_map.mpr ⟨p, hp, rfl⟩)
        have hj := Regards.join (fetch := fetch) (sys := sys) (Ψ := Ψ)
          (Γ := CtxS.den ρ { Γ with held := gi :: gj ::
            (Γ.held.eraseIdx (max i j)).eraseIdx (min i j) })
          (b := gi.1.den ρ) (S₁ := gi.2.den ρ) (S₂ := gj.2.den ρ)
          (rest := (((Γ.held.eraseIdx (max i j)).eraseIdx (min i j)).map
            fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest)
          (by
            show (gi.1.den ρ, gi.2.den ρ) :: (gj.1.den ρ, gj.2.den ρ) :: _ ++ _ = _
            rw [Val.same_den ρ hoff, Val.plus_den]
            show _ = (gi.1.den ρ, gi.2.den ρ) ::
              (gi.1.den ρ + BitVec.ofNat 64 (gi.2.size.den ρ).toNat, gj.2.den ρ) :: _
            rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
            rfl) hsz'
        have e : CtxS.den ρ { Γ with held := (gi.1, gi.2.append gj.2) ::
              (Γ.held.eraseIdx (max i j)).eraseIdx (min i j) }
            = { CtxS.den ρ { Γ with held := gi :: gj ::
                  (Γ.held.eraseIdx (max i j)).eraseIdx (min i j) } with
                held := (gi.1.den ρ, (gi.2.den ρ).append (gj.2.den ρ)) ::
                  ((((Γ.held.eraseIdx (max i j)).eraseIdx (min i j)).map
                    fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest) } := by
          refine ctx_ext rfl rfl ?_ rfl
          show (gi.1.den ρ, (gi.2.append gj.2).den ρ) :: _ ++ _ = _
          rw [HeldS.append_den ρ _ _ hsz' hfit]
          rfl
        rw [e]
        exact hj k Ψ' he hwf s hw
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
