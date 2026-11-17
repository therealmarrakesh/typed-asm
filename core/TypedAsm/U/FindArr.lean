import TypedAsm.U.Idx

namespace TypedAsm.U
open TypedAsm
variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- Whether a count of whole numbers is fewer than what a term stands for,
by the ranges known: each way things may be. -/
def inCount (G : List (Val × TyS)) (P : Lin Int) (c : Val) : Bool :=
  (know G (P.ms.map (·.2) ++ c.lin.ms.map (·.2))).all fun cs =>
    match noWrap (cs.length + 1) cs c with
    | some Pc => entails (cs.length + 1) cs (Lin.addMul (-1) Pc ⟨P.ms, P.k + 1⟩)
    | none => false

theorem inCount_lt {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {P : Lin Int} {c : Val}
    (h : inCount G P c = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    P.den (natOf ρ) < natOf ρ c := by
  obtain ⟨cs, hcs, hall⟩ := know_le (ρ := ρ) G _ hg
  have hc := List.all_eq_true.mp h cs hcs
  split at hc
  · next Pc hPc =>
    have e := noWrap_eq hPc hall
    have a := entails_le hc hall
    rw [Lin.addMul_den] at a
    simp only [Lin.den] at a e ⊢
    omega
  · cases hc

/-- The fact a context has that an address is one of a row of values, so
many along and fewer than there are: the first such. -/
def findArr (G : List (Val × TyS)) (a : Val) : List (Val × TyS) → Option (Val × Val × TyS)
  | [] => none
  | (p, .arr c τ) :: rest =>
    match idxOf (Lin.addMul (-1) p.lin a.lin) with
    | some P => if inCount G P c then some (p, c, τ) else findArr G a rest
    | none => findArr G a rest
  | _ :: rest => findArr G a rest

theorem findArr_spec {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {a : Val}
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    (l : List (Val × TyS)) → {p c : Val} → {τ : TyS} → findArr G a l = some (p, c, τ) →
    (p, TyS.arr c τ) ∈ l ∧
      ∃ i : Nat, a.den ρ = p.den ρ + BitVec.ofNat 64 (8 * i) ∧ i < (c.den ρ).toNat
  | [], _, _, _, h => nomatch h
  | (q, υ) :: rest, p, c, τ, h => by
    have tail : findArr G a rest = some (p, c, τ) →
        (p, TyS.arr c τ) ∈ (q, υ) :: rest ∧
          ∃ i : Nat, a.den ρ = p.den ρ + BitVec.ofNat 64 (8 * i) ∧ i < (c.den ρ).toNat :=
      fun h' => by
        obtain ⟨hm, hi⟩ := findArr_spec hg rest h'
        exact ⟨List.mem_cons_of_mem _ hm, hi⟩
    cases υ with
    | arr c' τ' =>
      simp only [findArr] at h
      split at h
      · next P hP =>
        split at h
        · next hin =>
          obtain ⟨i, hi, hd⟩ := idxOf_den ρ hP
          have hlt := inCount_lt (ρ := ρ) hin hg
          have e := Lin.addMul_den (Val.den ρ) (-1) q.lin a.lin
          rw [Val.lin_den, Val.lin_den, hd] at e
          have ha : a.den ρ = q.den ρ + BitVec.ofNat 64 (8 * i) := by
            rw [e]
            grind
          have hi' : i < (c'.den ρ).toNat := by
            rw [hi] at hlt
            simp only [natOf] at hlt
            omega
          cases h
          exact ⟨List.mem_cons_self, i, ha, hi'⟩
        · exact tail h
      · exact tail h
    | _ => exact tail h

end TypedAsm.U
