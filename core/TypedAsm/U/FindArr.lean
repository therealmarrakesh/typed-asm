import TypedAsm.U.Idx

namespace TypedAsm.U
open TypedAsm
variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- Whether a count of whole numbers is fewer than what a term stands for,
by the ranges known: each way things may be. -/
def inCount (G : List (Val × TyS)) (P : Lin Int) (c : Val) : Bool :=
  byKnown G (c :: P.ms.map (·.2)) fun cs =>
    entails (cs.length + 1) cs (Lin.addMul (-1) c.alone ⟨P.ms, P.k + 1⟩)

theorem inCount_lt {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {P : Lin Int} {c : Val}
    (h : inCount G P c = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    P.den (natOf ρ) < natOf ρ c := by
  refine byKnown_of h hg fun cs hc hall => ?_
  have a := entails_le hc hall
  rw [Lin.addMul_den, Val.alone_den] at a
  simp only [Lin.den] at a ⊢
  omega

/-- The fact a context has that an address is one of a row of values, so
many along and fewer than there are: the first such. -/
def findArr (G : List (Val × TyS)) (a : Val) :
    List (Val × TyS) → Option (Val × Val × TyS × Nat)
  | [] => none
  | (p, .arr c τ st) :: rest =>
    match idxOf st (Lin.addMul (-1) p.lin a.lin) with
    | some P => if inCount G P c then some (p, c, τ, st) else findArr G a rest
    | none => findArr G a rest
  | _ :: rest => findArr G a rest

theorem findArr_spec {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {a : Val}
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    (l : List (Val × TyS)) → {p c : Val} → {τ : TyS} → {st : Nat} →
    findArr G a l = some (p, c, τ, st) →
    (p, TyS.arr c τ st) ∈ l ∧
      ∃ i : Nat, a.den ρ = p.den ρ + BitVec.ofNat 64 (st * i) ∧ i < (c.den ρ).toNat
  | [], _, _, _, _, h => nomatch h
  | (q, υ) :: rest, p, c, τ, st, h => by
    have tail : findArr G a rest = some (p, c, τ, st) →
        (p, TyS.arr c τ st) ∈ (q, υ) :: rest ∧
          ∃ i : Nat, a.den ρ = p.den ρ + BitVec.ofNat 64 (st * i) ∧ i < (c.den ρ).toNat :=
      fun h' => by
        obtain ⟨hm, hi⟩ := findArr_spec hg rest h'
        exact ⟨List.mem_cons_of_mem _ hm, hi⟩
    cases υ with
    | arr c' τ' st' =>
      simp only [findArr] at h
      split at h
      · next P hP =>
        split at h
        · next hin =>
          obtain ⟨i, hi, hd⟩ := idxOf_den ρ hP
          have hlt := inCount_lt (ρ := ρ) hin hg
          have e := Lin.addMul_den (Val.den ρ) (-1) q.lin a.lin
          rw [Val.lin_den, Val.lin_den, hd] at e
          have ha : a.den ρ = q.den ρ + BitVec.ofNat 64 (st' * i) := by
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

/-- Whether so many along, and so many more each `m` on from the last, are
all fewer than what a term stands for, by the ranges known: each way
things may be. -/
def suffixOk (G : List (Val × TyS)) (m : Nat) (Pj : Lin Int) (c c' : Val) : Bool :=
  byKnown G (c :: c' :: Pj.ms.map (·.2)) fun cs =>
    entails (cs.length + 1) cs
      (Lin.addMul (-1) c.alone (Lin.addMul (m : Int) c'.alone ⟨Pj.ms, Pj.k + 1 - (m : Int)⟩))

theorem suffixOk_le {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {m : Nat}
    {Pj : Lin Int} {c c' : Val} (h : suffixOk G m Pj c c' = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    Pj.den (natOf ρ) + (m : Int) * natOf ρ c' + 1 - (m : Int) ≤ natOf ρ c := by
  refine byKnown_of h hg fun cs hc hall => ?_
  have a := entails_le hc hall
  rw [Lin.addMul_den, Lin.addMul_den, Val.alone_den, Val.alone_den] at a
  simp only [Lin.den] at a ⊢
  omega

/-- Whether a thing wanted is that a value is the address of a row, and a
row is known that it is the rest of: one starting so many before it, of at
least so many more values, of the same type; or of every so many of them,
where the row wanted has its values so many times as far apart. A row of
values no way apart is one value. -/
def arrFrom (G : List (Val × TyS)) (f : Val × TyS) : Bool :=
  match f.2 with
  | .arr c' τ st => G.any fun g =>
      match g.2 with
      | .arr c τ' st' =>
        τ' == τ && st == st / st' * st' &&
          (match idxOf st' (Lin.addMul (-1) g.1.lin f.1.lin) with
           | some Pj => suffixOk G (st / st') Pj c c'
           | none => false)
      | _ => false
  | _ => false

/-- **The rest of a row is a row.** -/
theorem arrFrom_hasTy {ρ : Env} {Ψ' : MemTy} {n : Nat} {G : List (Val × TyS)} {f : Val × TyS}
    (h : arrFrom G f = true)
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    HasTy fetch sys Ψ' n (f.2.den ρ) (f.1.den ρ) := by
  obtain ⟨v, υ⟩ := f
  cases υ with
  | arr c' τ st =>
    simp only [arrFrom, List.any_eq_true] at h
    obtain ⟨⟨p, γ⟩, hmem, hrest⟩ := h
    cases γ with
    | arr c τ' st' =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨⟨rfl, hst⟩, hrest⟩ := hrest
      split at hrest
      · next Pj hPj =>
        obtain ⟨j, hj, hd⟩ := idxOf_den ρ hPj
        have hle := suffixOk_le (ρ := ρ) hrest hg
        have e := Lin.addMul_den (Val.den ρ) (-1) p.lin v.lin
        rw [Val.lin_den, Val.lin_den, hd] at e
        have hv : v.den ρ = p.den ρ + BitVec.ofNat 64 (st' * j) := by
          rw [e]
          grind
        obtain ⟨a, l, off, hl, hp, hall⟩ := hasTy_arr.mp (hg (p, .arr c τ' st') hmem)
        have hp' : p.den ρ = a + BitVec.ofNat 64 off := hp
        refine hasTy_arr.mpr ⟨a, l, off + st' * j, hl, ?_, fun i hi => ?_⟩
        · show v.den ρ = _
          rw [hv, hp', BitVec.add_assoc, ← BitVec.ofNat_add]
        · have hi' : i < (c'.den ρ).toNat := hi
          have hmi : st / st' * i + st / st' ≤ st / st' * (c'.den ρ).toNat := by
            rw [← Nat.mul_succ]
            exact Nat.mul_le_mul_left _ hi'
          have := hall (j + st / st' * i) (by
            rw [hj] at hle
            simp only [natOf] at hle
            show j + st / st' * i < (c.den ρ).toNat
            have hc : ((st / st' * (c'.den ρ).toNat : Nat) : Int)
                = ((st / st' : Nat) : Int) * ((c'.den ρ).toNat : Int) := Int.natCast_mul ..
            omega)
          rw [show off + st' * j + st * i = off + st' * (j + st / st' * i) by
            rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm st' (st / st'), ← hst]; omega]
          exact this
      · cases hrest
    | _ => cases hrest
  | _ => cases h

end TypedAsm.U
