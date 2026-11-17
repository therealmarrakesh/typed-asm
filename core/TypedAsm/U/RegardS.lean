import TypedAsm.U.Find
import TypedAsm.U.Lin
import TypedAsm.U.Know
import TypedAsm.U.Entail
import TypedAsm.U.Range

/-!
# Whether one context may be regarded as another, computed

What it comes to for one context to be regarded as another is one statement
(`Regards.parts`): the same registers and flags; each thing known a
consequence of what was known; each region held a part of one that was,
parts of one region not overlapping. Here that is decided on terms: whether
two terms stand for the same value; where a region lies in another; whether
a thing known follows. What is decided is exactly the statement's
conditions, and that deciding them is right is proved once.

It does not decide everything that is so. Two terms are found to be the
same value only as the same term, or sums of the same terms and the same
number; a region is found in another only where its address is a number of
bytes past the other's, in that sense; and a thing known is found to follow
only from one thing known of the same value, or of itself.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- Whether two terms stand for the same value, as far as their being the
same term, or coming apart into the same multiples and the same number,
shows. -/
def Val.same (a b : Val) : Bool :=
  a == b || a.linSame b

theorem Val.same_den (ρ : Env) {a b : Val} (h : a.same b = true) : a.den ρ = b.den ρ := by
  unfold Val.same at h
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · rw [beq_iff_eq.mp h]
  · exact Val.linSame_den ρ h

def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by
  cases r <;> decide

def regionDen (ρ : Env) (b : Val × HeldS) : Region := (b.1.den ρ, b.2.den ρ)

/-! ## Regions as parts of regions -/

/-- Whether each value the part says is there lies within it, and is said
by the region to be there, the part starting `o` bytes into the region. -/
def slotsIn (o size : Nat) (gs ds : List (Nat × Val)) : Bool :=
  ds.all fun d => d.1 + 8 ≤ size && gs.any fun g => g.1 == o + d.1 && g.2.same d.2

/-- The first region of a list that a given region is a part of: its place,
counted from `i`, and how far into it the part starts. -/
def hostOf (d : Val × HeldS) : List (Val × HeldS) → Nat → Option (Nat × Nat)
  | [], _ => none
  | g :: gs, i =>
    match offsetFrom d.1 g.1 with
    | some o =>
      if o + d.2.size ≤ g.2.size && slotsIn o d.2.size g.2.slots d.2.slots then some (i, o)
      else hostOf d gs (i + 1)
    | none => hostOf d gs (i + 1)

theorem hostOf_spec (d : Val × HeldS) : (G : List (Val × HeldS)) → (i₀ i o : Nat) →
    hostOf d G i₀ = some (i, o) →
    ∃ g, G[i - i₀]? = some g ∧ i₀ ≤ i ∧ offsetFrom d.1 g.1 = some o ∧
      o + d.2.size ≤ g.2.size ∧ slotsIn o d.2.size g.2.slots d.2.slots = true
  | [], _, _, _, h => nomatch h
  | g :: gs, i₀, i, o, h => by
    have later : hostOf d gs (i₀ + 1) = some (i, o) →
        ∃ g', (g :: gs)[i - i₀]? = some g' ∧ i₀ ≤ i ∧ offsetFrom d.1 g'.1 = some o ∧
          o + d.2.size ≤ g'.2.size ∧ slotsIn o d.2.size g'.2.slots d.2.slots = true := by
      intro h'
      obtain ⟨g', hg', hle, rest⟩ := hostOf_spec d gs (i₀ + 1) i o h'
      refine ⟨g', ?_, by omega, rest⟩
      have e : i - i₀ = (i - (i₀ + 1)) + 1 := by omega
      rw [e, List.getElem?_cons_succ]
      exact hg'
    unfold hostOf at h
    cases hoff : offsetFrom d.1 g.1 with
    | none => rw [hoff] at h; exact later h
    | some o' =>
      rw [hoff] at h
      simp only at h
      split at h
      · next hc =>
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨g, by simp, Nat.le_refl _, hoff, hc.1, hc.2⟩
      · exact later h

/-- Each region of a list as a part of one of another: which, and how far
in. Nothing if one is a part of none. -/
def partsS (G : List (Val × HeldS)) : List (Val × HeldS) → Option (List (Nat × Nat × HeldS))
  | [] => some []
  | d :: ds =>
    match hostOf d G 0, partsS G ds with
    | some (i, o), some ps => some ((i, o, d.2) :: ps)
    | _, _ => none

def partDen (ρ : Env) (x : Nat × Nat × HeldS) : Part := (x.1, x.2.1, x.2.2.den ρ)

theorem partsS_den (ρ : Env) (G : List (Val × HeldS)) :
    (D : List (Val × HeldS)) → (P : List (Nat × Nat × HeldS)) → partsS G D = some P →
    D.map (regionDen ρ) = (P.map (partDen ρ)).map (partRegion (G.map (regionDen ρ))) ∧
      ∀ x ∈ P.map (partDen ρ), PartOk (G.map (regionDen ρ)) x
  | [], P, h => by cases h; exact ⟨rfl, fun _ hx => nomatch hx⟩
  | d :: ds, P, h => by
    unfold partsS at h
    cases hh : hostOf d G 0 with
    | none => rw [hh] at h; cases h
    | some io =>
      obtain ⟨i, o⟩ := io
      cases hp : partsS G ds with
      | none => rw [hh, hp] at h; cases h
      | some ps =>
        rw [hh, hp] at h
        cases h
        obtain ⟨g, hg, _, hoff, hle, hsl⟩ := hostOf_spec d G 0 i o hh
        rw [Nat.sub_zero] at hg
        obtain ⟨ih₁, ih₂⟩ := partsS_den ρ G ds ps hp
        have hE : (G.map (regionDen ρ))[i]? = some (regionDen ρ g) := by
          rw [List.getElem?_map, hg]; rfl
        have hok : PartOk (G.map (regionDen ρ)) (partDen ρ (i, o, d.2)) := by
          refine ⟨regionDen ρ g, hE, hle, ?_⟩
          intro p hp'
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
          simp only [slotsIn, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
            List.any_eq_true, beq_iff_eq] at hsl
          obtain ⟨hfit, q', hq', ho, hv⟩ := hsl q hq
          refine ⟨hfit, List.mem_map.mpr ⟨q', hq', ?_⟩⟩
          show (q'.1, q'.2.den ρ) = (o + q.1, q.2.den ρ)
          rw [ho, Val.same_den ρ hv]
        refine ⟨?_, ?_⟩
        · rw [List.map_cons, List.map_cons, List.map_cons, ih₁]
          congr 1
          rw [partRegion_eq (x := partDen ρ (i, o, d.2)) hE]
          show (d.1.den ρ, d.2.den ρ) = (g.1.den ρ + BitVec.ofNat 64 o, d.2.den ρ)
          rw [offsetFrom_den hoff]
        · intro x hx
          rw [List.map_cons] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hok
          · exact ih₂ x hx

/-- Whether no two parts overlap: of different regions, or one ending
before the other begins. -/
def apartS : List (Nat × Nat × HeldS) → Bool
  | [] => true
  | x :: xs =>
    (xs.all fun y => x.1 != y.1 || decide (x.2.1 + x.2.2.size ≤ y.2.1) ||
      decide (y.2.1 + y.2.2.size ≤ x.2.1)) && apartS xs

theorem apartS_den (ρ : Env) : (P : List (Nat × Nat × HeldS)) → apartS P = true →
    (P.map (partDen ρ)).Pairwise PartsApart
  | [], _ => .nil
  | x :: xs, h => by
    simp only [apartS, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at h
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨fun y hy => ?_, apartS_den ρ xs h.2⟩
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    rcases h.1 y' hy' with (h1 | h1) | h1
    · exact .inl h1
    · exact .inr (.inl h1)
    · exact .inr (.inr h1)

/-- Whether the parts of the region at place `i`, of `size` bytes, take in
the whole of it from byte `cur` on: one starts there, another where that one
ends, and so on to the end. -/
def coverFrom (P : List (Nat × Nat × HeldS)) (i size : Nat) : Nat → Nat → Bool
  | fuel, cur =>
    if cur = size then true
    else
      match fuel with
      | 0 => false
      | fuel + 1 =>
        match P.find? fun x => x.1 == i && x.2.1 == cur && decide (0 < x.2.2.size) with
        | some x => coverFrom P i size fuel (cur + x.2.2.size)
        | none => false

theorem coverFrom_spec (P : List (Nat × Nat × HeldS)) (i size : Nat) :
    (fuel cur : Nat) → coverFrom P i size fuel cur = true →
    ∀ o, cur ≤ o → o < size → ∃ x ∈ P, x.1 = i ∧ x.2.1 ≤ o ∧ o < x.2.1 + x.2.2.size
  | fuel, cur, h, o, hlo, hhi => by
    unfold coverFrom at h
    split at h
    · next he => omega
    · cases fuel with
      | zero => cases h
      | succ fuel =>
        simp only at h
        cases hf : P.find? fun x => x.1 == i && x.2.1 == cur && decide (0 < x.2.2.size) with
        | none => rw [hf] at h; cases h
        | some x =>
          rw [hf] at h
          have hx := List.find?_some hf
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
          by_cases ho : o < cur + x.2.2.size
          · exact ⟨x, List.mem_of_find?_eq_some hf, hx.1.1, by omega, by omega⟩
          · exact coverFrom_spec P i size fuel _ h o (by omega) hhi

/-- Whether the parts take in the whole of every region of a list. -/
def coverS (G : List (Val × HeldS)) (P : List (Nat × Nat × HeldS)) : Bool :=
  (List.range G.length).all fun i =>
    match G[i]? with
    | some g => coverFrom P i g.2.size P.length 0
    | none => true

theorem coverS_den (ρ : Env) (G : List (Val × HeldS)) (P : List (Nat × Nat × HeldS))
    (h : coverS G P = true) (i : Nat) (b : Region) (hb : (G.map (regionDen ρ))[i]? = some b)
    (o : Nat) (ho : o < b.2.size) :
    ∃ x ∈ P.map (partDen ρ), x.1 = i ∧ x.2.1 ≤ o ∧ o < x.2.1 + x.2.2.size := by
  rw [List.getElem?_map] at hb
  cases hg : G[i]? with
  | none => rw [hg] at hb; cases hb
  | some g =>
    rw [hg] at hb
    cases hb
    have hi : i < G.length := (List.getElem?_eq_some_iff.mp hg).1
    have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
    rw [hg] at this
    obtain ⟨x, hx, h1, h2, h3⟩ := coverFrom_spec P i g.2.size _ _ this o (Nat.zero_le _) ho
    exact ⟨partDen ρ x, List.mem_map.mpr ⟨x, hx, rfl⟩, h1, h2, h3⟩

/-- The first region of a list that an extent lies within: its place,
counted from `i`, how far in the extent starts, and the region. -/
def hostExtent (base : Val) (size : Nat) : List (Val × HeldS) → Nat → Option (Nat × Nat × HeldS)
  | [], _ => none
  | g :: gs, i =>
    match offsetFrom base g.1 with
    | some o => if o + size ≤ g.2.size then some (i, o, g.2) else hostExtent base size gs (i + 1)
    | none => hostExtent base size gs (i + 1)

/-- A stretch of a region, as a region: its bytes, and the values the
region says lie wholly in it. -/
def stretch (g : Val × HeldS) (x : Nat × Nat) : Val × HeldS :=
  (.add g.1 (.lit (BitVec.ofNat 64 x.1)),
    ⟨x.2, g.2.slots.filterMap fun p =>
      if x.1 ≤ p.1 ∧ p.1 + 8 ≤ x.1 + x.2 then some (p.1 - x.1, p.2) else none⟩)

/-! ## What is known -/

/-- Whether what is known one way is known another, read off the two. -/
def followsS (τ : TyS) : TyS → Bool
  | .any => true
  | .ptr S w off => τ == .ptr S w off || τ == .ptr S true off
  | .ref tag w off => τ == .ref tag w off || τ == .ref tag true off
  | .nullable υ =>
    τ == .nullable υ || followsS τ υ ||
      (match τ with
       | .nullable τ' => followsS τ' υ
       | _ => false)
  | .orErr υ =>
    τ == .orErr υ || followsS τ υ ||
      (match τ with
       | .orErr τ' => followsS τ' υ
       | _ => false)
  | .str c =>
    τ == .str c ||
      (c == .lit 0 &&
        (match τ with
         | .str _ => true
         | _ => false))
  | .atom i => τ == .atom i
  | .code r f h k rest => τ == .code r f h k rest
  | .arr c υ => τ == .arr c υ
  | .upTo t strict => τ == .upTo t strict
  | .range lo hi =>
    match τ with
    | .range lo' hi' => Range.within ⟨lo', hi'⟩ ⟨lo, hi⟩
    | _ => false

theorem followsS_sub (ρ : Env) (v : BitVec 64) :
    (υ τ : TyS) → followsS τ υ = true → Sub v (τ.den ρ) (υ.den ρ)
  | .any, τ, _ => .any _ _
  | .ptr S w off, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl
    · exact .refl _ _
    · exact .readOnly _ _ _ _
  | .ref tag w off, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl
    · exact .refl _ _
    · exact .refReadOnly _ _ _ _
  | .nullable υ, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (rfl | h) | h
    · exact .refl _ _
    · exact .nullable (followsS_sub ρ v υ τ h)
    · cases τ with
      | nullable τ' => exact .nullableMono (followsS_sub ρ v υ τ' h)
      | _ => cases h
  | .orErr υ, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (rfl | h) | h
    · exact .refl _ _
    · exact .orErr (followsS_sub ρ v υ τ h)
    · cases τ with
      | orErr τ' => exact .orErrMono (followsS_sub ρ v υ τ' h)
      | _ => cases h
  | .str c, τ, h => by
    simp only [followsS, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with rfl | ⟨rfl, hτ⟩
    · exact .refl _ _
    · cases τ with
      | str c' => exact .strLess _ _
      | _ => cases hτ
  | .atom i, τ, h => by
    simp only [followsS, beq_iff_eq] at h
    subst h
    exact .refl _ _
  | .code r f hd k rest, τ, h => by
    simp only [followsS, beq_iff_eq] at h
    subst h
    exact .refl _ _
  | .arr c υ, τ, h => by
    simp only [followsS, beq_iff_eq] at h
    subst h
    exact .refl _ _
  | .upTo t strict, τ, h => by
    simp only [followsS, beq_iff_eq] at h
    subst h
    exact .refl _ _
  | .range lo hi, τ, h => by
    cases τ with
    | range lo' hi' =>
      exact .rangeIn lo' hi' lo hi fun hv =>
        Range.within_has (r := ⟨lo', hi'⟩) (s := ⟨lo, hi⟩) h hv
    | _ => cases h

/-- Whether a thing is so of a value whatever else is known: that nothing
is; that zero may be null; that an error number may be one. -/
def outright (v : Val) : TyS → Bool
  | .any => true
  | .nullable τ => v.lit? == some 0 || outright v τ
  | .orErr τ =>
    (match v.lit? with
     | some k => decide (SysErr k)
     | none => false) || outright v τ
  | .range lo hi =>
    match v.lit? with
    | some k => decide (k - lo ≤ hi - lo)
    | none => false
  | _ => false

theorem outright_hasTy (ρ : Env) (Ψ' : MemTy) (n : Nat) (v : Val) :
    (τ : TyS) → outright v τ = true → HasTy fetch sys Ψ' n (τ.den ρ) (v.den ρ)
  | .any, _ => HasTy.any _
  | .nullable τ, h => by
    simp only [outright, Bool.or_eq_true, beq_iff_eq] at h
    refine (hasTy_nullable (τ := τ.den ρ)).mpr ?_
    rcases h with h | h
    · exact .inl (Val.lit?_den h)
    · exact .inr (outright_hasTy ρ Ψ' n v τ h)
  | .orErr τ, h => by
    simp only [outright, Bool.or_eq_true] at h
    refine (hasTy_orErr (τ := τ.den ρ)).mpr ?_
    rcases h with h | h
    · cases hl : v.lit? with
      | none => rw [hl] at h; cases h
      | some k =>
        rw [hl] at h
        rw [Val.lit?_den hl]
        exact .inl (of_decide_eq_true h)
    · exact .inr (outright_hasTy ρ Ψ' n v τ h)
  | .ptr _ _ _, h => nomatch h
  | .ref _ _ _, h => nomatch h
  | .str _, h => nomatch h
  | .atom _, h => nomatch h
  | .code .., h => nomatch h
  | .arr .., h => nomatch h
  | .upTo .., h => nomatch h
  | .range lo hi, h => by
    simp only [outright] at h
    cases hl : v.lit? with
    | none => rw [hl] at h; cases h
    | some k =>
      rw [hl] at h
      rw [Val.lit?_den hl]
      exact hasTy_range.mpr (of_decide_eq_true h)

/-- `EntSound ent`: wherever `ent` says one thing known gives another, it
does, of any value: at every step count, under every memory typing. -/
def EntSound (fetch : Fetch) (sys : Syscall) (ent : TyS → TyS → Bool) : Prop :=
  ∀ (ρ : Env) (v : BitVec 64) (τ υ : TyS), ent τ υ = true →
    Follows fetch sys v (τ.den ρ) (υ.den ρ)

/-- Nothing gives anything. -/
def noEnt : TyS → TyS → Bool := fun _ _ => false

theorem noEnt_sound : EntSound fetch sys noEnt := fun _ _ _ _ h => nomatch h

/-- Whether a thing known is so of itself, or follows from one of a list, of
the same value: read off the two, or by `ent`, which is asked what reading
off does not show. -/
def factFrom (ent : TyS → TyS → Bool) (G : List (Val × TyS)) (f : Val × TyS) : Bool :=
  outright f.1 f.2 || (G.any fun g => g.1.same f.1 && (followsS g.2 f.2 || ent g.2 f.2)) ||
    match f.2 with
    | .range lo hi => rangeHolds G f.1 lo hi
    | _ => false

/-- **What is so of itself, or follows from something known of the same
value, is so wherever what is known is.** -/
theorem factFrom_hasTy {ent : TyS → TyS → Bool} (he : EntSound fetch sys ent) (ρ : Env)
    {G : List (Val × TyS)} {f : Val × TyS}
    (h : factFrom ent G f = true) (Ψ' : MemTy) (n : Nat)
    (hg : ∀ g ∈ G.map (fun g => (g.1.den ρ, g.2.den ρ)), HasTy fetch sys Ψ' n g.2 g.1) :
    HasTy fetch sys Ψ' n (f.2.den ρ) (f.1.den ρ) := by
  simp only [factFrom, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  rcases h with (hout | ⟨g₀, hg₀, hs, hfo⟩) | hr
  rotate_left 2
  · split at hr
    · next lo hi hτ =>
      rw [hτ]
      exact hasTy_range.mpr (rangeHolds_has hr fun g hgm =>
        hg (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩))
    · cases hr
  · exact outright_hasTy ρ Ψ' n f.1 f.2 hout
  · have hsrc := hg (g₀.1.den ρ, g₀.2.den ρ) (List.mem_map.mpr ⟨g₀, hg₀, rfl⟩)
    rw [← Val.same_den ρ hs]
    rcases hfo with hfo | hen
    · exact hsrc.sub (followsS_sub ρ _ _ _ hfo)
    · exact he ρ _ _ _ hen Ψ' n hsrc

/-! ## The whole -/

/-- **Whether the first context may be regarded as the second.** -/
def regardS (ent : TyS → TyS → Bool) (Γ Δ : CtxS) : Bool :=
  (allRegs.all fun r => (Γ.regs.get r).same (Δ.regs.get r)) && Γ.flags == Δ.flags &&
    (match partsS Γ.held Δ.held with
     | some P => apartS P && coverS Γ.held P
     | none => false) &&
    Δ.known.all (factFrom ent Γ.known) && Δ.rest == Γ.rest

theorem regardS_sound {ent : TyS → TyS → Bool} (he : EntSound fetch sys ent) (ρ : Env)
    {Γ Δ : CtxS} (h : regardS ent Γ Δ = true) :
    Regards fetch sys Ψ (Γ.den ρ) (Δ.den ρ) := by
  simp only [regardS, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hr, hf⟩, hh⟩, hk⟩, hrest⟩ := h
  cases hP : partsS Γ.held Δ.held with
  | none => rw [hP] at hh; cases hh
  | some P =>
    rw [hP] at hh
    simp only [Bool.and_eq_true] at hh
    obtain ⟨hmap, hok⟩ := partsS_den ρ Γ.held Δ.held P hP
    refine Regards.parts (E := Γ.held.map (regionDen ρ)) (F := restDen ρ Γ.rest)
      (L := P.map (partDen ρ)) ?_ ?_ ?_ rfl ?_ hok (apartS_den ρ P hh.1)
      (coverS_den ρ Γ.held P hh.2)
    · funext r
      exact (Val.same_den ρ (hr r (mem_allRegs r))).symm
    · show Δ.flags.den ρ = Γ.flags.den ρ
      rw [hf]
    · intro f hf' Ψ' n hg
      obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hf'
      exact factFrom_hasTy he ρ (hk g hg') Ψ' n hg
    · show Δ.held.map (regionDen ρ) ++ restDen ρ Δ.rest = _
      rw [hmap, hrest]

end TypedAsm.U
