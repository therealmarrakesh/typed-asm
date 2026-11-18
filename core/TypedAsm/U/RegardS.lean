import TypedAsm.U.Find
import TypedAsm.U.Size
import TypedAsm.U.Lin
import TypedAsm.U.Know
import TypedAsm.U.FindArr
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
def Val.sameFlat (a b : Val) : Bool :=
  a == b || a.linSame b

theorem Val.sameFlat_den (ρ : Env) {a b : Val} (h : a.sameFlat b = true) : a.den ρ = b.den ρ := by
  unfold Val.sameFlat at h
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · rw [beq_iff_eq.mp h]
  · exact Val.linSame_den ρ h

/-- **Whether two terms stand for the same value**: so, as terms or as
sums; or the same operator, or the same function of the author's, on what
are the same values in that sense. -/
def Val.same : Val → Val → Bool
  | .un o x, b =>
    (Val.un o x).sameFlat b ||
      match b with
      | .un o' y => o == o' && Val.same x y
      | _ => false
  | .bin o x y, b =>
    (Val.bin o x y).sameFlat b ||
      match b with
      | .bin o' x' y' => o == o' && Val.same x x' && Val.same y y'
      | _ => false
  | .tri o x y z, b =>
    (Val.tri o x y z).sameFlat b ||
      match b with
      | .tri o' x' y' z' => o == o' && Val.same x x' && Val.same y y' && Val.same z z'
      | _ => false
  | .fop o fl x y, b =>
    (Val.fop o fl x y).sameFlat b ||
      match b with
      | .fop o' fl' x' y' => o == o' && fl == fl' && Val.same x x' && Val.same y y'
      | _ => false
  | .app f x y, b =>
    (Val.app f x y).sameFlat b ||
      match b with
      | .app f' x' y' => f == f' && Val.same x x' && Val.same y y'
      | _ => false
  | .lit v, b => (Val.lit v).sameFlat b
  | .var i, b => (Val.var i).sameFlat b
  | .bvar d i, b => (Val.bvar d i).sameFlat b
  | .slot s, b => (Val.slot s).sameFlat b

theorem Val.same_den (ρ : Env) : {a b : Val} → a.same b = true → a.den ρ = b.den ρ
  | .un o x, b, h => by
    unfold Val.same at h
    rcases Bool.or_eq_true _ _ |>.mp h with h | h
    · exact Val.sameFlat_den ρ h
    · cases b with
      | un o' y =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        show o.eval (x.den ρ) = o'.eval (y.den ρ)
        rw [h.1, Val.same_den ρ h.2]
      | _ => cases h
  | .bin o x y, b, h => by
    unfold Val.same at h
    rcases Bool.or_eq_true _ _ |>.mp h with h | h
    · exact Val.sameFlat_den ρ h
    · cases b with
      | bin o' x' y' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        show o.eval (x.den ρ) (y.den ρ) = o'.eval (x'.den ρ) (y'.den ρ)
        rw [h.1.1, Val.same_den ρ h.1.2, Val.same_den ρ h.2]
      | _ => cases h
  | .tri o x y z, b, h => by
    unfold Val.same at h
    rcases Bool.or_eq_true _ _ |>.mp h with h | h
    · exact Val.sameFlat_den ρ h
    · cases b with
      | tri o' x' y' z' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        show o.eval (x.den ρ) (y.den ρ) (z.den ρ) = o'.eval (x'.den ρ) (y'.den ρ) (z'.den ρ)
        rw [h.1.1.1, Val.same_den ρ h.1.1.2, Val.same_den ρ h.1.2, Val.same_den ρ h.2]
      | _ => cases h
  | .fop o fl x y, b, h => by
    unfold Val.same at h
    rcases Bool.or_eq_true _ _ |>.mp h with h | h
    · exact Val.sameFlat_den ρ h
    · cases b with
      | fop o' fl' x' y' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        show o.eval (fl.den ρ) (x.den ρ) (y.den ρ) = o'.eval (fl'.den ρ) (x'.den ρ) (y'.den ρ)
        rw [h.1.1.1, h.1.1.2, Val.same_den ρ h.1.2, Val.same_den ρ h.2]
      | _ => cases h
  | .app f x y, b, h => by
    unfold Val.same at h
    rcases Bool.or_eq_true _ _ |>.mp h with h | h
    · exact Val.sameFlat_den ρ h
    · cases b with
      | app f' x' y' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        show ρ.fn f (x.den ρ) (y.den ρ) = ρ.fn f' (x'.den ρ) (y'.den ρ)
        rw [h.1.1, Val.same_den ρ h.1.2, Val.same_den ρ h.2]
      | _ => cases h
  | .lit _, _, h => Val.sameFlat_den ρ (by unfold Val.same at h; exact h)
  | .var _, _, h => Val.sameFlat_den ρ (by unfold Val.same at h; exact h)
  | .bvar _ _, _, h => Val.sameFlat_den ρ (by unfold Val.same at h; exact h)
  | .slot _, _, h => Val.sameFlat_den ρ (by unfold Val.same at h; exact h)

def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by
  cases r <;> decide

def regionDen (ρ : Env) (b : Val × HeldS) : Region := (b.1.den ρ, b.2.den ρ)

/-! ## Regions as parts of regions

How far into a region a part starts, and how large each is, are terms.
Whether the part lies within the region, and whether two parts are apart,
is asked of what is known of values. -/

/-- Whether each value the part says is there lies within it, and is said
by the region to be there, the part starting `o` bytes into the region. -/
def slotsIn (sm : List (Val × TyS) → Val → Val → Bool) (K : List (Val × TyS)) (o size : Val)
    (gs ds : List (Val × Val)) : Bool :=
  ds.all fun d => fitsS K d.1 8 size && gs.any fun g => g.1.same (o.plus d.1) && sm K g.2 d.2

/-- The first region of a list that a given region is a part of: its place,
counted from `i`, and how far into it the part starts; among those whose
address the part's is a number past (`plain`), or among the others. -/
def hostOfP (sm : List (Val × TyS) → Val → Val → Bool) (plain : Bool) (K : List (Val × TyS))
    (d : Val × HeldS) :
    List (Val × HeldS) → Nat → Option (Nat × Val)
  | [], _ => none
  | g :: gs, i =>
    if (d.1.minus g.1).isSome == plain &&
        sumLe K [offTerm d.1 g.1, d.2.size] 0 [g.2.size] 0 &&
        slotsIn sm K (offTerm d.1 g.1) d.2.size g.2.slots d.2.slots then
      some (i, offTerm d.1 g.1)
    else hostOfP sm plain K d gs (i + 1)

theorem hostOfP_spec {sm : List (Val × TyS) → Val → Val → Bool} {plain : Bool} {K : List (Val × TyS)}
    (d : Val × HeldS) :
    (G : List (Val × HeldS)) → (i₀ i : Nat) → (o : Val) →
    hostOfP sm plain K d G i₀ = some (i, o) →
    ∃ g, G[i - i₀]? = some g ∧ i₀ ≤ i ∧ o = offTerm d.1 g.1 ∧
      sumLe K [o, d.2.size] 0 [g.2.size] 0 = true ∧
      slotsIn sm K o d.2.size g.2.slots d.2.slots = true
  | [], _, _, _, h => nomatch h
  | g :: gs, i₀, i, o, h => by
    unfold hostOfP at h
    split at h
    · next hc =>
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨g, by simp, Nat.le_refl _, rfl, hc.1.2, hc.2⟩
    · obtain ⟨g', hg', hle, rest⟩ := hostOfP_spec d gs (i₀ + 1) i o h
      refine ⟨g', ?_, by omega, rest⟩
      have e : i - i₀ = (i - (i₀ + 1)) + 1 := by omega
      rw [e, List.getElem?_cons_succ]
      exact hg'

/-- The first region of a list that a given region is a part of. -/
def hostOf (sm : List (Val × TyS) → Val → Val → Bool) (K : List (Val × TyS)) (d : Val × HeldS)
    (G : List (Val × HeldS)) : Option (Nat × Val) :=
  match hostOfP sm true K d G 0 with
  | some r => some r
  | none => hostOfP sm false K d G 0

theorem hostOf_spec {sm : List (Val × TyS) → Val → Val → Bool} {K : List (Val × TyS)} (d : Val × HeldS)
    (G : List (Val × HeldS)) (i : Nat)
    (o : Val) (h : hostOf sm K d G = some (i, o)) :
    ∃ g, G[i]? = some g ∧ o = offTerm d.1 g.1 ∧
      sumLe K [o, d.2.size] 0 [g.2.size] 0 = true ∧
      slotsIn sm K o d.2.size g.2.slots d.2.slots = true := by
  have key : ∀ plain, hostOfP sm plain K d G 0 = some (i, o) →
      ∃ g, G[i]? = some g ∧ o = offTerm d.1 g.1 ∧
        sumLe K [o, d.2.size] 0 [g.2.size] 0 = true ∧
        slotsIn sm K o d.2.size g.2.slots d.2.slots = true := fun plain hp => by
    obtain ⟨g, hg, _, rest⟩ := hostOfP_spec d G 0 i o hp
    rw [Nat.sub_zero] at hg
    exact ⟨g, hg, rest⟩
  unfold hostOf at h
  split at h
  · next r hr => cases h; exact key true hr
  · exact key false h

/-- Each region of a list as a part of one of another: which, and how far
in. Nothing if one is a part of none. -/
def partsS (sm : List (Val × TyS) → Val → Val → Bool) (K : List (Val × TyS))
    (G : List (Val × HeldS)) :
    List (Val × HeldS) → Option (List (Nat × Val × HeldS))
  | [] => some []
  | d :: ds =>
    match hostOf sm K d G, partsS sm K G ds with
    | some (i, o), some ps => some ((i, o, d.2) :: ps)
    | _, _ => none

def partDen (ρ : Env) (x : Nat × Val × HeldS) : Part := (x.1, x.2.1.nat ρ, x.2.2.den ρ)

theorem Val.plus_nat_le (ρ : Env) (a b : Val) : (a.plus b).nat ρ ≤ a.nat ρ + b.nat ρ := by
  show ((a.plus b).den ρ).toNat ≤ _
  rw [Val.plus_den, BitVec.toNat_add]
  exact Nat.mod_le _ _

theorem partsS_den (ρ : Env) {sm : List (Val × TyS) → Val → Val → Bool} {K : List (Val × TyS)}
    {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ))
    (hsm : ∀ a b, sm K a b = true → a.den ρ = b.den ρ) (G : List (Val × HeldS)) :
    (D : List (Val × HeldS)) → (P : List (Nat × Val × HeldS)) → partsS sm K G D = some P →
    D.map (regionDen ρ) = (P.map (partDen ρ)).map (partRegion (G.map (regionDen ρ))) ∧
      ∀ x ∈ P.map (partDen ρ), PartOk (G.map (regionDen ρ)) x
  | [], P, h => by cases h; exact ⟨rfl, fun _ hx => nomatch hx⟩
  | d :: ds, P, h => by
    unfold partsS at h
    cases hh : hostOf sm K d G with
    | none => rw [hh] at h; cases h
    | some io =>
      obtain ⟨i, o⟩ := io
      cases hp : partsS sm K G ds with
      | none => rw [hh, hp] at h; cases h
      | some ps =>
        rw [hh, hp] at h
        cases h
        obtain ⟨g, hgi, hoff, hle, hsl⟩ := hostOf_spec d G i o hh
        obtain ⟨ih₁, ih₂⟩ := partsS_den ρ hg hsm G ds ps hp
        have hE : (G.map (regionDen ρ))[i]? = some (regionDen ρ g) := by
          rw [List.getElem?_map, hgi]; rfl
        have hle' : o.nat ρ + d.2.size.nat ρ ≤ g.2.size.nat ρ := by
          have := sumLe_den hle hg
          simpa [sumNat] using this
        have hlt : g.2.size.nat ρ < 2 ^ 64 := (g.2.size.den ρ).isLt
        have hok : PartOk (G.map (regionDen ρ)) (partDen ρ (i, o, d.2)) := by
          refine ⟨regionDen ρ g, hE, hle', ?_⟩
          intro p hp'
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
          simp only [slotsIn, List.all_eq_true, Bool.and_eq_true, List.any_eq_true] at hsl
          obtain ⟨hfit, q', hq', ho, hv⟩ := hsl q hq
          have hfit' : q.1.nat ρ + 8 ≤ d.2.size.nat ρ := by
            have := leS_den hfit hg
            simpa using this
          refine ⟨hfit', List.mem_map.mpr ⟨q', hq', ?_⟩⟩
          show ((q'.1.den ρ).toNat, q'.2.den ρ) = (o.nat ρ + q.1.nat ρ, q.2.den ρ)
          rw [hsm _ _ hv, Val.same_den ρ ho, Val.plus_den, BitVec.toNat_add]
          have e1 : (o.den ρ).toNat = o.nat ρ := rfl
          have e2 : (q.1.den ρ).toNat = q.1.nat ρ := rfl
          rw [e1, e2, Nat.mod_eq_of_lt (by omega)]
        refine ⟨?_, ?_⟩
        · rw [List.map_cons, List.map_cons, List.map_cons, ih₁]
          congr 1
          rw [partRegion_eq (x := partDen ρ (i, o, d.2)) hE]
          show (d.1.den ρ, d.2.den ρ) = (g.1.den ρ + BitVec.ofNat 64 (o.nat ρ), d.2.den ρ)
          rw [hoff, Val.nat, BitVec.ofNat_toNat, BitVec.setWidth_eq, ← offTerm_den]
        · intro x hx
          rw [List.map_cons] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hok
          · exact ih₂ x hx

/-- Whether no two parts overlap: of different regions, or one ending
before the other begins. -/
def apartS (K : List (Val × TyS)) : List (Nat × Val × HeldS) → Bool
  | [] => true
  | x :: xs =>
    (xs.all fun y => x.1 != y.1 || sumLe K [x.2.1, x.2.2.size] 0 [y.2.1] 0 ||
      sumLe K [y.2.1, y.2.2.size] 0 [x.2.1] 0) && apartS K xs

theorem apartS_den (ρ : Env) {K : List (Val × TyS)} {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) :
    (P : List (Nat × Val × HeldS)) → apartS K P = true →
    (P.map (partDen ρ)).Pairwise PartsApart
  | [], _ => .nil
  | x :: xs, h => by
    simp only [apartS, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨fun y hy => ?_, apartS_den ρ hg xs h.2⟩
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    rcases h.1 y' hy' with (h1 | h1) | h1
    · exact .inl h1
    · have := sumLe_den h1 hg
      simp only [sumNat, Nat.add_zero] at this
      exact .inr (.inl this)
    · have := sumLe_den h1 hg
      simp only [sumNat, Nat.add_zero] at this
      exact .inr (.inr this)

/-- Whether the parts of the region at place `i`, of `size` bytes, take in
the whole of it from byte `cur` on: one starts there, another where that one
ends, and so on to the end. -/
def coverFrom (P : List (Nat × Val × HeldS)) (i : Nat) (size : Val) : Nat → Val → Bool
  | fuel, cur =>
    if cur.same size then true
    else
      match fuel with
      | 0 => false
      | fuel + 1 =>
        match P.find? fun x => x.1 == i && x.2.1.same cur && !x.2.2.size.same (.lit 0) with
        | some x => coverFrom P i size fuel (cur.plus x.2.2.size)
        | none => false

theorem coverFrom_spec (ρ : Env) (P : List (Nat × Val × HeldS)) (i : Nat) (size : Val) :
    (fuel : Nat) → (cur : Val) → coverFrom P i size fuel cur = true →
    ∀ o, cur.nat ρ ≤ o → o < size.nat ρ →
      ∃ x ∈ P, x.1 = i ∧ x.2.1.nat ρ ≤ o ∧ o < x.2.1.nat ρ + x.2.2.size.nat ρ
  | fuel, cur, h, o, hlo, hhi => by
    unfold coverFrom at h
    split at h
    · next he =>
      have : cur.nat ρ = size.nat ρ := by
        show (cur.den ρ).toNat = (size.den ρ).toNat
        rw [Val.same_den ρ he]
      omega
    · cases fuel with
      | zero => cases h
      | succ fuel =>
        simp only at h
        cases hf : P.find? fun x => x.1 == i && x.2.1.same cur && !x.2.2.size.same (.lit 0) with
        | none => rw [hf] at h; cases h
        | some x =>
          rw [hf] at h
          have hx := List.find?_some hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hx
          have hcur : x.2.1.nat ρ = cur.nat ρ := by
            show (x.2.1.den ρ).toNat = (cur.den ρ).toNat
            rw [Val.same_den ρ hx.1.2]
          by_cases ho : o < cur.nat ρ + x.2.2.size.nat ρ
          · exact ⟨x, List.mem_of_find?_eq_some hf, hx.1.1, by omega, by omega⟩
          · exact coverFrom_spec ρ P i size fuel _ h o
              (Nat.le_trans (Val.plus_nat_le ρ _ _) (by omega)) hhi

/-- Whether the parts take in the whole of every region of a list. -/
def coverS (G : List (Val × HeldS)) (P : List (Nat × Val × HeldS)) : Bool :=
  (List.range G.length).all fun i =>
    match G[i]? with
    | some g => coverFrom P i g.2.size P.length (.lit 0)
    | none => true

theorem coverS_den (ρ : Env) (G : List (Val × HeldS)) (P : List (Nat × Val × HeldS))
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
    obtain ⟨x, hx, h1, h2, h3⟩ := coverFrom_spec ρ P i g.2.size _ _ this o (Nat.zero_le _) ho
    exact ⟨partDen ρ x, List.mem_map.mpr ⟨x, hx, rfl⟩, h1, h2, h3⟩

/-- The first region of a list that an extent lies within: its place,
counted from `i`, how far in the extent starts, and the region; among those
whose address the extent's is a number past (`plain`), or among the others. -/
def hostExtentP (plain : Bool) (K : List (Val × TyS)) (base size : Val) :
    List (Val × HeldS) → Nat → Option (Nat × Val × HeldS)
  | [], _ => none
  | g :: gs, i =>
    if (base.minus g.1).isSome == plain && sumLe K [offTerm base g.1, size] 0 [g.2.size] 0 then
      some (i, offTerm base g.1, g.2)
    else hostExtentP plain K base size gs (i + 1)

/-- The first region of a list that an extent lies within. -/
def hostExtent (K : List (Val × TyS)) (base size : Val) (G : List (Val × HeldS)) :
    Option (Nat × Val × HeldS) :=
  match hostExtentP true K base size G 0 with
  | some r => some r
  | none => hostExtentP false K base size G 0

/-- A stretch of a region, as a region: its bytes, from so far in and so
many, and the values the region says lie wholly in it. -/
def stretch (K : List (Val × TyS)) (g : Val × HeldS) (x : Val × Val) : Val × HeldS :=
  (g.1.plus x.1,
    ⟨x.2, g.2.slots.filterMap fun p =>
      if leS K x.1 0 p.1 0 && sumLe K [p.1] 8 [x.1, x.2] 0 then some (offTerm p.1 x.1, p.2)
      else none⟩)

/-! ## What is known -/

/-- Whether what is known one way is known another, read off the two. -/
def followsS (τ : TyS) : TyS → Bool
  | .any => true
  | .ptr S w off => τ == .ptr S w off || τ == .ptr S true off
  | .ref tag w off => τ == .ref tag w off || τ == .ref tag true off
  | .refN base idx w off => τ == .refN base idx w off || τ == .refN base idx true off
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
  | .code r f h k rest rows => τ == .code r f h k rest rows
  | .arr c υ st => τ == .arr c υ st
  | .zeroIff c υ => τ == .zeroIff c υ
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
  | .refN base idx w off, τ, h => by
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
  | .code r f hd k rest rows, τ, h => by
    simp only [followsS, beq_iff_eq] at h
    subst h
    exact .refl _ _
  | .arr c υ st, τ, h => by
    simp only [followsS, beq_iff_eq] at h
    subst h
    exact .refl _ _
  | .zeroIff c υ, τ, h => by
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
  | .refN .., h => nomatch h
  | .str _, h => nomatch h
  | .atom _, h => nomatch h
  | .code .., h => nomatch h
  | .arr .., h => nomatch h
  | .zeroIff .., h => nomatch h
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
off does not show; or it is that the value lies in a range, or is at most
or below another, and the arithmetic of what is known shows it. -/
def factFrom (ent : TyS → TyS → Bool) (G : List (Val × TyS)) (f : Val × TyS) : Bool :=
  outright f.1 f.2 || (G.any fun g => g.1.same f.1 && (followsS g.2 f.2 || ent g.2 f.2)) ||
    (match f.2 with
     | .range lo hi => rangeHolds G f.1 lo hi
     | .upTo t strict => upToHolds G f.1 t strict
     | .zeroIff c υ =>
       rangeHolds G c 1 (-1) && G.any fun g => g.1.same f.1 && followsS g.2 υ
     | .nullable (.zeroIff c υ) =>
       rangeHolds G c 1 (-1) && G.any fun g => g.1.same f.1 && followsS g.2 υ
     | _ => false) || arrFrom G f

/-- **What is so of itself, or follows from something known of the same
value, or by the ranges known, or as the rest of a row known, is so
wherever what is known is.** -/
theorem factFrom_hasTy {ent : TyS → TyS → Bool} (he : EntSound fetch sys ent) (ρ : Env)
    {G : List (Val × TyS)} {f : Val × TyS}
    (h : factFrom ent G f = true) (Ψ' : MemTy) (n : Nat)
    (hg : ∀ g ∈ G.map (fun g => (g.1.den ρ, g.2.den ρ)), HasTy fetch sys Ψ' n g.2 g.1) :
    HasTy fetch sys Ψ' n (f.2.den ρ) (f.1.den ρ) := by
  simp only [factFrom, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  have hg' : ∀ g ∈ G, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ) := fun g hgm =>
    hg (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩)
  rcases h with ((hout | ⟨g₀, hg₀, hs, hfo⟩) | hr) | harr
  · exact outright_hasTy ρ Ψ' n f.1 f.2 hout
  · have hsrc := hg (g₀.1.den ρ, g₀.2.den ρ) (List.mem_map.mpr ⟨g₀, hg₀, rfl⟩)
    rw [← Val.same_den ρ hs]
    rcases hfo with hfo | hen
    · exact hsrc.sub (followsS_sub ρ _ _ _ hfo)
    · exact he ρ _ _ _ hen Ψ' n hsrc
  · split at hr
    · next lo hi hτ =>
      rw [hτ]
      exact hasTy_range.mpr (rangeHolds_has hr hg')
    · next t strict hτ =>
      rw [hτ]
      exact hasTy_upTo.mpr (upToHolds_has hr hg')
    · next c υ hτ =>
      simp only [Bool.and_eq_true, List.any_eq_true] at hr
      obtain ⟨hc, g₀, hg₀, hs, hfo⟩ := hr
      have hne : c.den ρ ≠ 0 := fun h0 => by
        have hr' : c.den ρ - 1 ≤ (-1 : BitVec 64) - 1 := rangeHolds_has hc hg'
        rw [h0] at hr'
        exact absurd hr' (by decide)
      have hsrc := hg' g₀ hg₀
      rw [hτ, ← Val.same_den ρ hs]
      show HasTy fetch sys Ψ' n (if c.den ρ = 0 then .range 0 0 else υ.den ρ) _
      simp only [hne, ↓reduceIte]
      exact hsrc.sub (followsS_sub ρ _ _ _ hfo)
    · next c υ hτ =>
      simp only [Bool.and_eq_true, List.any_eq_true] at hr
      obtain ⟨hc, g₀, hg₀, hs, hfo⟩ := hr
      have hne : c.den ρ ≠ 0 := fun h0 => by
        have hr' : c.den ρ - 1 ≤ (-1 : BitVec 64) - 1 := rangeHolds_has hc hg'
        rw [h0] at hr'
        exact absurd hr' (by decide)
      have hsrc := hg' g₀ hg₀
      rw [hτ, ← Val.same_den ρ hs]
      refine (hasTy_nullable (τ := (TyS.zeroIff c υ).den ρ)).mpr (.inr ?_)
      show HasTy fetch sys Ψ' n (if c.den ρ = 0 then .range 0 0 else υ.den ρ) _
      simp only [hne, ↓reduceIte]
      exact hsrc.sub (followsS_sub ρ _ _ _ hfo)
    · cases hr
  · exact arrFrom_hasTy harr hg'

/-! ## The whole -/

/-- What a context knows, as it is said of the terms. -/
theorem knownS {ρ : Env} {Γ : CtxS} {Ψ' : MemTy} {m : Nat}
    (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' m g.2 g.1) :
    ∀ g ∈ Γ.known, HasTy fetch sys Ψ' m (g.2.den ρ) (g.1.den ρ) := fun g hgm =>
  hg (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩)

/-- So many times a term, by adding. -/
def Val.times : Nat → Val → Val
  | 0, _ => .lit 0
  | n + 1, v => .add (Val.times n v) v

theorem Val.times_den (ρ : Env) (v : Val) : (n : Nat) →
    (Val.times n v).den ρ = BitVec.ofNat 64 (n * (v.den ρ).toNat)
  | 0 => by simp [Val.times, Val.den]
  | n + 1 => by
    show (Val.times n v).den ρ + v.den ρ = _
    rw [Val.times_den ρ v n, Nat.succ_mul, BitVec.ofNat_add]
    simp

/-- **Whether rows are one after another from an address**, each of values
so far apart and so wide, and each one of the rows said: the first starts
there, the next where it ends, and so on. -/
def runOk (sm : Val → Val → Bool) (rows : List RowS) (st : Nat) (byte : Bool) :
    Val → List RowS → Bool
  | _, [] => true
  | cur, g :: gs =>
    rows.contains g && g.byte == byte && g.stride == st && sm g.addr cur &&
      runOk sm rows st byte (.add cur (Val.times st g.count)) gs

/-- Each value so far from where a run of rows starts, within all they come
to, is a value of one of them. -/
theorem runOk_cover {ρ : Env} {sm : Val → Val → Bool}
    (hsm : ∀ a b, sm a b = true → a.den ρ = b.den ρ) (rows : List RowS) (st : Nat) (byte : Bool) :
    (ch : List RowS) → (cur : Val) → runOk sm rows st byte cur ch = true →
      ∀ i, i < sumNat ρ (ch.map (·.count)) →
      ∃ g ∈ ch, g ∈ rows ∧ g.byte = byte ∧ g.stride = st ∧
        ∃ i', i' < (g.count.den ρ).toNat ∧
        cur.den ρ + BitVec.ofNat 64 (st * i) = g.addr.den ρ + BitVec.ofNat 64 (st * i')
  | [], _, _, i, hi => by simp [sumNat] at hi
  | g :: gs, cur, h, i, hi => by
    simp only [runOk, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨hmem, hb⟩, hst⟩, hsame⟩, hrest⟩ := h
    have ha := hsm _ _ hsame
    simp only [List.map_cons, sumNat] at hi
    by_cases hlt : i < (g.count.den ρ).toNat
    · exact ⟨g, List.mem_cons_self, hmem, hb, hst, i, hlt, by rw [ha]⟩
    · obtain ⟨g', hch', hm', hb', hst', i', hi', he⟩ :=
        runOk_cover hsm rows st byte gs (.add cur (Val.times st g.count)) hrest
          (i - (g.count.den ρ).toNat) (by simp only [Val.nat] at hi; omega)
      refine ⟨g', List.mem_cons_of_mem _ hch', hm', hb', hst', i', hi', ?_⟩
      rw [← he]
      show cur.den ρ + BitVec.ofNat 64 (st * i)
        = cur.den ρ + (Val.times st g.count).den ρ
          + BitVec.ofNat 64 (st * (i - (g.count.den ρ).toNat))
      rw [Val.times_den, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add,
        Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)]

/-- The runs of rows there may be from an address: of none; and of each
row seen to start there, with each run from where it ends. -/
def runsFrom (sm : Val → Val → Bool) (rows : List RowS) (st : Nat) (byte : Bool) :
    Nat → Val → List (List RowS)
  | 0, _ => [[]]
  | f + 1, cur =>
    [] :: (rows.filter fun g => g.byte == byte && g.stride == st && sm g.addr cur).flatMap fun g =>
      (runsFrom sm rows st byte f (.add cur (Val.times st g.count))).map (g :: ·)

/-- Whether a count is the one count there is: the same value, however
large. -/
def countIn (sm : Val → Val → Bool) (c : Val) : List Val → Bool
  | [d] => sm c d
  | _ => false

theorem countIn_le {ρ : Env} {sm : Val → Val → Bool}
    (hsm : ∀ a b, sm a b = true → a.den ρ = b.den ρ) {c : Val} {ds : List Val}
    (h : countIn sm c ds = true) : sumNat ρ [c] + 0 ≤ sumNat ρ ds + 0 := by
  match ds, h with
  | [d], h =>
    simp only [sumNat, Val.nat]
    rw [hsm _ _ h]
    omega

/-- **Whether a row wanted follows from the rows said**: it is of no
values; or some run of the rows said, of values as far apart and as wide,
one after another from where it starts, comes to as many values or more,
each row of a kind that is the kind wanted. -/
def rowFrom (sm : Val → Val → Bool) (K : List (Val × TyS)) (rows : List RowS) (r : RowS) : Bool :=
  sm r.count (.lit 0) ||
    (runsFrom sm rows r.stride r.byte rows.length r.addr).any fun ch =>
      runOk sm rows r.stride r.byte r.addr ch &&
        (countIn sm r.count (ch.map (·.count)) || sumLe K [r.count] 0 (ch.map (·.count)) 0) &&
        ch.all fun g => followsS g.ty r.ty

/-- **Whether the first context may be regarded as the second**, two terms
being taken for the same value where `sm` says so, given what the first
context knows. -/
def regardWith (sm : List (Val × TyS) → Val → Val → Bool) (ent : TyS → TyS → Bool)
    (Γ Δ : CtxS) : Bool :=
  (allRegs.all fun r => sm Γ.known (Γ.regs.get r) (Δ.regs.get r)) && Γ.flags == Δ.flags &&
    (match partsS sm Γ.known Γ.held Δ.held with
     | some P => apartS Γ.known P && coverS Γ.held P
     | none => false) &&
    Δ.known.all (factFrom ent Γ.known) && Δ.rest == Γ.rest &&
    Δ.rows.all (rowFrom (sm Γ.known) Γ.known Γ.rows) &&
    Δ.rows.all fun r => r.fed.isNone || Γ.rows.any fun g =>
      g.fed == r.fed && g.byte == r.byte && g.stride == r.stride &&
        sm Γ.known g.addr r.addr && sm Γ.known g.count r.count

theorem regardWith_sound {sm : List (Val × TyS) → Val → Val → Bool} {ent : TyS → TyS → Bool}
    (he : EntSound fetch sys ent) (ρ : Env) {Γ Δ : CtxS}
    (hsm : ∀ (Ψ' : MemTy) (n : Nat),
      (∀ g ∈ Γ.known, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) →
      ∀ a b, sm Γ.known a b = true → a.den ρ = b.den ρ)
    (h : regardWith sm ent Γ Δ = true) :
    Regards fetch sys Ψ (Γ.den ρ) (Δ.den ρ) := by
  simp only [regardWith, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hr, hf⟩, hh⟩, hk⟩, hrest⟩, hrows⟩, hnofed⟩ := h
  cases hP : partsS sm Γ.known Γ.held Δ.held with
  | none => rw [hP] at hh; cases hh
  | some P =>
    rw [hP] at hh
    simp only [Bool.and_eq_true] at hh
    intro k Ψ' hext hwf s hw
    have hg : ∀ g ∈ Γ.known, HasTy fetch sys Ψ' k (g.2.den ρ) (g.1.den ρ) := knownS hw.known
    obtain ⟨hmap, hok⟩ := partsS_den ρ hg (hsm Ψ' k hg) Γ.held Δ.held P hP
    refine Regards.parts (Γ := Γ.den ρ) (Δ := Δ.den ρ) (E := Γ.held.map (regionDen ρ))
      (F := restDen ρ Γ.rest)
      (L := P.map (partDen ρ)) ?_ ?_ ?_ rfl ?_ hok (apartS_den ρ hg P hh.1)
      (coverS_den ρ Γ.held P hh.2) (fun k' Ψ'' s' hw' r hr' i hi => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (show r ∈ Δ.rows.map (RowS.den ρ) from hr')
        have hg'' := knownS hw'.known
        have hsm' := hsm Ψ'' k' hg''
        rcases Bool.or_eq_true_iff.mp (hrows x hx) with h0 | hrun
        · have e0 : x.count.den ρ = 0 := hsm' _ _ h0
          exact absurd hi (by show ¬ i < (x.count.den ρ).toNat; rw [e0]; exact Nat.not_lt_zero i)
        · obtain ⟨ch, -, hrun⟩ := List.any_eq_true.mp hrun
          simp only [Bool.and_eq_true] at hrun
          obtain ⟨⟨hok, hcnt⟩, htys⟩ := hrun
          have hle : sumNat ρ [x.count] + 0 ≤ sumNat ρ (ch.map (·.count)) + 0 :=
            (Bool.or_eq_true_iff.mp hcnt).elim (countIn_le hsm') (fun h => sumLe_den h hg'')
          obtain ⟨g, hgr, hgm, hb, hst, i', hi', he⟩ :=
            runOk_cover (ρ := ρ) hsm' Γ.rows x.stride x.byte ch x.addr hok i (by
              simp only [sumNat, Val.nat] at hle
              have : i < (x.count.den ρ).toNat := hi
              omega)
          have hty := hw'.rows (g.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩) i' hi'
          show HasTy fetch sys Ψ'' k' (x.ty.den ρ)
            (cellAt s' x.byte (x.addr.den ρ + BitVec.ofNat 64 (x.stride * i)))
          rw [he, ← hb, ← hst]
          exact HasTy.sub (followsS_sub ρ _ _ _ (List.all_eq_true.mp htys g hgr)) hty)
        (fun k' Ψ'' s' hw' r hr' off ho => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (show r ∈ Δ.rows.map (RowS.den ρ) from hr')
          have ho' : x.fed.map (BitVec.ofNat 64) = some off := ho
          rcases Bool.or_eq_true_iff.mp (hnofed x hx) with hn | hany
          · have hn' : x.fed = none := by simpa using hn
            rw [hn'] at ho'
            cases ho'
          · obtain ⟨g, hgm, hc⟩ := List.any_eq_true.mp hany
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨⟨⟨⟨hfe, hb⟩, hst⟩, ha⟩, hcn⟩ := hc
            have hsm' := hsm Ψ'' k' (knownS hw'.known)
            have hF := hw'.fed (g.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩) off
              (show g.fed.map (BitVec.ofNat 64) = some off by rw [hfe]; exact ho')
            show FedRow s' (RowOf.mk (x.addr.den ρ) (x.count.den ρ) x.stride x.byte (x.ty.den ρ)
              (x.fed.map (BitVec.ofNat 64))) off
            rw [← hsm' _ _ ha, ← hsm' _ _ hcn, ← hst, ← hb]
            exact hF)
        k Ψ' hext hwf s hw
    · funext r
      exact (hsm Ψ' k hg _ _ (hr r (mem_allRegs r))).symm
    · show Δ.flags.den ρ = Γ.flags.den ρ
      rw [hf]
    · intro f hf' Ψ' n hg
      obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hf'
      exact factFrom_hasTy he ρ (hk g hg') Ψ' n hg
    · show Δ.held.map (regionDen ρ) ++ restDen ρ Δ.rest = _
      rw [hmap, hrest]

/-- Two terms taken for the same value only as `Val.same` finds them so. -/
def sameK : List (Val × TyS) → Val → Val → Bool := fun _ a b => a.same b

/-- **Whether the first context may be regarded as the second.** -/
def regardS (ent : TyS → TyS → Bool) (Γ Δ : CtxS) : Bool := regardWith sameK ent Γ Δ

theorem regardS_sound {ent : TyS → TyS → Bool} (he : EntSound fetch sys ent) (ρ : Env)
    {Γ Δ : CtxS} (h : regardS ent Γ Δ = true) :
    Regards fetch sys Ψ (Γ.den ρ) (Δ.den ρ) :=
  regardWith_sound he ρ (fun _ _ _ _ _ hs => Val.same_den ρ hs) h

/-- The place among the regions held of one at an address, of a size. -/
def findRegion (base : Val) (size : Nat) : List (Val × HeldS) → Nat → Option Nat
  | [], _ => none
  | g :: gs, i =>
    if g.1.same base && g.2.size.same (litNat size) && decide (size < 2 ^ 64) then some i
    else findRegion base size gs (i + 1)

theorem findRegion_spec (ρ : Env) {base : Val} {size : Nat} : (G : List (Val × HeldS)) →
    (i₀ j : Nat) → findRegion base size G i₀ = some j →
    ∃ g, G[j - i₀]? = some g ∧ i₀ ≤ j ∧ g.1.same base = true ∧ g.2.size.nat ρ = size
  | [], _, _, h => nomatch h
  | g :: gs, i₀, j, h => by
    unfold findRegion at h
    split at h
    · next hc =>
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      refine ⟨g, by simp, Nat.le_refl _, hc.1.1, ?_⟩
      show (g.2.size.den ρ).toNat = size
      rw [Val.same_den ρ hc.1.2]
      exact litNat_nat ρ hc.2
    · obtain ⟨g', hg', hle, rest⟩ := findRegion_spec ρ gs (i₀ + 1) j h
      refine ⟨g', ?_, by omega, rest⟩
      have e : j - i₀ = (j - (i₀ + 1)) + 1 := by omega
      rw [e, List.getElem?_cons_succ]
      exact hg'

end TypedAsm.U
