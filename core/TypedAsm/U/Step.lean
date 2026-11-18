import TypedAsm.U.FindFact
import TypedAsm.U.FlagsS
import TypedAsm.U.RegardS
import TypedAsm.U.Bridge
import TypedAsm.U.Guard
import TypedAsm.U.Text
import TypedAsm.U.Span
import TypedAsm.U.FindArr

/-!
# The checker's step

One function, for every instruction that is described. It reads the
description: the registers used, the bytes read and written, and where they
are. The bytes are found among the regions the context holds, by the
address as a term. What is read is the value the region holds there, or a
value the context does not say, which is given a name. Each register
written holds the term for what the instruction gives it. What is written
is put where it goes. And the address control goes to is given, as a term.

It is proved to be what the one statement that types every instruction
gives, for the machine.
-/

namespace TypedAsm.U

open TypedAsm

/-- The value a region holds at a place, if it holds one there. -/
def HeldS.slotAt (S : HeldS) (o : Val) : Option Val :=
  match S.slots.find? fun p => p.1.same o with
  | some p => some p.2
  | none => none

theorem HeldS.slotAt_mem {S : HeldS} {o : Val} {v : Val} (h : S.slotAt o = some v) :
    ∃ o', (o', v) ∈ S.slots ∧ o'.same o = true := by
  unfold HeldS.slotAt at h
  split at h
  · next p hp =>
    cases h
    exact ⟨p.1, List.mem_of_find?_eq_some hp,
      List.find?_some (p := fun q : Val × Val => q.1.same o) hp⟩
  · cases h

theorem HeldS.slotAt_den (ρ : Env) {S : HeldS} {o : Val} {v : Val} (h : S.slotAt o = some v) :
    (o.nat ρ, v.den ρ) ∈ (S.den ρ).vals := by
  obtain ⟨o', hm, hs⟩ := HeldS.slotAt_mem h
  refine List.mem_map.mpr ⟨(o', v), hm, ?_⟩
  show ((o'.den ρ).toNat, v.den ρ) = ((o.den ρ).toNat, v.den ρ)
  rw [Val.same_den ρ hs]

/-- A region saying nothing of the bytes from a place on, as many as some
terms come to and `n` more: only the values shown, by what is known, to
keep clear of them are left. -/
def HeldS.clearT (K : List (Val × TyS)) (S : HeldS) (o : Val) (ls : List Val) (n : Nat) : HeldS :=
  ⟨S.size, S.slots.filter fun p => sumLe K (o :: ls) n [p.1] 0 || leS K p.1 8 o 0⟩

/-- The value fewer than eight bytes stored at a place fall wholly in,
where the region is said to hold a number written out there and what is
stored is a number written out: where that value is, and the number with
those bytes replaced. -/
def HeldS.bytesInto (S : HeldS) (o : Val) (n : Nat) (v : Val) : Option (Val × Val) :=
  match v with
  | .lit x =>
    S.slots.findSome? fun p =>
      match o.minus p.1, p.2 with
      | some d, .lit w =>
        if d.toNat + n ≤ 8 then some (p.1, .lit (putBytes w d.toNat n x)) else none
      | _, _ => none
  | _ => none

/-- A region with `n` of its bytes, from a place, given a value. Of eight
bytes, the region then holds the value there. Of fewer stored wholly into
a number the region held, it holds the number with those bytes replaced. -/
def HeldS.put (K : List (Val × TyS)) (S : HeldS) (o : Val) (n : Nat) (v : Val) : HeldS :=
  if n = 8 then ⟨S.size, (o, v) :: (S.clearT K o [] 8).slots⟩
  else if n < 8 then
    match S.bytesInto o n v with
    | some c => ⟨S.size, c :: (S.clearT K o [] n).slots⟩
    | none => S.clearT K o [] n
  else S.clearT K o [] n

theorem HeldS.put_size (K : List (Val × TyS)) (S : HeldS) (o : Val) (n : Nat) (v : Val) :
    (S.put K o n v).size = S.size := by
  unfold HeldS.put
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

theorem HeldS.clearT_mem {ρ : Env} {Ψ' : MemTy} {m : Nat} {K : List (Val × TyS)}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' m (g.2.den ρ) (g.1.den ρ)) {S : HeldS} {o : Val}
    {ls : List Val} {n : Nat} {p : Nat × BitVec 64} (hp : p ∈ ((S.clearT K o ls n).den ρ).vals) :
    p ∈ (S.den ρ).vals ∧ (p.1 + 8 ≤ o.nat ρ ∨ o.nat ρ + (sumNat ρ ls + n) ≤ p.1) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hq' := List.mem_filter.mp hq
  refine ⟨List.mem_map.mpr ⟨q, hq'.1, rfl⟩, ?_⟩
  rcases Bool.or_eq_true _ _ |>.mp hq'.2 with h | h
  · have := sumLe_den h hg
    simp only [sumNat, Nat.add_zero] at this
    exact .inr (by show _ ≤ q.1.nat ρ; omega)
  · have := leS_den h hg
    exact .inl (by show q.1.nat ρ + 8 ≤ _; omega)

theorem HeldS.bytesInto_den {ρ : Env} {S : HeldS} {o v : Val} {n : Nat} {c : Val × Val}
    (h : S.bytesInto o n v = some c) :
    ∃ w d, slotDen ρ c = ((c.1.den ρ).toNat, putBytes w d n (v.den ρ)) ∧
      ((c.1.den ρ).toNat, w) ∈ (S.den ρ).vals ∧
      BitVec.ofNat 64 (o.nat ρ) = BitVec.ofNat 64 (c.1.den ρ).toNat + BitVec.ofNat 64 d ∧
      d + n ≤ 8 := by
  unfold HeldS.bytesInto at h
  split at h
  · next x =>
    obtain ⟨p, hp, hx⟩ := List.exists_of_findSome?_eq_some h
    split at hx
    · next d w hd hlit =>
      split at hx
      · next hlt =>
        cases hx
        refine ⟨w, d.toNat, rfl, List.mem_map.mpr ⟨p, hp, ?_⟩, ?_, hlt⟩
        · show ((p.1.den ρ).toNat, p.2.den ρ) = _
          rw [hlit]
          rfl
        · rw [Val.nat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_toNat,
            BitVec.setWidth_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          exact Val.minus_den ρ hd
      · cases hx
    · cases hx
  · cases h

theorem HeldS.put_mem {ρ : Env} {Ψ' : MemTy} {m : Nat} {K : List (Val × TyS)}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' m (g.2.den ρ) (g.1.den ρ)) {S : HeldS} {o : Val}
    {n : Nat} {v : Val} {p : Nat × BitVec 64} (hp : p ∈ ((S.put K o n v).den ρ).vals) :
    (p ∈ (S.den ρ).vals ∧ (p.1 + 8 ≤ o.nat ρ ∨ o.nat ρ + n ≤ p.1)) ∨
      (n = 8 ∧ p = (o.nat ρ, v.den ρ)) ∨
      (n < 8 ∧ ∃ c w d, p = (c, putBytes w d n (v.den ρ)) ∧ (c, w) ∈ (S.den ρ).vals ∧
        BitVec.ofNat 64 (o.nat ρ) = BitVec.ofNat 64 c + BitVec.ofNat 64 d ∧ d + n ≤ 8) := by
  have clr : ∀ k, p ∈ ((S.clearT K o [] k).den ρ).vals →
      p ∈ (S.den ρ).vals ∧ (p.1 + 8 ≤ o.nat ρ ∨ o.nat ρ + k ≤ p.1) := fun k hp => by
    have := HeldS.clearT_mem hg (S := S) (o := o) (ls := []) (n := k) hp
    simp only [sumNat, Nat.zero_add] at this
    exact this
  unfold HeldS.put at hp
  split at hp
  · next h8 =>
    rcases List.mem_cons.mp (show p ∈ slotDen ρ (o, v) ::
        (S.clearT K o [] 8).slots.map (slotDen ρ) from hp) with rfl | hp
    · exact .inr (.inl ⟨h8, rfl⟩)
    · have := clr 8 hp
      exact .inl ⟨this.1, by omega⟩
  · split at hp
    · next h1 =>
      split at hp
      · next c hc =>
        rcases List.mem_cons.mp (show p ∈ slotDen ρ c ::
            (S.clearT K o [] n).slots.map (slotDen ρ) from hp) with rfl | hp
        · obtain ⟨w, d, he, hmem, ho, hd⟩ := HeldS.bytesInto_den (ρ := ρ) hc
          exact .inr (.inr ⟨h1, _, w, d, he, hmem, ho, hd⟩)
        · exact .inl (clr n hp)
      · exact .inl (clr n hp)
    · exact .inl (clr n hp)

/-- What is shown of reading given what a context knows, is so of reading. -/
theorem Reads.withKnown {Γ : Ctx} {a : BitVec 64} {n : Nat} {P : BitVec 64 → Ctx → Prop}
    (h : ∀ (k : Nat) (Ψ' : MemTy), (∀ g ∈ Γ.known, HasTy fetch sys Ψ' k g.2 g.1) →
      Reads fetch sys Ψ Γ a n P) : Reads fetch sys Ψ Γ a n P :=
  fun k Ψ' he hwf s hw => h k Ψ' hw.known k Ψ' he hwf s hw

/-- And of writing. -/
theorem Writes.withKnown {Γ Γw : Ctx} {a v : BitVec 64} {n : Nat} (hv : Γw.val = Γ.val)
    (hf : Γw.flags = Γ.flags)
    (h : ∀ (k : Nat) (Ψ' : MemTy), (∀ g ∈ Γ.known, HasTy fetch sys Ψ' k g.2 g.1) →
      Writes fetch sys Ψ Γ a n v Γw) : Writes fetch sys Ψ Γ a n v Γw :=
  ⟨hv, hf, fun k Ψ' he hwf s hw => (h k Ψ' hw.known).2.2 k Ψ' he hwf s hw⟩

theorem Reads.mono {Γ : Ctx} {a : BitVec 64} {n : Nat} {P P' : BitVec 64 → Ctx → Prop}
    (h : Reads fetch sys Ψ Γ a n P) (hP : ∀ x Δ, P x Δ → P' x Δ) : Reads fetch sys Ψ Γ a n P' := by
  intro k Ψ' he hwf s hw
  obtain ⟨hr, Γr, hp, hv, hf, hw'⟩ := h k Ψ' he hwf s hw
  exact ⟨hr, Γr, hP _ _ hp, hv, hf, hw'⟩

/-- A region the context holds, as terms, is one it holds. -/
theorem CtxS.held_den (ρ : Env) (Γ : CtxS) {j : Nat} {b : Val} {S : HeldS}
    (h : Γ.held[j]? = some (b, S)) : (Γ.den ρ).held[j]? = some (b.den ρ, S.den ρ) := by
  show ((Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest)[j]? = _
  have hj : j < (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hj, List.getElem?_map, h]
  rfl

/-- The fact a context has that an address is a pointer to text: the first,
of a value the address is. With what says whether there is more. -/
def findStr (a : Val) : List (Val × TyS) → Option (Val × Val)
  | [] => none
  | (q, .str c) :: rest => if q.same a then some (q, c) else findStr a rest
  | _ :: rest => findStr a rest

theorem findStr_spec {a : Val} : (l : List (Val × TyS)) → {q c : Val} →
    findStr a l = some (q, c) → (q, TyS.str c) ∈ l ∧ q.same a = true
  | [], _, _, h => by cases h
  | (p, τ) :: rest, q, c, h => by
    have tail : findStr a rest = some (q, c) → (q, TyS.str c) ∈ (p, τ) :: rest ∧ q.same a = true :=
      fun h' => ⟨List.mem_cons_of_mem _ (findStr_spec rest h').1, (findStr_spec rest h').2⟩
    cases τ with
    | str c' =>
      simp only [findStr] at h
      split at h
      · next hs => cases h; exact ⟨List.mem_cons_self, hs⟩
      · exact tail h
    | _ => exact tail h

/-- A term for so many bytes read: no more than so many bytes, which the
term says by the operator at its head. -/
def narrow (n : Nat) (x : Val) : Val :=
  match n with
  | 1 => .un .low8 x
  | 2 => .un .low16 x
  | 4 => .un (.trunc .w32) x
  | _ => x

theorem narrow_den (ρ : Env) (n : Nat) (x : Val) : (narrow n x).den ρ = cutN n (x.den ρ) := by
  by_cases h1 : n = 1
  · subst h1; rfl
  · by_cases h2 : n = 2
    · subst h2; rfl
    · by_cases h4 : n = 4
      · subst h4; rfl
      · unfold narrow cutN
        split <;> first | contradiction | (split <;> first | contradiction | rfl)

/-- **Eight bytes read in a region held are then held as what was read**:
the region says, of those bytes, that they hold the value. -/
theorem Reads.heldName {Γ : Ctx} {k : Nat} {b : BitVec 64} {S : Held} {o : Nat}
    (hk : Γ.held[k]? = some (b, S)) (hin : o + 8 ≤ S.size) :
    Reads fetch sys Ψ Γ (b + BitVec.ofNat 64 o) 8
      (fun x Γr => Γr = { Γ with held := Γ.held.set k (b, ⟨S.size, (o, x) :: S.vals⟩) }) := by
  intro j Ψ' he hwf s hw
  have hmem : (b, S) ∈ Γ.held := List.mem_of_getElem? hk
  exact ⟨State.canRead_of_canWrite (State.canWrite_sub (n := S.size) (hw.held.perm (b, S) hmem) hin),
    _, rfl, rfl, rfl, hw.nameSlot hk hin⟩

/-- **The regions held once eight bytes of one are read that it says
nothing of**: that region saying, of those bytes, that they hold the name
`k`, which is what was read. So what is learnt of the value read is known
of what the region holds. Nothing where the bytes are not eight, are not
in a region held at a place written out, or hold a value already. -/
def nameRead (Γ : CtxS) (k : Nat) (next : BitVec 64) :
    Option (Mem × Nat) → Option (List (Val × HeldS))
  | some (m, n) =>
    if n = 8 then
      match findHeldP true Γ.known (eaS Γ.regs next m) [] 8 Γ.held 0 with
      | some (j, b, S, o) =>
        match S.slotAt o with
        | none =>
          if o.under k then some (Γ.held.set j (b, ⟨S.size, (o, .var k) :: S.slots⟩)) else none
        | some _ => none
      | none => none
    else none
  | none => none

theorem nameRead_sound {ρ : Env} {Γ : CtxS} {k : Nat} {next : BitVec 64} {m : Mem} {n : Nat}
    {heldN : List (Val × HeldS)} (hu : Γ.under k = true)
    (h : nameRead Γ k next (some (m, n)) = some heldN) :
    Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
      (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with held := heldN } ∧
        (Val.var k).den (ρ.setVal k x) = x) := by
  simp only [nameRead] at h
  split at h
  · next h8 =>
    subst h8
    split at h
    · next j b S o hfind =>
      split at h
      · split at h
        · next hou =>
          cases h
          refine Reads.withKnown fun k' Ψ' hg0 => ?_
          obtain ⟨i, hi, hl, hin, ha⟩ := findHeldP_spec (ρ := ρ) Γ.held 0 hfind (knownS hg0)
          have hji : j = i := by omega
          subst hji
          rw [← eaS_den, ha]
          simp only [sumNat, Nat.zero_add] at hin
          refine (Reads.heldName (CtxS.held_den ρ Γ hl) hin).mono ?_
          rintro x Γr rfl
          refine ⟨?_, Env.setVal_get_self ρ k x⟩
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          have hjlt : j < (Γ.held.map fun b =>
              (b.1.den (ρ.setVal k x), b.2.den (ρ.setVal k x))).length := by
            rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hl).1
          have hreg : (b.den (ρ.setVal k x), S.den (ρ.setVal k x)) = (b.den ρ, S.den ρ) := by
            have h1 := CtxS.held_den (ρ.setVal k x) Γ hl
            have h2 := CtxS.held_den ρ Γ hl
            rw [hΓ] at h1
            exact Option.some.inj (h1.symm.trans h2)
          have hb : b.den (ρ.setVal k x) = b.den ρ := congrArg Prod.fst hreg
          have hS : S.den (ρ.setVal k x) = S.den ρ := congrArg Prod.snd hreg
          refine ctx_ext (congrArg CtxOf.val hΓ).symm (congrArg CtxOf.flags hΓ).symm ?_
            (congrArg CtxOf.known hΓ).symm (congrArg CtxOf.rows hΓ).symm
          show (Γ.den ρ).held.set j _
            = (Γ.held.set j (b, ⟨S.size, (o, .var k) :: S.slots⟩)).map
                (fun b => (b.1.den (ρ.setVal k x), b.2.den (ρ.setVal k x)))
              ++ restDen (ρ.setVal k x) Γ.rest
          rw [List.map_set, ← List.set_append_left _ _ hjlt]
          have hheld : (Γ.held.map fun b => (b.1.den (ρ.setVal k x), b.2.den (ρ.setVal k x)))
              ++ restDen (ρ.setVal k x) Γ.rest = (Γ.den ρ).held := congrArg CtxOf.held hΓ
          rw [hheld]
          congr 1
          show (b.den ρ, (⟨(S.den ρ).size, (o.nat ρ, x) :: (S.den ρ).vals⟩ : Held))
            = (b.den (ρ.setVal k x),
                (⟨(S.size.den (ρ.setVal k x)).toNat,
                  ((o.den (ρ.setVal k x)).toNat, (Val.var k).den (ρ.setVal k x))
                    :: S.slots.map (slotDen (ρ.setVal k x))⟩ : Held))
          have hsz : (S.size.den (ρ.setVal k x)).toNat = (S.den ρ).size :=
            congrArg (fun H : Held => H.size) hS
          have hvals : S.slots.map (slotDen (ρ.setVal k x)) = (S.den ρ).vals :=
            congrArg (fun H : Held => H.vals) hS
          rw [hb, hsz, hvals, Val.den_setVal ρ k x o hou,
            show (Val.var k).den (ρ.setVal k x) = x from Env.setVal_get_self ρ k x]
          rfl
        · cases h
      · cases h
    · cases h
  · cases h

/-- The bytes read in a region the context holds, of those an address is a
number into (`plain`) or of the others: the value held there, where one is
held at those eight bytes, and otherwise the name `k`. -/
def readHeldP (plain : Bool) (Γ : CtxS) (k : Nat) (a : Val) (n : Nat) :
    Option (Val × List (Val × TyS)) :=
  match findHeldP plain Γ.known a [] n Γ.held 0 with
  | some (_, _, S, o) =>
    if n = 8 then
      match S.slotAt o with
      | some v => some (v, [])
      | none => some (.var k, [])
    else some (narrow n (.var k), [])
  | none => none

theorem readHeldP_sound {ρ : Env} {plain : Bool} {Γ : CtxS} {k : Nat} {a : Val} {n : Nat}
    {cell : Val} {extra : List (Val × TyS)} (hu : Γ.under k = true)
    (h : readHeldP plain Γ k a n = some (cell, extra)) :
    Reads fetch sys Ψ (Γ.den ρ) (a.den ρ) n
      (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
        cell.den (ρ.setVal k x) = x) := by
  unfold readHeldP at h
  split at h
  · next j b S o hfind =>
    refine Reads.withKnown fun k' Ψ' hg0 => ?_
    obtain ⟨i, hi, hl, hin, ha⟩ := findHeldP_spec (ρ := ρ) Γ.held 0 hfind (knownS hg0)
    rw [ha]
    simp only [sumNat, Nat.zero_add] at hin
    refine (Reads.held (CtxS.held_den ρ Γ hl) hin).narrow.mono ?_
    rintro x Γr ⟨⟨rfl, hslot⟩, hcut⟩
    -- nothing is learnt, and the context is as it was
    have key : ∀ c : Val, c.den (ρ.setVal k x) = x →
        (some (c, ([] : List (Val × TyS))) = some (cell, extra)) →
        Γ.den ρ = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
          cell.den (ρ.setVal k x) = x := by
      intro c hc he
      cases he
      exact ⟨(CtxS.den_setVal ρ k x Γ hu).symm, hc⟩
    split at h
    · next h8 =>
      split at h
      · next v hv =>
        have hx := hslot h8 (v.den ρ) (HeldS.slotAt_den ρ hv)
        obtain ⟨o', hm, _⟩ := HeldS.slotAt_mem hv
        -- the slot's term mentions no name from `k` on
        have hcu : v.under k = true := by
          simp only [CtxS.under, heldUnder, Bool.and_eq_true, List.all_eq_true] at hu
          exact ((hu.1.1.1.2 (b, S) (List.mem_of_getElem? hl)).2 (o', v) hm).2
        exact key v (by rw [Val.den_setVal ρ k x _ hcu]; exact hx.symm) h
      · exact key (.var k) (Env.setVal_get_self ρ k x) h
    · exact key (narrow n (.var k))
        (by rw [narrow_den, show (Val.var k).den (ρ.setVal k x) = x from
          Env.setVal_get_self ρ k x]; exact hcut) h
  · cases h

/-- What the context holds once bytes of a region it holds are written: the
region holds the value written there, and of its other values those shown
to keep clear of the bytes. -/
def writeHeldP (plain : Bool) (Γ : CtxS) (a : Val) (n : Nat) (v : Val) :
    Option (List (Val × HeldS)) :=
  match findHeldP plain Γ.known a [] n Γ.held 0 with
  | some (j, b, S, o) =>
    if n ≤ 8 then some (Γ.held.set j (b, S.put Γ.known o n v)) else none
  | none => none

theorem writeHeldP_sound {ρ : Env} {plain : Bool} {Γ : CtxS} {a v : Val} {n : Nat}
    {held' : List (Val × HeldS)} (h : writeHeldP plain Γ a n v = some held')
    (hrows : Γ.rows = []) :
    Writes fetch sys Ψ (Γ.den ρ) (a.den ρ) n (v.den ρ) (CtxS.den ρ { Γ with held := held' }) := by
  unfold writeHeldP at h
  split at h
  · next j b S o hfind =>
    split at h
    · next hn =>
      cases h
      refine Writes.withKnown rfl rfl fun k' Ψ' hg0 => ?_
      have hg := knownS hg0
      obtain ⟨i, hi, hl, hin, ha⟩ := findHeldP_spec (ρ := ρ) Γ.held 0 hfind hg
      have hji : j = i := by omega
      subst hji
      rw [ha]
      simp only [sumNat, Nat.zero_add] at hin
      have hW := Writes.heldTo (fetch := fetch) (sys := sys) (Ψ := Ψ)
        (S' := (S.put Γ.known o n v).den ρ) (v.den ρ) (CtxS.held_den ρ Γ hl) hin hn
        (by show ((S.put Γ.known o n v).size.den ρ).toNat = _; rw [HeldS.put_size]; rfl)
        (fun p hp => HeldS.put_mem hg hp) (by show Γ.rows.map _ = []; rw [hrows]; rfl)
      have e : CtxS.den ρ { Γ with held := Γ.held.set j (b, S.put Γ.known o n v) }
          = { Γ.den ρ with
              held := (Γ.den ρ).held.set j (b.den ρ, (S.put Γ.known o n v).den ρ) } := by
        refine ctx_ext rfl rfl ?_ rfl
        show (Γ.held.set j (b, S.put Γ.known o n v)).map (fun b => (b.1.den ρ, b.2.den ρ))
            ++ restDen ρ Γ.rest
          = ((Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest).set j _
        have hj : j < (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)).length := by
          rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hl).1
        rw [List.set_append_left _ _ hj, List.map_set]
      rw [e]
      exact hW
    · cases h
  · cases h

/-- The term for the bytes an instruction reads, and what reading them
tells. Nothing where it reads none. In a region the context holds: the value
held there, where one is held at those eight bytes, and otherwise the name
`k`, for a value the context does not say. In a block a value is known to
point into: the name `k`, of which is then known what the block's shape
says is at those bytes. A byte of text, through a pointer to text: the name
`k`, and of the pointer it is then known that there is more unless that
byte is nought. One of a row of values a pointer is known to be the address
of, where the ranges known show it is fewer along than there are: the name
`k`, known to be of the type the row's values are. -/
def readCell (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64) :
    Option (Mem × Nat) → Option (Val × List (Val × TyS))
  | none => some (.lit 0, [])
  | some (m, n) =>
    match readHeldP true Γ k (eaS Γ.regs next m) n with
    | some r => some r
    | none =>
      match findFact kinds (eaS Γ.regs next m) n Γ.known with
      | some (_, Sh, _, _, o) => some (narrow n (.var k), readFactsS Sh o n (.var k))
      | none =>
        if n = 1 then
          match findStr (eaS Γ.regs next m) Γ.known with
          | some (q, _) => some (narrow 1 (.var k), [(q, .str (narrow 1 (.var k)))])
          | none => none
        else if n = 8 then
          match findArr Γ.known (eaS Γ.regs next m) Γ.known with
          | some (_, _, τ, _) => some (.var k, [(.var k, τ)])
          | none => none
        else none

theorem readCell_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {k : Nat} {next : BitVec 64} {cell : Val}
    {extra : List (Val × TyS)} (hu : Γ.under k = true) :
    (rd : Option (Mem × Nat)) → readCell kinds Γ k next rd = some (cell, extra) →
    match rd with
    | some (m, n) => Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
        (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
          cell.den (ρ.setVal k x) = x)
    | none => extra = [] ∧ cell.den (ρ.setVal k 0) = 0
  | none, h => by cases h; exact ⟨rfl, rfl⟩
  | some (m, n), h => by
    simp only [readCell] at h
    split at h
    · next r hr =>
      cases h
      show Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n _
      rw [← eaS_den]
      exact readHeldP_sound hu hr
    · split at h
      · next p Sh w off o hfind =>
        cases h
        obtain ⟨τ, hmem, hpt, hin, ha⟩ := findFact_spec (ρ := ρ) Γ.known hfind
        have hf : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known :=
          List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
        have haddr : eaOf (Γ.den ρ).val next m + BitVec.ofNat 64 off
            = p.den ρ + BitVec.ofNat 64 o := by
          rw [← eaS_den]; exact ha
        refine (Reads.shared hf (TyS.pointee_den hk ρ hpt) haddr (by rw [ShapeS.den_size]; exact hin)).narrow.mono ?_
        rintro x Γr ⟨rfl, hcut⟩
        refine ⟨?_, by rw [narrow_den, show (Val.var k).den (ρ.setVal k x) = x from
          Env.setVal_get_self ρ k x]; exact hcut⟩
        have hΓ := CtxS.den_setVal ρ k x Γ hu
        refine ctx_ext (congrArg CtxOf.val hΓ).symm (congrArg CtxOf.flags hΓ).symm
          (congrArg CtxOf.held hΓ).symm ?_ (congrArg CtxOf.rows hΓ).symm
        show readFacts (Sh.den ρ) o n x ++ (Γ.den ρ).known
          = (readFactsS Sh o n (.var k) ++ Γ.known).map _
        have hSh : Sh.den (ρ.setVal k x) = Sh.den ρ := by
          have hu' := hu
          simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu'
          exact TyS.pointee_setVal hk ρ k x (hu'.1.1.2 _ hmem).2 hpt
        rw [List.map_append, readFactsS_den, hSh]
        congr 1
        · show _ = readFacts (Sh.den ρ) o n ((Val.var k).den (ρ.setVal k x))
          rw [show (Val.var k).den (ρ.setVal k x) = x from Env.setVal_get_self ρ k x]
        · exact (congrArg CtxOf.known hΓ).symm
      · split at h
        · next h1 =>
          subst h1
          split at h
          · next q c hstr =>
            cases h
            obtain ⟨hmem, hsame⟩ := findStr_spec Γ.known hstr
            have hf : (q.den ρ, Ty.str (c.den ρ)) ∈ (Γ.den ρ).known :=
              List.mem_map.mpr ⟨(q, .str c), hmem, rfl⟩
            have haddr : eaOf (Γ.den ρ).val next m = q.den ρ := by
              rw [← eaS_den]; exact (Val.same_den ρ hsame).symm
            show Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) 1 _
            rw [haddr]
            refine (Reads.text hf).narrow.mono ?_
            rintro x Γr ⟨rfl, hcut⟩
            have hcell : (narrow 1 (.var k)).den (ρ.setVal k x) = x := by
              rw [narrow_den, show (Val.var k).den (ρ.setVal k x) = x from
                Env.setVal_get_self ρ k x]
              exact hcut
            refine ⟨?_, hcell⟩
            have hΓ := CtxS.den_setVal ρ k x Γ hu
            refine ctx_ext (congrArg CtxOf.val hΓ).symm (congrArg CtxOf.flags hΓ).symm
              (congrArg CtxOf.held hΓ).symm ?_ (congrArg CtxOf.rows hΓ).symm
            have hq : q.under k = true := by
              have hu' := hu
              simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu'
              exact (hu'.1.1.2 _ hmem).1
            show (q.den ρ, Ty.str x) :: (Γ.den ρ).known
              = (q.den (ρ.setVal k x), Ty.str ((narrow 1 (.var k)).den (ρ.setVal k x)))
                :: (Γ.den (ρ.setVal k x)).known
            rw [hcell, Val.den_setVal ρ k x _ hq, hΓ]
          · cases h
        · split at h
          · next h8 =>
            subst h8
            split at h
            · next p c τ st hfa =>
              cases h
              show Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) 8 _
              intro j Ψ' he hwf s hw
              obtain ⟨hmem, i, ha, hi⟩ := findArr_spec (ρ := ρ) (Ψ' := Ψ') (n := j)
                (fun g hg => hw.known (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hg, rfl⟩))
                Γ.known hfa
              have hf : (p.den ρ, Ty.arr (c.den ρ) (τ.den ρ) st) ∈ (Γ.den ρ).known :=
                List.mem_map.mpr ⟨(p, .arr c τ st), hmem, rfl⟩
              have haddr : eaOf (Γ.den ρ).val next m = p.den ρ + BitVec.ofNat 64 (st * i) := by
                rw [← eaS_den]; exact ha
              obtain ⟨hr, Γr, hΓr, hv, hfl, hw'⟩ := Reads.arr hf haddr hi j Ψ' he hwf s hw
              refine ⟨hr, Γr, ⟨?_, Env.setVal_get_self ρ k _⟩, hv, hfl, hw'⟩
              rw [hΓr]
              have hΓ := CtxS.den_setVal ρ k (loadN s 8 (eaOf (Γ.den ρ).val next m)) Γ hu
              refine ctx_ext (congrArg CtxOf.val hΓ).symm (congrArg CtxOf.flags hΓ).symm
                (congrArg CtxOf.held hΓ).symm ?_ (congrArg CtxOf.rows hΓ).symm
              have hτu : τ.under k = true := by
                have hu' := hu
                simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu'
                have := (hu'.1.1.2 _ hmem).2
                simp only [TyS.under, Bool.and_eq_true] at this
                exact this.2
              show (loadN s 8 (eaOf (Γ.den ρ).val next m), τ.den ρ) :: (Γ.den ρ).known
                = ((Val.var k).den (ρ.setVal k (loadN s 8 (eaOf (Γ.den ρ).val next m))),
                    τ.den (ρ.setVal k (loadN s 8 (eaOf (Γ.den ρ).val next m))))
                  :: (Γ.den (ρ.setVal k (loadN s 8 (eaOf (Γ.den ρ).val next m)))).known
              rw [TyS.den_setVal ρ k _ τ hτu, hΓ,
                show (Val.var k).den (ρ.setVal k (loadN s 8 (eaOf (Γ.den ρ).val next m)))
                  = loadN s 8 (eaOf (Γ.den ρ).val next m) from Env.setVal_get_self ρ k _]
            · cases h
          · cases h

/-- Whether each typed value of a block keeps clear of the `n` bytes written
at `o`, or is the eight bytes written, with a value that is of its type:
of itself, or by something known of it. -/
def valsOkS (Γ : CtxS) (v : Val) (o n : Nat) : ValsS → Bool
  | .nil => true
  | .cons q τ rest =>
    (decide (q + 8 ≤ o) || decide (o + n ≤ q) ||
      (n == 8 && q == o && factFrom noEnt Γ.known (v, τ))) &&
    valsOkS Γ v o n rest

theorem valsOkS_sound (ρ : Env) {Γ : CtxS} {v : Val} {o n : Nat} :
    (vs : ValsS) → valsOkS Γ v o n vs = true → ∀ q ∈ vs.den ρ,
    (q.1 + 8 ≤ o ∨ o + n ≤ q.1) ∨
      (n = 8 ∧ q.1 = o ∧ ∀ (Ψ' : MemTy) (k : Nat),
        (∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' k g.2 g.1) →
        HasTy fetch sys Ψ' k q.2 (v.den ρ))
  | .nil, _, q, hq => nomatch hq
  | .cons q₀ τ rest, h, q, hq => by
    simp only [valsOkS, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · have h1 := h.1
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1
      rcases h1 with (h1 | h1) | ⟨⟨h8, hqo⟩, hty⟩
      · exact .inl (.inl h1)
      · exact .inl (.inr h1)
      · exact .inr ⟨h8, hqo, fun Ψ' k hg => factFrom_hasTy noEnt_sound ρ hty Ψ' k hg⟩
    · exact valsOkS_sound ρ rest h.2 q hq

/-- What the context holds once an instruction has written its bytes. In a
region held: the region holds the value written there. In a block a value
is known to point into, through a pointer that may be written through: what
is held is as it was, the block still holding what its shape says. -/
def writeCell (kinds : Nat → Option ShapeS) (Γ : CtxS) (next : BitVec 64) (v : Val) :
    Option (Mem × Nat) → Option (List (Val × HeldS))
  | none => some Γ.held
  | some (m, n) =>
    match writeHeldP true Γ (eaS Γ.regs next m) n v with
    | some r => some r
    | none =>
      match findFact kinds (eaS Γ.regs next m) n Γ.known with
      | some (_, Sh, w, _, o) =>
        if w && decide (n ≤ 8) && valsOkS Γ v o n Sh.vals then some Γ.held else none
      | none => none

theorem writeCell_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {next : BitVec 64} {v : Val} {held' : List (Val × HeldS)} :
    (wr : Option (Mem × Nat)) → (wr.isSome = true → Γ.rows = []) →
    writeCell kinds Γ next v wr = some held' →
    match wr with
    | some (m, n) => Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ)
        (CtxS.den ρ { Γ with held := held' })
    | none => held' = Γ.held
  | none, _, h => by cases h; rfl
  | some (m, n), hrows', h => by
    have hrows : Γ.rows = [] := hrows' rfl
    simp only [writeCell] at h
    split at h
    · next r hr =>
      cases h
      show Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ) _
      rw [← eaS_den]
      exact writeHeldP_sound hr hrows
    · split at h
      · next p Sh w off o hfind =>
        split at h
        · next hc =>
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨hw, hn⟩, hvals⟩ := hc
          subst hw
          obtain ⟨τ, hmem, hpt, hin, ha⟩ := findFact_spec (ρ := ρ) Γ.known hfind
          have hf : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known :=
            List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
          have haddr : eaOf (Γ.den ρ).val next m + BitVec.ofNat 64 off
              = p.den ρ + BitVec.ofNat 64 o := by
            rw [← eaS_den]; exact ha
          show Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ) (Γ.den ρ)
          exact Writes.shared (v.den ρ) hf (TyS.pointee_den hk ρ hpt) haddr (by rw [ShapeS.den_size]; exact hin) hn
            (fun q hq => ((by rw [ShapeS.den_vals] at hq; exact valsOkS_sound ρ Sh.vals hvals q hq :
              (q.1 + 8 ≤ o ∨ o + n ≤ q.1) ∨ _)).elim .inl (fun h => .inr (.inr h))) (by show Γ.rows.map _ = []; rw [hrows]; rfl)
        · cases h
      · cases h

/-- Whether no typed value of a block reaches into the `n` bytes from `o`,
but ones of which nothing is said: those hold whatever is stored. -/
def ValsS.loose (o n : Nat) : ValsS → Bool
  | .nil => true
  | .cons o' τ rest => (o' + 8 ≤ o || o + n ≤ o' || τ == .any) && rest.loose o n

theorem ValsS.loose_den (ρ : Env) (o n : Nat) :
    (vs : ValsS) → vs.loose o n = true →
    ∀ q ∈ vs.den ρ, (q.1 + 8 ≤ o ∨ o + n ≤ q.1) ∨ q.2 = .any
  | .nil, _, _, hq => nomatch hq
  | .cons o' τ rest, h, q, hq => by
    simp only [ValsS.loose, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · rcases h.1 with (h1 | h1) | h1
      · exact .inl (.inl h1)
      · exact .inl (.inr h1)
      · exact .inr (by rw [h1]; rfl)
    · exact ValsS.loose_den ρ o n rest h.2 q hq

/-- Whether no typed value of a block reaches into the `n` bytes from `o`. -/
def ValsS.free (o n : Nat) : ValsS → Bool
  | .nil => true
  | .cons o' _ rest => (o' + 8 ≤ o || o + n ≤ o') && rest.free o n

theorem ValsS.free_den (ρ : Env) (o n : Nat) :
    (vs : ValsS) → (vs.den ρ).all (ShapeOf.clearOf o n) = vs.free o n
  | .nil => rfl
  | .cons o' τ rest => by
    show (ShapeOf.clearOf o n (o', τ.den ρ) && (rest.den ρ).all _) = _
    rw [ValsS.free_den ρ o n rest]
    rfl

/-! ## An address that is not a number into anything -/

/-- The fact a context has that an address lies a stretch into a block
others may point into. -/
def findFactR (kinds : Nat → Option ShapeS) (Γ : CtxS) (a : Val) (n : Nat) :
    List (Val × TyS) → Option (Val × TyS × ShapeS × Bool × Nat × Nat × Nat)
  | [] => none
  | (p, τ) :: rest =>
    match τ.pointee kinds, Γ.spanFrom a p with
    | some (Sh, w, off), some (d, M) =>
      if d + off + M + n ≤ Sh.size then some (p, τ, Sh, w, off, d, M)
      else findFactR kinds Γ a n rest
    | _, _ => findFactR kinds Γ a n rest

theorem findFactR_spec {kinds : Nat → Option ShapeS} {Γ : CtxS} {a : Val} {n : Nat} :
    (l : List (Val × TyS)) → {p : Val} → {τ : TyS} → {Sh : ShapeS} → {w : Bool} →
    {off d M : Nat} → findFactR kinds Γ a n l = some (p, τ, Sh, w, off, d, M) →
    (p, τ) ∈ l ∧ τ.pointee kinds = some (Sh, w, off) ∧ d + off + M + n ≤ Sh.size ∧
      Γ.spanFrom a p = some (d, M)
  | [], _, _, _, _, _, _, _, h => by cases h
  | (q, υ) :: rest, p, τ, Sh, w, off, d, M, h => by
    have tail : findFactR kinds Γ a n rest = some (p, τ, Sh, w, off, d, M) →
        (p, τ) ∈ (q, υ) :: rest ∧ τ.pointee kinds = some (Sh, w, off) ∧
          d + off + M + n ≤ Sh.size ∧ Γ.spanFrom a p = some (d, M) := fun h' => by
      obtain ⟨hm, h1, h2, h3⟩ := findFactR_spec rest h'
      exact ⟨List.mem_cons_of_mem _ hm, h1, h2, h3⟩
    unfold findFactR at h
    split at h
    · next Sh' w' off' d' M' hpt hsp =>
      split at h
      · next hin =>
        cases h
        exact ⟨List.mem_cons_self, hpt, hin, hsp⟩
      · exact tail h
    · exact tail h

/-- The bytes an instruction reads at an address not a number into anything:
in a region the context holds, where what is known of values shows the
address to lie in it, as any bytes of a region; or within a stretch of a
block a value is known to point into, the name `k`, nothing being said of
what is there. -/
def readRanged (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64) :
    Option (Mem × Nat) → Option (Val × List (Val × TyS))
  | none => none
  | some (m, n) =>
    match readHeldP false Γ k (eaS Γ.regs next m) n with
    | some r => some r
    | none =>
      if (findFactR kinds Γ (eaS Γ.regs next m) n Γ.known).isSome then
        some (narrow n (.var k), [])
      else none

theorem readRanged_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {k : Nat} {next : BitVec 64} {cell : Val} {extra : List (Val × TyS)} (hu : Γ.under k = true)
    {m : Mem} {n : Nat} (h : readRanged kinds Γ k next (some (m, n)) = some (cell, extra)) :
    Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
      (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
        cell.den (ρ.setVal k x) = x) := by
  simp only [readRanged] at h
  split at h
  · next r hr =>
    cases h
    rw [← eaS_den]
    exact readHeldP_sound hu hr
  · split at h
    · next hf =>
      cases h
      have core : Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
          (fun _ Γr => Γr = Γ.den ρ) := by
        intro j Ψ' he hwf s hw
        obtain ⟨⟨p, τ, Sh, w, off, d, M⟩, hfind⟩ := Option.isSome_iff_exists.mp hf
        obtain ⟨hmem, hpt, hin, hsp⟩ := findFactR_spec Γ.known hfind
        obtain ⟨o', ha, h1, h2⟩ := CtxS.spanFrom_den hsp hw.known
        have hfm : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known := List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
        refine Reads.sharedAt (fetch := fetch) (sys := sys) (Ψ := Ψ) hfm (TyS.pointee_den hk ρ hpt)
          (o := o' + off) ?_ (by rw [ShapeS.den_size]; omega) j Ψ' he hwf s hw
        rw [← eaS_den, ha, BitVec.ofNat_add, BitVec.add_assoc]
      refine core.narrow.mono ?_
      rintro x Γr ⟨rfl, hcut⟩
      exact ⟨(CtxS.den_setVal ρ k x Γ hu).symm, by
        rw [narrow_den, show (Val.var k).den (ρ.setVal k x) = x from Env.setVal_get_self ρ k x]
        exact hcut⟩
    · cases h

/-- What the context holds once an instruction has written its bytes at an
address not a number into anything: in a region the context holds, where
what is known of values shows the address to lie in it, as any write to a
region; or, within a stretch of a block a value is known to point into, the
stretch holds no typed value and the block is as it was. -/
def writeRanged (kinds : Nat → Option ShapeS) (Γ : CtxS) (next : BitVec 64) (v : Val) :
    Option (Mem × Nat) → Option (List (Val × HeldS))
  | none => none
  | some (m, n) =>
    match writeHeldP false Γ (eaS Γ.regs next m) n v with
    | some r => some r
    | none =>
      if n ≤ 8 then
        match findFactR kinds Γ (eaS Γ.regs next m) n Γ.known with
        | some (_, _, Sh, w, off, d, M) =>
          if w && Sh.vals.loose (d + off) (M + n) then some Γ.held else none
        | none => none
      else none

theorem writeRanged_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {next : BitVec 64} (v : Val) {held' : List (Val × HeldS)} {m : Mem} {n : Nat}
    (h : writeRanged kinds Γ next v (some (m, n)) = some held') (hrows : Γ.rows = []) :
    Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ)
      (CtxS.den ρ { Γ with held := held' }) := by
  simp only [writeRanged] at h
  split at h
  · next r hr =>
    cases h
    rw [← eaS_den]
    exact writeHeldP_sound hr hrows
  · split at h
    · next hn =>
      split at h
      · next p τ Sh w off d M hfind =>
        split at h
        · next hc =>
          cases h
          rw [Bool.and_eq_true] at hc
          obtain ⟨hw', hfree⟩ := hc
          subst hw'
          obtain ⟨hmem, hpt, hin, hsp⟩ := findFactR_spec Γ.known hfind
          have hfm : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known :=
            List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
          refine ⟨rfl, rfl, fun k' Ψ' he hwf s hw => ?_⟩
          obtain ⟨o', ha, h1, h2⟩ := CtxS.spanFrom_den hsp hw.known
          have hall : ∀ q ∈ (Sh.den ρ).vals,
              (q.1 + 8 ≤ d + off ∨ d + off + (M + n) ≤ q.1) ∨ q.2 = .any := by
            rw [ShapeS.den_vals]
            exact ValsS.loose_den ρ _ _ Sh.vals hfree
          have W := Writes.shared (fetch := fetch) (sys := sys) (Ψ := Ψ) (v.den ρ) hfm
            (TyS.pointee_den hk ρ hpt) (a := (eaS Γ.regs next m).den ρ) (o := o' + off) (n := n)
            (by rw [ha, BitVec.ofNat_add, BitVec.add_assoc])
            (by rw [ShapeS.den_size]; omega) hn
            (fun q hq => (hall q hq).elim (fun h => .inl (by omega)) (fun h => .inr (.inl h))) (by show Γ.rows.map _ = []; rw [hrows]; rfl)
          rw [← eaS_den]
          exact W.2.2 k' Ψ' he hwf s hw
        · cases h
      · cases h
    · cases h

/-- The bytes an instruction reads: found exactly, or within a stretch. -/
def readAny (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64)
    (rd : Option (Mem × Nat)) : Option (Val × List (Val × TyS)) :=
  match readCell kinds Γ k next rd with
  | some r => some r
  | none => readRanged kinds Γ k next rd

theorem readAny_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {k : Nat} {next : BitVec 64} {cell : Val}
    {extra : List (Val × TyS)} (hu : Γ.under k = true) :
    (rd : Option (Mem × Nat)) → readAny kinds Γ k next rd = some (cell, extra) →
    match rd with
    | some (m, n) => Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
        (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
          cell.den (ρ.setVal k x) = x)
    | none => extra = [] ∧ cell.den (ρ.setVal k 0) = 0 := by
  intro rd h
  unfold readAny at h
  split at h
  · next r hr => cases h; exact readCell_sound hk hu rd hr
  · cases rd with
    | none => cases h
    | some mn => exact readRanged_sound hk hu h

/-- What is held once an instruction has written: exactly, or within a
stretch. -/
def writeAny (kinds : Nat → Option ShapeS) (Γ : CtxS) (next : BitVec 64) (v : Val)
    (wr : Option (Mem × Nat)) : Option (List (Val × HeldS)) :=
  match writeCell kinds Γ next v wr with
  | some r => some r
  | none => writeRanged kinds Γ next v wr

theorem writeAny_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {next : BitVec 64} {v : Val} {held' : List (Val × HeldS)} :
    (wr : Option (Mem × Nat)) → (wr.isSome = true → Γ.rows = []) →
    writeAny kinds Γ next v wr = some held' →
    match wr with
    | some (m, n) => Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ)
        (CtxS.den ρ { Γ with held := held' })
    | none => held' = Γ.held := by
  intro wr hrows h
  unfold writeAny at h
  split at h
  · next r hr => cases h; exact writeCell_sound hk wr hrows hr
  · cases wr with
    | none => cases h
    | some mn => exact writeRanged_sound hk v h (hrows rfl)

/-- The term for the address an instruction uses as a number. -/
def eaTerm (Γ : CtxS) (next : BitVec 64) : Option Mem → Val
  | some m => eaS Γ.regs next m
  | none => .lit 0

theorem eaTerm_den (ρ : Env) (Γ : CtxS) (next : BitVec 64) (ea : Option Mem) :
    (eaTerm Γ next ea).den ρ = (ea.map (eaOf (Γ.den ρ).val next)).getD 0 := by
  cases ea with
  | none => rfl
  | some m => exact eaS_den ρ Γ next m

/-- The term for the `j`th register an instruction uses stands for that
register's value. -/
theorem argAt_den (ρ : Env) (Γ : CtxS) (srcs : List Reg) (j : Nat) :
    (argAt Γ.regs srcs j).den ρ = (srcs.map (Γ.den ρ).val).getD j 0 := by
  unfold argAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases srcs[j]? <;> rfl

/-- What an instruction computes with, as the context's terms. -/
def fillOf (Γ : CtxS) (srcs : List Reg) (next : BitVec 64) (ea cell : Val) : Filling where
  slot
    | .arg j => argAt Γ.regs srcs j
    | .cell => cell
    | .ea => ea
    | .next => .lit next
  old := Γ.flags

/-- **An instruction's terms, filled in with the context's, stand for what
its description computes from what the context says.** -/
theorem fill_den {ρ ρ' : Env} {Γ : CtxS} (s : Sem) (next : BitVec 64) {cell : Val} {x : BitVec 64}
    (hΓ : Γ.den ρ' = Γ.den ρ) (hx : cell.den ρ' = x) :
    (∀ t : Val, t.slotOnly = true →
      (t.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)).den ρ'
        = t.den (slotEnv (s.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
            ((s.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x)) ∧
    (∀ f : FlagsT, f.slotOnly = true →
      (f.fill (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)).den ρ'
        = f.den (slotEnv (s.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
            ((s.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x)) := by
  have hs : (ρ'.filled (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)).slot
      = (slotEnv (s.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
          ((s.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x).slot := by
    funext sl
    cases sl with
    | arg j =>
      show (argAt Γ.regs s.srcs j).den ρ' = (s.srcs.map (Γ.den ρ).val).getD j 0
      rw [← hΓ]
      exact argAt_den ρ' Γ s.srcs j
    | cell => exact hx
    | ea =>
      show (eaTerm Γ next s.ea).den ρ' = _
      rw [eaTerm_den, hΓ]
      rfl
    | next => rfl
  have ho : (ρ'.filled (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)).old
      = (slotEnv (s.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
          ((s.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x).old :=
    congrArg CtxOf.flags hΓ
  exact ⟨fun t ht => (Val.den_fillN ρ' _ t).trans (Val.den_slots hs ho t ht),
    fun f hf => (FlagsT.den_fill ρ' _ f).trans (FlagsT.den_slots hs ho f hf)⟩

/-- The registers with those an instruction writes given its terms, filled
in; the later winning. -/
def setRegs (σ : Filling) : List (Reg × Val) → Regs Val → Regs Val
  | [], m => m
  | p :: l, m => setRegs σ l (m.set p.1 (p.2.fillN σ))

theorem setRegs_den (ρ : Env) (σ : Filling) :
    (l : List (Reg × Val)) → (m : Regs Val) → (f : Reg → BitVec 64) →
    (∀ r, (m.get r).den ρ = f r) →
    ∀ r, ((setRegs σ l m).get r).den ρ
      = (l.map fun p => (p.1, (p.2.fillN σ).den ρ)).foldl
          (fun f p => fun r => if r = p.1 then p.2 else f r) f r
  | [], _, _, hm, r => hm r
  | p :: l, m, f, hm, r => by
    refine setRegs_den ρ σ l (m.set p.1 (p.2.fillN σ)) _ (fun r' => ?_) r
    show ((m.set p.1 (p.2.fillN σ)).get r').den ρ
      = if r' = p.1 then (p.2.fillN σ).den ρ else f r'
    rw [Regs.get_set]
    split
    · rfl
    · exact hm r'

/-- **What an instruction reads**: as `readAny` has it; but where it is
eight bytes of a region held that the region says nothing of, the region
then says they hold what was read. -/
def readFull (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64)
    (rd : Option (Mem × Nat)) : Option (Val × List (Val × TyS) × List (Val × HeldS)) :=
  match nameRead Γ k next rd with
  | some heldN => some (.var k, [], heldN)
  | none => (readAny kinds Γ k next rd).map fun r => (r.1, r.2, Γ.held)

theorem readFull_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {k : Nat} {next : BitVec 64} {cell : Val} {extra : List (Val × TyS)}
    {heldR : List (Val × HeldS)} (hu : Γ.under k = true) :
    (rd : Option (Mem × Nat)) → readFull kinds Γ k next rd = some (cell, extra, heldR) →
    match rd with
    | some (m, n) => Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
        (fun x Γr => Γr = CtxS.den (ρ.setVal k x)
            { Γ with known := extra ++ Γ.known, held := heldR } ∧
          cell.den (ρ.setVal k x) = x)
    | none => extra = [] ∧ heldR = Γ.held ∧ cell.den (ρ.setVal k 0) = 0 := by
  intro rd h
  unfold readFull at h
  split at h
  · next heldN hn =>
    cases h
    cases rd with
    | none => cases hn
    | some mn =>
      obtain ⟨m, n⟩ := mn
      exact nameRead_sound hu hn
  · obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c, e⟩ := r
    cases he
    have hR := readAny_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ) hk hu rd hr
    cases rd with
    | none => exact ⟨hR.1, rfl, hR.2⟩
    | some mn => exact hR

/-! ## What is so of rows once bytes are stored -/

/-- What a value of a row is, of a value stored: the value, or its low
byte. -/
def cellVal (byte : Bool) (v : Val) : Val := if byte then mkUn .low8 v else v

theorem cellVal_den (ρ : Env) (byte : Bool) (v : Val) :
    (cellVal byte v).den ρ
      = if byte then ((v.den ρ).setWidth 8).setWidth 64 else v.den ρ := by
  cases byte
  · rfl
  · exact mkUn_den ρ .low8 v

theorem sumNat_replicate (ρ : Env) (c : Val) : (n : Nat) →
    sumNat ρ (List.replicate n c) = n * c.nat ρ
  | 0 => by simp [sumNat]
  | n + 1 => by
    show c.nat ρ + sumNat ρ (List.replicate n c) = _
    rw [sumNat_replicate ρ c n, Nat.succ_mul]
    omega

/-- Where an address lies in a region held, so many bytes and more: found
with what it is from the region's address written out, or not. -/
def findHeld2 (G : List (Val × TyS)) (a : Val) (ls : List Val) (n : Nat)
    (held : List (Val × HeldS)) : Option (Nat × Val × HeldS × Val) :=
  match findHeldP true G a ls n held 0 with
  | some r => some r
  | none => findHeldP false G a ls n held 0

theorem findHeld2_spec {ρ : Env} {Ψ' : MemTy} {m : Nat} {G : List (Val × TyS)}
    {a : Val} {ls : List Val} {n : Nat} (l : List (Val × HeldS)) {k : Nat} {b : Val} {S : HeldS}
    {o : Val} (h : findHeld2 G a ls n l = some (k, b, S, o))
    (hg : ∀ g ∈ G, HasTy fetch sys Ψ' m (g.2.den ρ) (g.1.den ρ)) :
    l[k]? = some (b, S) ∧ o.nat ρ + (sumNat ρ ls + n) ≤ S.size.nat ρ ∧
      a.den ρ = b.den ρ + BitVec.ofNat 64 (o.nat ρ) := by
  unfold findHeld2 at h
  split at h
  · next r hr =>
    cases h
    obtain ⟨j, hj, hl, hin, ha⟩ := findHeldP_spec (ρ := ρ) l 0 hr hg
    rw [Nat.zero_add] at hj
    subst hj
    exact ⟨hl, hin, ha⟩
  · obtain ⟨j, hj, hl, hin, ha⟩ := findHeldP_spec (ρ := ρ) l 0 h hg
    rw [Nat.zero_add] at hj
    subst hj
    exact ⟨hl, hin, ha⟩

/-- How many bytes a value of a row is. -/
def RowS.width (r : RowS) : Nat := if r.byte then 1 else 8

/-- **What a row is once bytes are stored in the region `j`, so far in**:
as it was, where the store keeps clear of it; with a value more at its end
or at its start, where the store puts one of its type there; and nothing,
where it is not seen to be so. -/
def rowAfter (ent : TyS → TyS → Bool) (Γ : CtxS) (j : Nat) (ow : Val) (n : Nat) (v wa : Val)
    (r : RowS) : Option RowS :=
  if decide (r.width ≤ r.stride) then
    match findHeld2 Γ.known r.addr (List.replicate r.stride r.count) 0 Γ.held with
    | some (j', _, _, orr) =>
      if j' = j then
        if sumLe Γ.known (orr :: List.replicate r.stride r.count) 0 [ow] 0 then
          if decide (n = r.width) &&
              sumLe Γ.known [ow] 0 (orr :: List.replicate r.stride r.count) 0 &&
              factFrom ent Γ.known (cellVal r.byte v, r.ty) then
            some { r with count := .add r.count (.lit 1) }
          else some r
        else if sumLe Γ.known [ow] n [orr] 0 then
          if decide (n = r.width) && sumLe Γ.known [ow] r.stride [orr] 0 &&
              sumLe Γ.known [orr] 0 [ow] r.stride &&
              factFrom ent Γ.known (cellVal r.byte v, r.ty) then
            some { r with addr := wa, count := .add r.count (.lit 1) }
          else some r
        else none
      else none
    | none => none
  else none

theorem rowAfter_sound {ρ : Env} {ent : TyS → TyS → Bool} (he : EntSound fetch sys ent)
    {Γ : CtxS} {j : Nat} {ow v wa : Val} {n : Nat} {r r' : RowS}
    (h : rowAfter ent Γ j ow n v wa r = some r') (hr : r ∈ Γ.rows) {base : Val} {S : HeldS}
    (hj : Γ.held[j]? = some (base, S))
    (hwa : wa.den ρ = base.den ρ + BitVec.ofNat 64 (ow.nat ρ)) (hn : n ≤ 8)
    {k : Nat} {Ψ' : MemTy} {s : State} (hw : WellTyped fetch sys Ψ' k (Γ.den ρ) s)
    (hfit : ow.nat ρ + n ≤ S.size.nat ρ) :
    ∀ i, i < (r'.den ρ).count.toNat → HasTy fetch sys Ψ' k (r'.den ρ).ty
      (cellAt (storeN s n (wa.den ρ) (v.den ρ)) (r'.den ρ).byte
        ((r'.den ρ).addr + BitVec.ofNat 64 ((r'.den ρ).stride * i))) := by
  have hg := knownS hw.known
  have hrd : r.den ρ ∈ (Γ.den ρ).rows := List.mem_map.mpr ⟨r, hr, rfl⟩
  have hjd := CtxS.held_den ρ Γ hj
  unfold rowAfter at h
  split at h
  · next hwid =>
    have hwid' : (if (r.den ρ).byte then 1 else 8) ≤ (r.den ρ).stride := of_decide_eq_true hwid
    split at h
    · next j' b' S' orr hfind =>
      obtain ⟨hl, hin, hra⟩ := findHeld2_spec (ρ := ρ) Γ.held hfind hg
      split at h
      · next hjj =>
        subst hjj
        have hbs : (b', S') = (base, S) := Option.some.inj (hl.symm.trans hj)
        cases hbs
        rw [sumNat_replicate, Nat.add_zero] at hin
        have hra' : (r.den ρ).addr = base.den ρ + BitVec.ofNat 64 (orr.nat ρ) := hra
        have hrow : orr.nat ρ + (r.den ρ).stride * (r.den ρ).count.toNat ≤ (S.den ρ).size := hin
        rw [hwa]
        split at h
        · next hpast =>
          have hp := sumLe_den hpast hg
          simp only [sumNat, sumNat_replicate, Nat.add_zero] at hp
          split at h
          · next hc =>
            cases h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            obtain ⟨⟨hnw, hback⟩, hf⟩ := hc
            have hb := sumLe_den hback hg
            simp only [sumNat, sumNat_replicate, Nat.add_zero] at hb
            have hv := factFrom_hasTy he ρ hf Ψ' k hw.known
            rw [cellVal_den] at hv
            exact rowAppended hw hjd hrd hfit hra' hwid'
              (show ow.nat ρ = orr.nat ρ + r.stride * r.count.nat ρ by omega) hnw hv
          · cases h
            exact rowKept hw hjd hrd hn hfit hrow hra' hwid'
              (.inl (show orr.nat ρ + r.stride * r.count.nat ρ ≤ ow.nat ρ by omega)) _
        · split at h
          · next hbelow =>
            have hp := sumLe_den hbelow hg
            simp only [sumNat, Nat.add_zero] at hp
            split at h
            · next hc =>
              cases h
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
              obtain ⟨⟨⟨hnw, h1⟩, h2⟩, hf⟩ := hc
              have h1' := sumLe_den h1 hg
              have h2' := sumLe_den h2 hg
              simp only [sumNat, Nat.add_zero] at h1' h2'
              have hv := factFrom_hasTy he ρ hf Ψ' k hw.known
              rw [cellVal_den] at hv
              show ∀ i, i < (r.count.den ρ + 1).toNat → HasTy fetch sys Ψ' k (r.ty.den ρ)
                (cellAt (storeN s n (base.den ρ + BitVec.ofNat 64 (ow.nat ρ)) (v.den ρ)) r.byte
                  (wa.den ρ + BitVec.ofNat 64 (r.stride * i)))
              rw [hwa]
              exact rowPrepended hw hjd hrd hfit hrow hra' hwid'
                (show ow.nat ρ + r.stride = orr.nat ρ by omega) hnw hv
            · cases h
              exact rowKept hw hjd hrd hn hfit hrow hra' hwid' (.inr hp) _
          · cases h
      · cases h
    · cases h
  · cases h

/-- **The row a store makes**: of one value, the one stored, of the least
and the most the context shows it to be; where it shows anything. So the
bytes a program stores one by one are each known as they are stored, and
a label may say so of them. -/
def newRow (Γ : CtxS) (wa : Val) (n : Nat) (v : Val) : List RowS :=
  if n = 1 ∨ n = 8 then
    match Γ.within (cellVal (decide (n = 1)) v) with
    | some (lo, hi) =>
      if hi < 18446744073709551616 ∧ (0 < lo ∨ hi < 18446744073709551615) then
        [⟨wa, .lit 1, n, decide (n = 1), .range (BitVec.ofNat 64 lo) (BitVec.ofNat 64 hi)⟩]
      else []
    | none => []
  else []

theorem newRow_sound {ρ : Env} {Γ : CtxS} {wa v : Val} {n : Nat} {k : Nat} {Ψ' : MemTy}
    {s : State} (hw : WellTyped fetch sys Ψ' k (Γ.den ρ) s) :
    ∀ r ∈ (newRow Γ wa n v).map (RowS.den ρ), ∀ i, i < r.count.toNat →
      HasTy fetch sys Ψ' k r.ty
        (cellAt (storeN s n (wa.den ρ) (v.den ρ)) r.byte (r.addr + BitVec.ofNat 64 (r.stride * i))) := by
  intro r hr i hi
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  unfold newRow at hr'
  split at hr'
  · next hn =>
    split at hr'
    · next lo hi' hwin =>
      split at hr'
      · next hcond =>
        rw [List.mem_singleton] at hr'
        subst hr'
        have hi0 : i = 0 := by
          have h1 : (BitVec.ofNat 64 1 : BitVec 64).toNat = 1 := rfl
          have : i < (BitVec.ofNat 64 1 : BitVec 64).toNat := hi
          omega
        subst hi0
        have hb := CtxS.within_den hwin hw.known
        have hrange : ∀ x : BitVec 64, lo ≤ x.toNat → x.toNat ≤ hi' →
            HasTy fetch sys Ψ' k (.range (BitVec.ofNat 64 lo) (BitVec.ofNat 64 hi')) x := by
          intro x h1 h2
          refine hasTy_range.mpr ?_
          have hx := x.isLt
          have hhi : hi' < 2 ^ 64 := hcond.1
          have hlo : lo < 2 ^ 64 := by omega
          rw [BitVec.le_def, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi]
          omega
        have ea : wa.den ρ + BitVec.ofNat 64 (n * 0) = wa.den ρ := by simp
        show HasTy fetch sys Ψ' k (.range (BitVec.ofNat 64 lo) (BitVec.ofNat 64 hi'))
          (cellAt (storeN s n (wa.den ρ) (v.den ρ)) (decide (n = 1))
            (wa.den ρ + BitVec.ofNat 64 (n * 0)))
        rw [ea]
        rcases hn with rfl | rfl
        · have hc := cellAt_storeN_same s (wa.den ρ) (v.den ρ) true
          have hv := cellVal_den ρ true v
          simp only [↓reduceIte] at hc hv
          show HasTy fetch sys Ψ' k _ (cellAt (storeN s 1 (wa.den ρ) (v.den ρ)) true (wa.den ρ))
          rw [hc, ← hv]
          exact hrange _ hb.1 hb.2
        · have hc := cellAt_storeN_same s (wa.den ρ) (v.den ρ) false
          have hv := cellVal_den ρ false v
          simp only [Bool.false_eq_true, ↓reduceIte] at hc hv
          show HasTy fetch sys Ψ' k _ (cellAt (storeN s 8 (wa.den ρ) (v.den ρ)) false (wa.den ρ))
          rw [hc, ← hv]
          exact hrange _ hb.1 hb.2
      · cases hr'
    · cases hr'
  · cases hr'

/-- **What is so of rows once `n` bytes at an address are stored**: of each
row the context has, what `rowAfter` leaves; nothing where the bytes are
not found in a region held. -/
def rowsAfter (ent : TyS → TyS → Bool) (Γ : CtxS) (wa : Val) (n : Nat) (v : Val) : List RowS :=
  if n ≤ 8 then
    match findHeld2 Γ.known wa [] n Γ.held with
    | some (j, _, _, ow) => Γ.rows.filterMap (rowAfter ent Γ j ow n v wa) ++ newRow Γ wa n v
    | none => []
  else []

theorem rowsAfter_sound {ρ : Env} {ent : TyS → TyS → Bool} (he : EntSound fetch sys ent)
    {Γ : CtxS} {wa v : Val} {n : Nat} {k : Nat} {Ψ' : MemTy} {s : State}
    (hw : WellTyped fetch sys Ψ' k (Γ.den ρ) s) :
    ∀ r ∈ (rowsAfter ent Γ wa n v).map (RowS.den ρ), ∀ i, i < r.count.toNat →
      HasTy fetch sys Ψ' k r.ty
        (cellAt (storeN s n (wa.den ρ) (v.den ρ)) r.byte (r.addr + BitVec.ofNat 64 (r.stride * i))) := by
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  unfold rowsAfter at hr'
  split at hr'
  · next hn =>
    split at hr'
    · next j b S ow hfind =>
      obtain ⟨hl, hin, ha⟩ := findHeld2_spec (ρ := ρ) Γ.held hfind (knownS hw.known)
      rcases List.mem_append.mp hr' with hr' | hr'
      · obtain ⟨r0, hr0, hra⟩ := List.mem_filterMap.mp hr'
        simp only [sumNat, Nat.zero_add] at hin
        exact rowAfter_sound he hra hr0 hl ha hn hw hin
      · exact newRow_sound hw _ (List.mem_map.mpr ⟨_, hr', rfl⟩)
    · cases hr'
  · cases hr'

/-- The row a context has that the `n` bytes at an address are a value of:
so many along, and fewer than there are. -/
def rowAt (Γ : CtxS) (next : BitVec 64) (m : Mem) (n : Nat) : Option RowS :=
  Γ.rows.find? fun r =>
    decide (n = if r.byte then 1 else 8) &&
      (match idxOf r.stride (Lin.addMul (-1) r.addr.lin (eaS Γ.regs next m).lin) with
       | some P => inCount Γ.known P r.count
       | none => false)

/-- What a row says of the value an instruction reads: that it is of the
row's type. -/
def rowFact (Γ : CtxS) (next : BitVec 64) (cell : Val) : Option (Mem × Nat) → List (Val × TyS)
  | none => []
  | some (m, n) =>
    match rowAt Γ next m n with
    | some r => [(cell, r.ty)]
    | none => []

/-- **What an instruction reads**, with what a row says of it. -/
def readRows (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64)
    (rd : Option (Mem × Nat)) : Option (Val × List (Val × TyS) × List (Val × HeldS)) :=
  match readFull kinds Γ k next rd with
  | some (c, e, h) => some (c, rowFact Γ next c rd ++ e, h)
  | none => none

theorem readRows_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {k : Nat} {next : BitVec 64} {cell : Val} {extra : List (Val × TyS)}
    {heldR : List (Val × HeldS)} (hu : Γ.under k = true) :
    (rd : Option (Mem × Nat)) → readRows kinds Γ k next rd = some (cell, extra, heldR) →
    match rd with
    | some (m, n) => Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
        (fun x Γr => Γr = CtxS.den (ρ.setVal k x)
            { Γ with known := extra ++ Γ.known, held := heldR } ∧
          cell.den (ρ.setVal k x) = x)
    | none => extra = [] ∧ heldR = Γ.held ∧ cell.den (ρ.setVal k 0) = 0 := by
  intro rd h
  unfold readRows at h
  split at h
  · next c e hh hrf =>
    cases h
    have R := readFull_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ) hk hu rd hrf
    cases rd with
    | none => exact R
    | some mn =>
      obtain ⟨m, n⟩ := mn
      have R' : Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
          (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := e ++ Γ.known, held := heldR } ∧
            cell.den (ρ.setVal k x) = x) := R
      show Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n _
      cases hfind : rowAt Γ next m n with
      | none =>
        simp only [rowFact, hfind, List.nil_append]
        exact R'
      | some r =>
        simp only [rowFact, hfind]
        unfold rowAt at hfind
        have hmem := List.mem_of_find?_eq_some hfind
        have hp := List.find?_some hfind
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        obtain ⟨hn, hidx⟩ := hp
        split at hidx
        · next P hP =>
          have hτu : r.ty.under k = true := by
            have hu' := hu
            simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu'
            exact (hu'.2 r hmem).2
          refine Reads.withKnown fun k' Ψ' hg0 => ?_
          have hg := knownS hg0
          obtain ⟨i, hi, hd⟩ := idxOf_den ρ hP
          have hlt := inCount_lt (ρ := ρ) hidx hg
          have e := Lin.addMul_den (Val.den ρ) (-1) r.addr.lin (eaS Γ.regs next m).lin
          rw [Val.lin_den, Val.lin_den, hd] at e
          have ha : eaOf (Γ.den ρ).val next m
              = (r.den ρ).addr + BitVec.ofNat 64 ((r.den ρ).stride * i) := by
            rw [← eaS_den]
            show (eaS Γ.regs next m).den ρ = r.addr.den ρ + BitVec.ofNat 64 (r.stride * i)
            rw [e]
            grind
          have hi' : i < (r.den ρ).count.toNat := by
            show i < (r.count.den ρ).toNat
            rw [hi] at hlt
            simp only [natOf] at hlt
            omega
          refine (Reads.row R' (r := r.den ρ) (List.mem_map.mpr ⟨r, hmem, rfl⟩) hi' ha hn).mono ?_
          rintro x Γr ⟨Γ0, ⟨rfl, hx⟩, rfl⟩
          refine ⟨?_, hx⟩
          refine ctx_ext rfl rfl rfl ?_
          show ((x, r.ty.den ρ) :: _ : List Fact)
            = (cell.den (ρ.setVal k x), r.ty.den (ρ.setVal k x)) :: _
          rw [hx, TyS.den_setVal ρ k x r.ty hτu]
          rfl
        · cases hidx
  · cases h

/-- **The checker's step.** The context after an instruction, and the term
for where control goes. `k` is a name no term yet mentions, for what is
read where the context does not say. -/
def stepHeld (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64) (i : Instr) :
    Option (CtxS × Val) :=
  match i.sem with
  | some s =>
    match readRows kinds Γ k next s.rd with
    | some (cell, extra, heldR) =>
      let Γ₁ : CtxS := { Γ with known := extra ++ Γ.known, held := heldR }
      let σ := fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell
      if !s.guard.okS Γ₁ Γ.flags (s.ga.fillN σ) (s.gb.fillN σ) (s.gc.fillN σ) then none else
      match writeAny kinds { Γ₁ with rows := [] } next (s.store.fillN σ) s.wr with
      | some held' =>
        some ({ Γ₁ with
                regs := setRegs σ s.outs Γ.regs
                flags := s.flags.fill σ
                held := held'
                rows := match s.wr with
                  | some (m, n) =>
                    rowsAfter noEnt Γ₁ (eaS Γ.regs next m) n (s.store.fillN σ)
                  | none => Γ.rows },
          match s.goes with
          | some t => t.fillN σ
          | none => .lit next)
      | none => none
    | none => none
  | none => none

theorem stepHeld_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds)
    {Γ Γ' : CtxS} {k : Nat} {next : BitVec 64} {i : Instr} {t : Val}
    (h : stepHeld kinds Γ k next i = some (Γ', t)) (hu : Γ.under k = true) :
    Steps fetch sys Ψ i next (Γ.den ρ) fun t' Δ =>
      ∃ x, t' = t.den (ρ.setVal k x) ∧ Δ = Γ'.den (ρ.setVal k x) := by
  unfold stepHeld at h
  cases hsem : i.sem with
  | none => rw [hsem] at h; cases h
  | some s =>
    rw [hsem] at h
    simp only at h
    have hd : i.desc = some s.toDesc := by rw [← sem_desc, hsem]; rfl
    have hso := sem_slotOnly hsem
    simp only [Sem.slotOnly, Bool.and_eq_true] at hso
    obtain ⟨⟨⟨⟨⟨⟨hga, hgb⟩, hgc⟩, houts⟩, hflags⟩, hstore⟩, hgoes⟩ := hso
    split at h
    · next cell extra heldR hrc =>
      have hgd : s.guard.okS { Γ with known := extra ++ Γ.known, held := heldR } Γ.flags
          (s.ga.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
          (s.gb.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
          (s.gc.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)) = true := by
        cases hq : s.guard.okS { Γ with known := extra ++ Γ.known, held := heldR } Γ.flags
          (s.ga.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
          (s.gb.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
          (s.gc.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)) with
        | true => rfl
        | false =>
          simp only [hq, Bool.not_false, ↓reduceIte] at h
          cases h
      simp only [hgd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · next held' hwc =>
        cases h
        have hR := readRows_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ) hk hu s.rd hrc
        refine Steps.mono (Steps.desc
          (R := fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known, held := heldR } ∧
            cell.den (ρ.setVal k x) = x)
          (W := fun x _ Γw => Γw = CtxS.den (ρ.setVal k x)
            { Γ with known := extra ++ Γ.known, held := held',
                     rows := match s.wr with
                       | some (m, n) =>
                         rowsAfter noEnt { Γ with known := extra ++ Γ.known, held := heldR }
                           (eaS Γ.regs next m) n
                           (s.store.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
                       | none => Γ.rows }) hd ?_ ?_ ?_) ?_
        · show match s.rd with
            | some (m, n) => _
            | none => _
          cases hrd : s.rd with
          | none =>
            rw [hrd] at hR
            obtain ⟨he, hh, hc⟩ := hR
            subst he
            subst hh
            exact ⟨(CtxS.den_setVal ρ k 0 Γ hu).symm, hc⟩
          | some mn => rw [hrd] at hR; exact hR
        · rintro x Γr ⟨rfl, hx⟩
          refine ⟨_, rfl, ?_⟩
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          have hval : (CtxS.den (ρ.setVal k x)
                { Γ with known := extra ++ Γ.known, held := heldR, rows := [] }).val
              = (Γ.den ρ).val := (congrArg CtxOf.val hΓ : (Γ.den (ρ.setVal k x)).val = _)
          have hW := writeAny_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ.setVal k x) hk
            (Γ := { Γ with known := extra ++ Γ.known, held := heldR, rows := [] }) s.wr
            (fun _ => rfl) hwc
          have hRows := fun (m : Mem) (n : Nat) (k' : Nat) (Ψ' : MemTy) (st : State)
              (hw : WellTyped fetch sys Ψ' k'
                (CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known, held := heldR }) st) =>
            rowsAfter_sound (fetch := fetch) (sys := sys) (ρ := ρ.setVal k x) noEnt_sound
              (wa := eaS Γ.regs next m) (n := n)
              (v := s.store.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)) hw
          show match s.wr with
            | some (m, n) => _
            | none => _
          cases hwr : s.wr with
          | none =>
            rw [hwr] at hW
            show CtxS.den (ρ.setVal k x)
              { Γ with known := extra ++ Γ.known, held := held', rows := Γ.rows } = _
            rw [hW]
          | some mn =>
            obtain ⟨m, n⟩ := mn
            rw [hwr] at hW
            have hRm := hRows m n
            rw [(fill_den s next hΓ hx).1 _ hstore, hval] at hW
            rw [(fill_den s next hΓ hx).1 _ hstore,
              show (eaS Γ.regs next m).den (ρ.setVal k x) = eaOf (Γ.den ρ).val next m from by
                rw [← hval]; exact eaS_den (ρ.setVal k x) _ next m] at hRm
            exact Writes.rows _ hW fun k' Ψ' _ _ st hw => hRm k' Ψ' st hw
        · rintro x Γr ⟨rfl, hx⟩ Ψ' n hk
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          have hfill := fill_den s next hΓ hx
          have hok := GuardE.okS_den (ρ := ρ.setVal k x) hgd hk
          rw [hfill.1 _ hga, hfill.1 _ hgb, hfill.1 _ hgc] at hok
          have hfl : Γ.flags.den (ρ.setVal k x) = (Γ.den ρ).flags := congrArg CtxOf.flags hΓ
          rw [hfl] at hok
          exact hok
        · rintro t' Δ ⟨x, Γr, Γw, ⟨rfl, hx⟩, rfl, rfl, rfl⟩
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          have hfill := fill_den s next hΓ hx
          refine ⟨x, ?_, ?_⟩
          · show (Option.map _ s.goes).getD next = _
            cases hgo : s.goes with
            | none => rfl
            | some tg =>
              rw [hgo] at hgoes
              exact (hfill.1 tg hgoes).symm
          · refine ctx_ext ?_ ?_ rfl rfl
            · funext r
              show List.foldl _ (Γ.den (ρ.setVal k x)).val (s.outs.map _) r
                = ((setRegs _ s.outs Γ.regs).get r).den (ρ.setVal k x)
              rw [setRegs_den (ρ.setVal k x) _ s.outs Γ.regs (Γ.den (ρ.setVal k x)).val
                (fun _ => rfl) r]
              refine congrFun (congrArg _ (List.map_congr_left fun p hp => ?_)) r
              rw [hfill.1 p.2 (List.all_eq_true.mp houts p hp)]
              rfl
            · exact (hfill.2 s.flags hflags).symm
      · cases h
    · cases h

end TypedAsm.U
