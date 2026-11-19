import TypedAsm.U.Split

/-!
# What it comes to for one context to be regarded as another

A context says five kinds of thing of a state: what each register holds;
what the flags are; what is known of values; which regions are held, alone;
and what values lie in them. One context may be regarded as another when
every state that matches the first matches the second: the same state,
under the same memory typing, described another way. Taking the five in
turn, that comes to this:

* the registers hold the same values, and the flags are the same: both
  contexts say all of them, so nothing less will do;
* each thing the second knows is so whenever everything the first knows is:
  which covers a fact that follows from another, facts dropped, and facts
  that are so of any value. To know is something one may do less of and
  still be right;
* to hold is not. A context says all that is held, so the second holds
  every byte the first does: each region it holds, written out, is a
  **part** of one the first holds, lying within it and saying of values
  only what the first says is there; the parts of each region do not
  overlap, and between them take in the whole of it; and what else the
  first holds, the second holds as it was. Which covers the same regions,
  in any order, saying less of what they hold, and one taken as several.

That is one statement, `Regards.parts`, and everything of the kind is a case
of it. Two things are not, and are stated beside it. A context may come to
name the value in bytes it holds and said nothing of: the value is whatever
the memory holds, which no context before it says, so this is a choice made
of the state (`Ok.nameSlot`). And regions end to end may be taken as one
(`Regards.join`): the one is then part of several, not of one.

Coming to hold memory and ceasing to are no part of this: memory mapped,
unmapped, or made a block others may point into is a thing that happens,
with a statement of its own.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-! ## Parts of ranges that are apart -/

/-- Parts of one range, one ending before the other begins, are apart. -/
theorem disjoint_same {b : BitVec 64} {o₁ n₁ o₂ n₂ N : Nat} (hN : N < 2 ^ 64)
    (h₁ : o₁ + n₁ ≤ N) (h₂ : o₂ + n₂ ≤ N) (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) :
    Disjoint (b + BitVec.ofNat 64 o₁) n₁ (b + BitVec.ofNat 64 o₂) n₂ := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega

/-! ## Parts of regions -/

/-- A part of a held region: which region, by its place among those held;
how far into it the part starts; and the part's size and the values it says
are in it. -/
abbrev Part := Nat × Nat × Held

/-- The region a part is. -/
def partRegion (E : List Region) (x : Part) : Region :=
  (((E[x.1]?).map (·.1)).getD 0 + BitVec.ofNat 64 x.2.1, x.2.2)

/-- A part lies within its region, and says of values only what the region
says, at that place. -/
def PartOk (E : List Region) (x : Part) : Prop :=
  ∃ b, E[x.1]? = some b ∧ x.2.1 + x.2.2.size ≤ b.2.size ∧
    ∀ p ∈ x.2.2.vals, p.1 + 8 ≤ x.2.2.size ∧ (x.2.1 + p.1, p.2) ∈ b.2.vals

/-- Two parts do not overlap: they are of different regions, or one ends
before the other begins. -/
def PartsApart (x y : Part) : Prop :=
  x.1 ≠ y.1 ∨ x.2.1 + x.2.2.size ≤ y.2.1 ∨ y.2.1 + y.2.2.size ≤ x.2.1

theorem partRegion_eq {E : List Region} {x : Part} {b : Region} (h : E[x.1]? = some b) :
    partRegion E x = (b.1 + BitVec.ofNat 64 x.2.1, x.2.2) := by
  unfold partRegion
  rw [h]
  rfl

/-- **One context may be regarded as another** that says the same of the
registers and the flags, knows only what follows from what the first knows,
and holds what the first holds as parts: apart from one another, and
between them the whole of each region; with what else the first holds,
`F`, held as it was. -/
theorem Regards.parts {Γ Δ : Ctx} {E F : List Region} {L : List Part}
    (hval : Δ.val = Γ.val) (hflags : Δ.flags = Γ.flags)
    (hknown : ∀ f ∈ Δ.known, ∀ (Ψ' : MemTy) (n : Nat),
      (∀ g ∈ Γ.known, HasTy fetch sys Ψ' n g.2 g.1) → HasTy fetch sys Ψ' n f.2 f.1)
    (hΓ : Γ.held = E ++ F) (hΔ : Δ.held = L.map (partRegion E) ++ F)
    (hok : ∀ x ∈ L, PartOk E x) (hap : L.Pairwise PartsApart)
    (hcov : ∀ i b, E[i]? = some b → ∀ o, o < b.2.size →
      ∃ x ∈ L, x.1 = i ∧ x.2.1 ≤ o ∧ o < x.2.1 + x.2.2.size)
    (hrows : ∀ (k : Nat) (Ψ' : MemTy) (s : State), WellTyped fetch sys Ψ' k Γ s →
      ∀ r ∈ Δ.rows, ∀ i, i < r.count.toNat →
        HasTy fetch sys Ψ' k r.ty (cellAt s r.byte (r.addr + BitVec.ofNat 64 (r.stride * i)))
      := by exact fun _ _ _ hw r h => hw.rows r h) :
    Regards fetch sys Ψ Γ Δ := by
  intro k Ψ' he hwf s hw
  have hE : ∀ b ∈ E, b ∈ Γ.held := fun b hb => by rw [hΓ]; exact List.mem_append_left _ hb
  have hF : ∀ b ∈ F, b ∈ Γ.held := fun b hb => by rw [hΓ]; exact List.mem_append_right _ hb
  have hap0 : (E ++ F).Pairwise fun b c => Disjoint b.1 b.2.size c.1 c.2.size := by
    rw [← hΓ]; exact hw.held.apart
  obtain ⟨hapE, hapF, hapEF⟩ := List.pairwise_append.mp hap0
  have hlt : ∀ b ∈ Γ.held, b.2.size < 2 ^ 64 := hw.held.size_lt
  -- each region of the second context is a part of one of the first
  have key : ∀ c ∈ Δ.held, ∃ b ∈ Γ.held, ∃ o, c.1 = b.1 + BitVec.ofNat 64 o ∧
      o + c.2.size ≤ b.2.size ∧ ∀ p ∈ c.2.vals, p.1 + 8 ≤ c.2.size ∧ (o + p.1, p.2) ∈ b.2.vals := by
    intro c hc
    rw [hΔ] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      obtain ⟨b, hb, hle, hv⟩ := hok x hx
      refine ⟨b, hE b (List.mem_of_getElem? hb), x.2.1, ?_, ?_, ?_⟩
      · rw [partRegion_eq hb]
      · rw [partRegion_eq hb]; exact hle
      · rw [partRegion_eq hb]; exact hv
    · refine ⟨c, hF c hc, 0, by simp, by omega, fun p hp => ⟨hw.held.fits c (hF c hc) p hp, ?_⟩⟩
      rw [Nat.zero_add]; exact hp
  exact
    { val := fun r => by rw [hval]; exact hw.val r
      known := fun f hf => hknown f hf Ψ' k hw.known
      flags := by rw [hflags]; exact hw.flags
      heapPerm := hw.heapPerm
      heap := hw.heap
      text := hw.text
      said := hw.said
      rows := hrows k Ψ' s hw
      complete := fun a ha => by
        rcases hw.complete a ha with ⟨b, hb, hin⟩ | hr
        · rw [hΓ] at hb
          rcases List.mem_append.mp hb with hb | hb
          · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
            have hEi : E[i]? = some E[i] := List.getElem?_eq_getElem hi
            obtain ⟨x, hx, hxi, hlo, hhi⟩ := hcov i _ hEi _ hin
            refine .inl ⟨partRegion E x, by
              rw [hΔ]; exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩), ?_⟩
            rw [partRegion_eq (b := E[i]) (by rw [hxi]; exact hEi)]
            show (a - (E[i].1 + BitVec.ofNat 64 x.2.1)).toNat < x.2.2.size
            have hsz := hlt E[i] (hE _ (List.getElem_mem hi))
            bv_omega
          · exact .inl ⟨b, by rw [hΔ]; exact List.mem_append_right _ hb, hin⟩
        · exact .inr hr
      held :=
        { perm := fun c hc => by
            obtain ⟨b, hb, o, hc1, hle, _⟩ := key c hc
            rw [hc1]; exact State.canWrite_sub (hw.held.perm b hb) hle
          size_lt := fun c hc => by
            obtain ⟨b, hb, o, _, hle, _⟩ := key c hc
            have := hlt b hb
            omega
          fits := fun c hc p hp => by
            obtain ⟨b, hb, o, _, _, hv⟩ := key c hc
            exact (hv p hp).1
          vals := fun c hc p hp => by
            obtain ⟨b, hb, o, hc1, _, hv⟩ := key c hc
            have := hw.held.vals b hb _ (hv p hp).2
            rw [hc1, BitVec.add_assoc, ← BitVec.ofNat_add]
            exact this
          heap := fun c hc a l hl => by
            obtain ⟨b, hb, o, hc1, hle, _⟩ := key c hc
            rw [hc1]
            exact (hw.held.heap b hb a l hl).part_left hle (hlt b hb) (hwf.size_lt a l hl)
          apart := by
            rw [hΔ]
            refine List.pairwise_append.mpr ⟨?_, hapF, ?_⟩
            · refine List.pairwise_map.mpr (hap.imp_of_mem ?_)
              intro x y hx hy hxy
              obtain ⟨bx, hbx, hlex, _⟩ := hok x hx
              obtain ⟨by', hby, hley, _⟩ := hok y hy
              rw [partRegion_eq hbx, partRegion_eq hby]
              obtain ⟨hix, hex⟩ := List.getElem?_eq_some_iff.mp hbx
              obtain ⟨hiy, hey⟩ := List.getElem?_eq_some_iff.mp hby
              have hbxE := List.mem_of_getElem? hbx
              have hbyE := List.mem_of_getElem? hby
              by_cases hij : x.1 = y.1
              · have hsame : bx = by' := by
                  rw [hij] at hbx
                  exact Option.some.inj (hbx.symm.trans hby)
                subst hsame
                exact disjoint_same (hlt bx (hE bx hbxE)) hlex hley
                  (hxy.resolve_left (fun h => h hij))
              · have hd : Disjoint bx.1 bx.2.size by'.1 by'.2.size := by
                  have hp := List.pairwise_iff_getElem.mp hapE
                  rw [← hex, ← hey]
                  rcases Nat.lt_or_gt_of_ne hij with h | h
                  · exact hp _ _ hix hiy h
                  · exact (hp _ _ hiy hix h).symm
                exact hd.parts hlex hley (hlt bx (hE bx hbxE)) (hlt by' (hE by' hbyE))
            · intro c hc f hf
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
              obtain ⟨b, hb, hle, _⟩ := hok x hx
              rw [partRegion_eq hb]
              have hbE := List.mem_of_getElem? hb
              exact (hapEF b hbE f hf).part_left hle (hlt b (hE b hbE)) (hlt f (hF f hf)) } }

/-- **The case where only what is known changes**: each thing known
following from something known before of the same value. -/
theorem Regards.follows {Γ : Ctx} (fs : List Fact)
    (h : ∀ f ∈ fs, ∃ τ, (f.1, τ) ∈ Γ.known ∧ Follows fetch sys f.1 τ f.2) :
    Regards fetch sys Ψ Γ { Γ with known := fs } :=
  Regards.parts (E := []) (F := Γ.held) (L := []) rfl rfl
    (fun f hf Ψ' n hg =>
      let ⟨τ, hτ, hfol⟩ := h f hf
      hfol Ψ' n (hg _ hτ))
    rfl rfl (fun _ hx => nomatch hx) .nil (fun i b hb => by simp at hb)

/-! ## Naming what a region holds -/

/-- A state that matches a context matches it still when a region it holds
is said to hold, at eight of its bytes, the value that is there. -/
theorem WellTyped.nameSlot {n : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    {i : Nat} {b : BitVec 64} {S : Held} (hi : Γ.held[i]? = some (b, S)) {o : Nat}
    (ho : o + 8 ≤ S.size) :
    WellTyped fetch sys Ψ n
      { Γ with held := (Γ.held.set i
          (b, ⟨S.size, (o, s.load64 (b + BitVec.ofNat 64 o)) :: S.vals⟩)) } s := by
  obtain ⟨hilt, hieq⟩ := List.getElem?_eq_some_iff.mp hi
  have hbS : (b, S) ∈ Γ.held := List.mem_of_getElem? hi
  -- each region of the new list is one of the old, or the one renamed
  have hmem : ∀ c ∈ Γ.held.set i (b, ⟨S.size, (o, s.load64 (b + BitVec.ofNat 64 o)) :: S.vals⟩),
      c ∈ Γ.held ∨ c = (b, ⟨S.size, (o, s.load64 (b + BitVec.ofNat 64 o)) :: S.vals⟩) :=
    fun c hc => List.mem_or_eq_of_mem_set hc
  exact
    { val := h.val
      known := h.known
      flags := h.flags
      heapPerm := h.heapPerm
      heap := h.heap
      text := h.text
      said := h.said
      rows := h.rows
      complete := fun x hx => by
        rcases h.complete x hx with ⟨c, hc, hin⟩ | hr
        · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc
          refine .inl ⟨(Γ.held.set i (b, ⟨S.size, (o, s.load64 (b + BitVec.ofNat 64 o)) ::
            S.vals⟩))[m]'(by rw [List.length_set]; exact hm), List.getElem_mem _, ?_⟩
          rw [List.getElem_set]
          split
          · next him => subst him; rw [hieq] at hin; exact hin
          · exact hin
        · exact .inr hr
      held :=
        { perm := fun c hc => by
            rcases hmem c hc with hc | rfl
            · exact h.held.perm c hc
            · exact h.held.perm (b, S) hbS
          size_lt := fun c hc => by
            rcases hmem c hc with hc | rfl
            · exact h.held.size_lt c hc
            · exact h.held.size_lt (b, S) hbS
          fits := fun c hc p hp => by
            rcases hmem c hc with hc | rfl
            · exact h.held.fits c hc p hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · exact ho
              · exact h.held.fits (b, S) hbS p hp
          vals := fun c hc p hp => by
            rcases hmem c hc with hc | rfl
            · exact h.held.vals c hc p hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · rfl
              · exact h.held.vals (b, S) hbS p hp
          heap := fun c hc a l hl => by
            rcases hmem c hc with hc | rfl
            · exact h.held.heap c hc a l hl
            · exact h.held.heap (b, S) hbS a l hl
          apart := by
            have hp := List.pairwise_iff_getElem.mp h.held.apart
            refine List.pairwise_iff_getElem.mpr fun j k hj hk hjk => ?_
            rw [List.length_set] at hj hk
            have hsame : ∀ m (hm : m < Γ.held.length),
                ((Γ.held.set i (b, ⟨S.size, (o, s.load64 (b + BitVec.ofNat 64 o)) :: S.vals⟩))[m]'(by
                  rw [List.length_set]; exact hm)).1 = Γ.held[m].1 ∧
                ((Γ.held.set i (b, ⟨S.size, (o, s.load64 (b + BitVec.ofNat 64 o)) :: S.vals⟩))[m]'(by
                  rw [List.length_set]; exact hm)).2.size = Γ.held[m].2.size := by
              intro m hm
              rw [List.getElem_set]
              split
              · next him => subst him; rw [hieq]; exact ⟨rfl, rfl⟩
              · exact ⟨rfl, rfl⟩
            rw [(hsame j hj).1, (hsame j hj).2, (hsame k hk).1, (hsame k hk).2]
            exact hp j k hj hk hjk } }

/-- **Code typed whatever value a region holds at eight of its bytes is
typed where the context says nothing of them.** The value is the state's,
which no context before says: this is how a context comes to name it. -/
theorem Ok.nameSlot {n : Nat} {a : BitVec 64} {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}
    (hi : Γ.held[i]? = some (b, S)) {o : Nat}
    (ho : ∀ (Ψ' : MemTy) (m : Nat), (∀ g ∈ Γ.known, HasTy fetch sys Ψ' m g.2 g.1) → o + 8 ≤ S.size)
    (h : ∀ x, Ok fetch sys Ψ n a
      { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) :
    Ok fetch sys Ψ n a Γ :=
  fun k hk Ψ' he hwf s hs hw => h _ k hk Ψ' he hwf s hs (hw.nameSlot hi (ho Ψ' _ hw.known))

/-! ## The same of arriving -/

/-- **The machine arrives in a context where it arrives in any the context
may be regarded as.** -/
theorem Arrives.regard {n : Nat} {t : BitVec 64} {Γ Δ : Ctx} (h : Regards fetch sys Ψ Γ Δ)
    (hΔ : Arrives fetch sys Ψ n t Δ) : Arrives fetch sys Ψ n t Γ :=
  fun k hk Ψ' he hwf s hs hw => hΔ k hk Ψ' he hwf s hs (h (k + 1) Ψ' he hwf s hw)

theorem Arrives.nameSlot {n : Nat} {t : BitVec 64} {Γ : Ctx} {i : Nat} {b : BitVec 64} {S : Held}
    (hi : Γ.held[i]? = some (b, S)) {o : Nat}
    (ho : ∀ (Ψ' : MemTy) (m : Nat), (∀ g ∈ Γ.known, HasTy fetch sys Ψ' m g.2 g.1) → o + 8 ≤ S.size)
    (h : ∀ x, Arrives fetch sys Ψ n t
      { Γ with held := Γ.held.set i (b, ⟨S.size, (o, x) :: S.vals⟩) }) :
    Arrives fetch sys Ψ n t Γ :=
  fun k hk Ψ' he hwf s hs hw => h _ k hk Ψ' he hwf s hs (hw.nameSlot hi (ho Ψ' _ hw.known))

end TypedAsm.U
