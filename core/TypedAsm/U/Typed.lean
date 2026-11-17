import TypedAsm.U.Blocks
import TypedAsm.U.Loaded
import TypedAsm.U.LayoutS
import TypedAsm.Bytes
import TypedAsm.U.Labels

/-!
# The typed values of the blocks a program says

A block a program says one of its segments holds may say that some of its
bytes hold a value something is known of: a pointer to another of the
blocks, or nought. Whether that is so is seen in the segment's bytes.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

/-- The value eight bytes of a list make, from the `j`th. -/
def wordAt (d : List Byte) (j : Nat) : BitVec 64 := ofBytes ((d.drop j).take 8)

/-- **A value loaded from a segment's pages is the one its bytes make.** -/
theorem load64_pageData {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    {g : Nat × Perm × List Byte} (hg : g ∈ segs) {t : State}
    (hmem : t.mem = (State.init.loadSegs segs).mem) {j : Nat} (hj : j + 8 ≤ (pageData g).length) :
    t.load64 (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 j) = wordAt (pageData g) j := by
  rw [State.load64_ofBytes, wordAt]
  congr 1
  apply List.ext_getElem
  · simp only [State.loadBytes, List.length_map, List.length_range, List.length_take,
      List.length_drop]
    omega
  · intro i h1 h2
    have hi : i < 8 := by
      simp only [State.loadBytes, List.length_map, List.length_range] at h1
      exact h1
    simp only [State.loadBytes, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    have e : BitVec.ofNat 64 g.1 + BitVec.ofNat 64 j + BitVec.ofNat 64 i
        = BitVec.ofNat 64 g.1 + BitVec.ofNat 64 (j + i) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [e]
    exact mem_pageData hok hg hmem (by omega)

/-- The typed values of a shape, as a list. -/
def ValsS.toList : ValsS → List (Nat × TyS)
  | .nil => []
  | .cons o τ rest => (o, τ) :: rest.toList

theorem ValsS.den_toList (ρ : Env) : (vs : ValsS) →
    vs.den ρ = vs.toList.map fun p => (p.1, p.2.den ρ)
  | .nil => rfl
  | .cons o τ rest => by
    simp only [ValsS.den, ValsS.toList, List.map_cons, ValsS.den_toList ρ rest]

/-- Whether a thing is so of a value, as far as the blocks said show: that
it is the address of a byte of one of them, of a shape or a kind; that it
is nought, where it may be; that it lies in a range; and, as far as `j`
shows, that it is code wanting a family. -/
def tyHolds (j : BitVec 64 → CtxS → Bool) (bs : List (BitVec 64 × LayoutS)) :
    TyS → BitVec 64 → Bool
  | .any, _ => true
  | .range lo hi, v => decide (v - lo ≤ hi - lo)
  | .nullable τ, v => v == 0 || tyHolds j bs τ v
  | .code regs flags held known rest, v => j v (codeCtx regs flags held known rest)
  | .ptr S w off, v => bs.any fun b =>
      b.2.shape == S && (!w || b.2.writable) && v == b.1 + BitVec.ofNat 64 off
  | .ref tag w off, v => bs.any fun b =>
      b.2.tag == some tag && (!w || b.2.writable) && v == b.1 + BitVec.ofNat 64 off
  | _, _ => false

theorem tyHolds_hasTy {j : BitVec 64 → CtxS → Bool} {bs : List (BitVec 64 × LayoutS)}
    {kinds : Nat → Option Shape}
    (hnd : (denBlocks bs).Pairwise fun x y => x.1 ≠ y.1) (n : Nat)
    (hj : ∀ a E, j a E = true → ∀ (ρ : Env) (fam : Fam),
      Ok fetch sys (MemTy.ofList (denBlocks bs) kinds) n a
        (E.den { ρ with bound := fam :: ρ.bound })) :
    (τ : TyS) → (v : BitVec 64) → tyHolds j bs τ v = true →
    HasTy fetch sys (MemTy.ofList (denBlocks bs) kinds) n (τ.den {}) v
  | .any, _, _ => HasTy.any _
  | .range lo hi, v, h => hasTy_range.mpr (of_decide_eq_true h)
  | .nullable τ, v, h => by
    simp only [tyHolds, Bool.or_eq_true, beq_iff_eq] at h
    refine (hasTy_nullable (τ := τ.den {})).mpr ?_
    rcases h with h | h
    · exact .inl h
    · exact .inr (tyHolds_hasTy hnd n hj τ v h)
  | .ptr S w off, v, h => by
    simp only [tyHolds, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨b, hb, ⟨hS, hw⟩, hv⟩ := h
    simp only [TyS.den, HasTy]
    refine ⟨b.1, b.2.den, MemTy.ofList_of_mem _ hnd (b.1, b.2.den) (List.mem_map.mpr ⟨b, hb, rfl⟩),
      ?_, fun hw' => ?_, hv⟩
    · show b.2.shape.den {} = S.den {}
      rw [hS]
    · rcases hw with hw | hw
      · rw [hw] at hw'; cases hw'
      · exact hw
  | .ref tag w off, v, h => by
    simp only [tyHolds, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at h
    obtain ⟨b, hb, ⟨ht, hw⟩, hv⟩ := h
    simp only [TyS.den, HasTy]
    refine ⟨b.1, b.2.den, MemTy.ofList_of_mem _ hnd (b.1, b.2.den) (List.mem_map.mpr ⟨b, hb, rfl⟩),
      ht, fun hw' => ?_, hv⟩
    rcases hw with hw | hw
    · rw [hw] at hw'; cases hw'
    · exact hw
  | .orErr _, _, h => nomatch h
  | .str _, _, h => nomatch h
  | .atom _, _, h => nomatch h
  | .arr .., _, h => nomatch h
  | .upTo .., _, h => nomatch h
  | .code regs flags held known rest, v, h => by
    rw [code_den, hasTy_code]
    intro x k hk Ψ' he hwf s hs hw
    exact hj v _ h {} x k (Nat.le_of_lt hk) Ψ' he hwf s hs hw

/-- Whether each typed value of each block is so of the eight bytes the
block's segment has there. -/
def valsHold (j : BitVec 64 → CtxS → Bool) (segs : List (Nat × Perm × List Byte))
    (bs : List (BitVec 64 × LayoutS)) : Bool :=
  bs.all fun x => x.2.shape.vals.toList.all fun p =>
    match segs.find? fun g => blockOf g (x.1, x.2.den) with
    | some g =>
      decide (x.1.toNat - g.1 + p.1 + 8 ≤ (pageData g).length) &&
        tyHolds j bs p.2 (wordAt (pageData g) (x.1.toNat - g.1 + p.1))
    | none => false

/-- **Each block holds what its shape says**, in a state whose memory is
that of the segments placed. -/
theorem heap_of_check {segs : List (Nat × Perm × List Byte)} (hok : segsOk segs = true)
    {t : State} (hmem : t.mem = (State.init.loadSegs segs).mem)
    {j : BitVec 64 → CtxS → Bool} {bs : List (BitVec 64 × LayoutS)} {kinds : Nat → Option Shape}
    (hnd : (denBlocks bs).Pairwise fun x y => x.1 ≠ y.1) (h : valsHold j segs bs = true) (n : Nat)
    (hj : ∀ a E, j a E = true → ∀ (ρ : Env) (fam : Fam),
      Ok fetch sys (MemTy.ofList (denBlocks bs) kinds) n a
        (E.den { ρ with bound := fam :: ρ.bound })) :
    ∀ x ∈ denBlocks bs, ∀ p ∈ x.2.shape.vals,
      HasTy fetch sys (MemTy.ofList (denBlocks bs) kinds) n p.2
        (t.load64 (x.1 + BitVec.ofNat 64 p.1)) := by
  intro x hx p hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hp' : p ∈ y.2.shape.vals.den {} := by
    cases hs : y.2.shape with
    | mk size vals =>
      have : (y.2.den).shape.vals = vals.den {} := by
        show (y.2.shape.den {}).vals = _
        rw [hs]
        rfl
      rw [this] at hp
      show p ∈ (ShapeS.mk size vals).vals.den {}
      exact hp
  rw [ValsS.den_toList] at hp'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
  have hc := List.all_eq_true.mp (List.all_eq_true.mp h y hy) q hq
  split at hc
  · next g hfind =>
    have hg := List.mem_of_find?_eq_some hfind
    have hb : blockOf g (y.1, y.2.den) = true :=
      List.find?_some (p := fun g => blockOf g (y.1, y.2.den)) hfind
    simp only [blockOf, Bool.and_eq_true, decide_eq_true_eq] at hb
    have h1 : g.1 ≤ y.1.toNat := hb.1.1.1.1
    rw [Bool.and_eq_true, decide_eq_true_eq] at hc
    show HasTy fetch sys _ n (q.2.den {}) (t.load64 (y.1 + BitVec.ofNat 64 q.1))
    rw [block_addr (g := g) (x := (y.1, y.2.den)) h1 q.1, load64_pageData hok hg hmem hc.1]
    exact tyHolds_hasTy hnd n hj q.2 _ hc.2
  · cases hc

/-- Whether something a program says of its static data is seen in the
blocks it says: of an address written out, something that mentions nothing
and is so of it by the blocks; or that it is text. -/
def staticS (bs : List (BitVec 64 × LayoutS)) (f : Val × TyS) : Bool :=
  (match f.1 with
   | .lit v => f.2.ground && tyHolds (fun _ _ => false) bs f.2 v
   | _ => false) || staticOk (denBlocks bs) f

/-- **What is seen so is so**, under the typing of those blocks and every
one it grows to. -/
theorem staticsOk_of_holds {bs : List (BitVec 64 × LayoutS)} {kinds : Nat → Option Shape}
    {st : List (Val × TyS)} (hnd : (denBlocks bs).Pairwise fun x y => x.1 ≠ y.1)
    (h : st.all (staticS bs) = true) :
    StaticsOk fetch sys (MemTy.ofList (denBlocks bs) kinds) st := by
  intro ρ f hf n Ψ' hext hwf
  have hc := List.all_eq_true.mp h f hf
  rcases Bool.or_eq_true _ _ |>.mp hc with hc | hc
  · obtain ⟨v, τ⟩ := f
    cases v with
    | lit v =>
      simp only [Bool.and_eq_true] at hc
      rw [TyS.den_ground ρ {} τ hc.1]
      exact (tyHolds_hasTy (j := fun _ _ => false) hnd n (fun _ _ h => Bool.noConfusion h) τ v
        hc.2).ext hext
    | _ => cases hc
  · exact staticsOk_of_check (st := [f]) hnd (by simp only [List.all_cons, hc, List.all_nil,
      Bool.and_self]) ρ f List.mem_cons_self n Ψ' hext hwf

end TypedAsm.U
