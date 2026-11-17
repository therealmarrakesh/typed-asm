import TypedAsm.U.Split

/-!
# A held region made a block others may point into

Code builds something in memory it holds alone, where it may store what it
likes, and then hands it on as a block of a shape: from there on its typed
values keep their types, and anything may point to it. Nothing happens to
the machine; the memory typing gains a block, and the context, in place of
the region, the knowledge that its address points to one.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- The memory typing with a block added. -/
def MemTy.add (Ψ : MemTy) (a : BitVec 64) (L : Layout) : MemTy :=
  ⟨fun x => if x = a then some L else Ψ x, Ψ.kinds⟩

namespace MemTy

variable {a : BitVec 64} {L : Layout}

theorem add_self : (Ψ.add a L) a = some L := by
  show (if a = a then some L else Ψ a) = some L
  simp only [↓reduceIte]

theorem add_cases {x : BitVec 64} {l : Layout} (h : (Ψ.add a L) x = some l) :
    (x = a ∧ l = L) ∨ (x ≠ a ∧ Ψ x = some l) := by
  change (if x = a then some L else Ψ x) = some l at h
  split at h
  · next hx => exact .inl ⟨hx, (Option.some.inj h).symm⟩
  · next hx => exact .inr ⟨hx, h⟩

theorem add_ext (hN : Ψ a = none) : Ψ.Ext (Ψ.add a L) :=
  ⟨fun x l hl => by
    have hx : x ≠ a := fun e => by rw [e, hN] at hl; cases hl
    show (if x = a then some L else Ψ x) = some l
    simp only [hx, ↓reduceIte]
    exact hl, rfl⟩

theorem add_wf (hΨ : Ψ.WF) (hpos : 0 < L.size) (hlt : L.size < 2 ^ 64)
    (hdis : ∀ b lb, Ψ b = some lb → Disjoint a L.size b lb.size)
    (hin : ∀ p ∈ L.shape.vals, p.1 + 8 ≤ L.shape.size)
    (hkind : ∀ t, L.tag = some t → Ψ.kinds t = some L.shape)
    (hsaid : L.said = none) : (Ψ.add a L).WF := by
  constructor
  · intro x l hl
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · exact hlt
    · exact hΨ.size_lt x l hl'
  · intro x y lx ly hx hy hxy
    rcases add_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx'⟩
    · rcases add_cases hy with ⟨rfl, -⟩ | ⟨-, hy'⟩
      · exact absurd rfl hxy
      · exact hdis y ly hy'
    · rcases add_cases hy with ⟨rfl, rfl⟩ | ⟨-, hy'⟩
      · exact (hdis x lx hx').symm
      · exact hΨ.disjoint x y lx ly hx' hy' hxy
  · intro x l hl
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · exact hpos
    · exact hΨ.nonempty x l hl'
  · intro x l hl p hp
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · exact hin p hp
    · exact hΨ.fits x l hl' p hp
  · intro x l hl t ht
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · exact hkind t ht
    · exact hΨ.kinds x l hl' t ht
  · intro x l b hl hb
    rcases add_cases hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
    · rw [hsaid] at hb; cases hb
    · exact hΨ.said x l b hl' hb

end MemTy

/-- A block that is there, holds what its layout says and overlaps nothing
the context holds may join the memory typing. -/
theorem WellTyped.addBlock {n : Nat} {Γ : Ctx} {s : State} {a : BitVec 64} {L : Layout}
    (h : WellTyped fetch sys Ψ n Γ s) (hN : Ψ a = none)
    (hperm : s.canRead a L.size = true ∧ (L.writable = true → s.canWrite a L.size = true))
    (hvals : ∀ p ∈ L.shape.vals, HasTy fetch sys Ψ n p.2 (s.load64 (a + BitVec.ofNat 64 p.1)))
    (htext : L.text = 0) (hheld : ∀ c ∈ Γ.held, Disjoint c.1 c.2.size a L.size)
    (hsaid : L.said = none) : WellTyped fetch sys (Ψ.add a L) n Γ s :=
  have he := MemTy.add_ext (L := L) hN
  { val := h.val
    known := fun f hf => (h.known f hf).ext he
    flags := h.flags
    heapPerm := fun x l hl => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · exact hperm
      · exact h.heapPerm x l hl'
    heap := fun x l hl p hp => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · exact (hvals p hp).ext he
      · exact (h.heap x l hl' p hp).ext he
    text := fun x l hl ht => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · exact absurd htext ht
      · exact h.text x l hl' ht
    said := fun x l b hl hb => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · rw [hsaid] at hb; cases hb
      · exact h.said x l b hl' hb
    held :=
      { perm := h.held.perm
        size_lt := h.held.size_lt
        fits := h.held.fits
        vals := h.held.vals
        heap := fun c hc x l hl => by
          rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
          · exact hheld c hc
          · exact h.held.heap c hc x l hl'
        apart := h.held.apart } }

/-- What is known of a block's address besides its shape: that it is a block
of a kind, where it is one. -/
def tagFacts (b : BitVec 64) : Option Nat → List Fact
  | some t => [(b, Ty.ref t true 0)]
  | none => []

/-- **A held region may be regarded as a block others may point into**, of
any shape its first bytes stand for: where the shape gives a type, the
region holds a value there that is known to be of it, or the type asks
nothing. The region is no longer held; its address is known to point to the
block, and to a block of the kind, if it is made one of a kind. What is
past the shape's bytes is given up. -/
theorem Regards.publish {Γ : Ctx} {k : Nat} {b : BitVec 64} {S : Held} {K : Shape}
    (tag : Option Nat) (hk : Γ.held[k]? = some (b, S)) (hne : 0 < K.size)
    (hle : K.size ≤ S.size) (hfit : ∀ q ∈ K.vals, q.1 + 8 ≤ K.size)
    (hvals : ∀ q ∈ K.vals, q.2 = .any ∨
      ∃ v τ', (q.1, v) ∈ S.vals ∧ (v, τ') ∈ Γ.known ∧ Sub v τ' q.2)
    (hkind : ∀ t, tag = some t → Ψ.kinds t = some K) :
    Regards fetch sys Ψ Γ
      { Γ with
        held := Γ.held.eraseIdx k
        known := (b, Ty.ptr K true 0) :: (tagFacts b tag ++ Γ.known) } := by
  intro j Ψ' he hwf s h
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hin : (b, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hsz := h.held.size_lt _ hin
  have hpm := h.held.perm _ hin
  have hhp := h.held.heap _ hin
  simp only at hsz hpm hhp
  -- no block of the memory typing starts where this region does
  have hN : Ψ' b = none := by
    cases hl : Ψ' b with
    | none => rfl
    | some l =>
      have hd := (hhp b l hl).1 (by have := hwf.nonempty b l hl; omega)
      exact absurd hd (by bv_omega)
  have hsize : (⟨K, true, tag, 0, none⟩ : Layout).size = K.size := by simp [Layout.size]
  have hpmK : s.canWrite b K.size = true := Linux.canWrite_le hpm hle
  have hB := (h.eraseHeld k).addBlock (a := b) (L := ⟨K, true, tag, 0, none⟩) hN
    (by rw [hsize]; exact ⟨State.canRead_of_canWrite hpmK, fun _ => hpmK⟩)
    (fun q hq => by
      rcases hvals q hq with hany | ⟨v, τ', hv, hτ', hsub⟩
      · rw [hany]; exact HasTy.any _
      · rw [h.held.vals _ hin (q.1, v) hv]
        exact (h.known _ hτ').sub hsub)
    rfl
    (fun c hc => by
      obtain ⟨i, hi, hik, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hc
      have hd := h.held_apart hi hklt hik
      rw [hkeq] at hd
      rw [hsize]
      exact (hd.prefix_left hle hsz (h.held.size_lt _ (List.getElem_mem hi))).symm)
    rfl
  have hwf' : (Ψ'.add b ⟨K, true, tag, 0, none⟩).WF :=
    MemTy.add_wf hwf (by rw [hsize]; omega) (by rw [hsize]; omega)
      (fun x lx hl => by rw [hsize]; exact (hhp x lx hl).prefix_left hle hsz (hwf.size_lt x lx hl))
      hfit (fun t ht => by rw [he.kinds]; exact hkind t ht) rfl
  refine ⟨_, MemTy.add_ext hN, hwf', ?_⟩
  have hptr : HasTy fetch sys (Ψ'.add b ⟨K, true, tag, 0, none⟩) j (.ptr K true 0) b :=
    hasTy_ptr.mpr ⟨b, _, MemTy.add_self, rfl, fun _ => rfl, by simp⟩
  have := hB.addKnown ((b, Ty.ptr K true 0) :: tagFacts b tag)
    (fun f hf => by
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hptr
      · cases tag with
        | none => cases hf
        | some t =>
          have e : f = (b, Ty.ref t true 0) := List.mem_singleton.mp hf
          subst e
          exact hasTy_ref.mpr ⟨b, _, MemTy.add_self, rfl, fun _ => rfl, by simp⟩)
  exact this

end TypedAsm.U
