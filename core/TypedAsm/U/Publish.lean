import TypedAsm.Linux
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

/-- **A region held becomes a block of the memory typing**: one of the
same size, that holds what its layout says. The state then matches the
context without the region, under the memory typing with the block. Every
byte that was held is the block's: none is let go. -/
theorem WellTyped.toBlock {n : Nat} {Γ : Ctx} {s : State} {a : BitVec 64} {L : Layout} {k : Nat}
    {S : Held} (h : WellTyped fetch sys Ψ n Γ s) (hk : Γ.held[k]? = some (a, S))
    (hsize : L.size = S.size) (hN : Ψ a = none)
    (hvals : ∀ p ∈ L.shape.vals, HasTy fetch sys Ψ n p.2 (s.load64 (a + BitVec.ofNat 64 p.1)))
    (htext : L.text = 0) (hsaid : L.said = none) :
    WellTyped fetch sys (Ψ.add a L) n { Γ with held := Γ.held.eraseIdx k } s :=
  have he := MemTy.add_ext (L := L) hN
  have hklt := (List.getElem?_eq_some_iff.mp hk).1
  have hkeq := (List.getElem?_eq_some_iff.mp hk).2
  have hin : (a, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hsub : ∀ c ∈ Γ.held.eraseIdx k, c ∈ Γ.held :=
    fun c hc => (List.eraseIdx_sublist _ _).subset hc
  have hpm : s.canWrite a L.size = true := by rw [hsize]; exact h.held.perm _ hin
  { val := h.val
    known := fun f hf => (h.known f hf).ext he
    flags := h.flags
    heapPerm := fun x l hl => by
      rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
      · exact ⟨State.canRead_of_canWrite hpm, fun _ => hpm⟩
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
    complete := fun x hx => by
      rcases h.complete x hx with ⟨c, hc, hlt⟩ | ⟨base, l, hl, hlt⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
        by_cases hik : i = k
        · subst hik
          rw [hkeq] at hlt
          exact .inr ⟨a, L, MemTy.add_self, by rw [hsize]; exact hlt⟩
        · exact .inl ⟨_, List.mem_eraseIdx_iff_getElem.mpr ⟨i, hi, hik, rfl⟩, hlt⟩
      · exact .inr ⟨base, l, he.blocks base l hl, hlt⟩
    held :=
      { perm := fun c hc => h.held.perm c (hsub c hc)
        size_lt := fun c hc => h.held.size_lt c (hsub c hc)
        fits := fun c hc => h.held.fits c (hsub c hc)
        vals := fun c hc => h.held.vals c (hsub c hc)
        heap := fun c hc x l hl => by
          rcases MemTy.add_cases hl with ⟨rfl, rfl⟩ | ⟨-, hl'⟩
          · obtain ⟨i, hi, hik, rfl⟩ := List.mem_eraseIdx_iff_getElem.mp hc
            have hd := h.held_apart hi hklt hik
            rw [hkeq, ← hsize] at hd
            exact hd.symm
          · exact h.held.heap c (hsub c hc) x l hl'
        apart := h.held.apart.sublist (List.eraseIdx_sublist _ _) } }

/-- `Publishes Γ Δ`: every state that matches `Γ` matches `Δ` once the
memory typing has grown. It is not a way of regarding: memory held alone
has become memory others may point into, and stays so. It is asked only
where a program says so. -/
def Publishes (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ Δ : Ctx) : Prop :=
  ∀ k, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' k Γ s →
    ∃ Ψ'' : MemTy, Ψ'.Ext Ψ'' ∧ Ψ''.WF ∧ WellTyped fetch sys Ψ'' k Δ s

/-- Code typed in the context after is typed in the context before. -/
theorem Ok.publish {n : Nat} {a : BitVec 64} {Γ Δ : Ctx} (h : Publishes fetch sys Ψ Γ Δ)
    (hΔ : Ok fetch sys Ψ n a Δ) : Ok fetch sys Ψ n a Γ := by
  intro k hk Ψ' he hwf s hrip hw
  obtain ⟨Ψ'', he', hwf', hw'⟩ := h k Ψ' he hwf s hw
  exact hΔ k hk Ψ'' (he.trans he') hwf' s hrip hw'

/-- What is known of a block's address besides its shape: that it is a block
of a kind, where it is one. -/
def tagFacts (b : BitVec 64) : Option Nat → List Fact
  | some t => [(b, Ty.ref t true 0)]
  | none => []

/-- **A held region becomes a block others may point into**, of any shape
of its size: where the shape gives a type, the region holds a value there
that is of it wherever what the context knows is so, or the type asks
nothing. The region is no
longer held; its address is known to point to the block, and to a block of
the kind, if it is made one of a kind. The whole region becomes the block:
a part of it is first taken as a region of its own. -/
theorem Publishes.region {Γ : Ctx} {k : Nat} {b : BitVec 64} {S : Held} {K : Shape}
    (tag : Option Nat) (hk : Γ.held[k]? = some (b, S)) (hne : 0 < K.size)
    (hKS : K.size = S.size) (hfit : ∀ q ∈ K.vals, q.1 + 8 ≤ K.size)
    (hvals : ∀ q ∈ K.vals, q.2 = .any ∨
      ∃ v, (q.1, v) ∈ S.vals ∧ ∀ (Ψ' : MemTy) (n : Nat),
        (∀ g ∈ Γ.known, HasTy fetch sys Ψ' n g.2 g.1) → HasTy fetch sys Ψ' n q.2 v)
    (hkind : ∀ t, tag = some t → Ψ.kinds t = some K) :
    Publishes fetch sys Ψ Γ
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
  have hle : K.size ≤ S.size := Nat.le_of_eq hKS
  -- no block of the memory typing starts where this region does
  have hN : Ψ' b = none := by
    cases hl : Ψ' b with
    | none => rfl
    | some l =>
      have hd := (hhp b l hl).1 (by have := hwf.nonempty b l hl; omega)
      exact absurd hd (by bv_omega)
  have hsize : (⟨K, true, tag, 0, none⟩ : Layout).size = K.size := by simp [Layout.size]
  have hpmK : s.canWrite b K.size = true := Linux.canWrite_le hpm hle
  have hB := h.toBlock (a := b) (L := ⟨K, true, tag, 0, none⟩) hk (by rw [hsize]; exact hKS) hN
    (fun q hq => by
      rcases hvals q hq with hany | ⟨v, hv, hty⟩
      · rw [hany]; exact HasTy.any _
      · rw [h.held.vals _ hin (q.1, v) hv]
        exact hty Ψ' j h.known)
    rfl rfl
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
