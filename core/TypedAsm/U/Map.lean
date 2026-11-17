import TypedAsm.U.Publish
import TypedAsm.U.LinuxDesc

/-!
# Memory asked of the system

Fresh memory, appearing where nothing was accessible, leaves a state
matching the context it matched; and the context may hold it, as a region
of plain bytes. Nothing the context knew of can have pointed there.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat} {Γ : Ctx} {s : State}

/-- Fresh memory appearing where nothing was accessible leaves a state
matching the context it matched. -/
theorem WellTyped.mapZero {a : BitVec 64} {size : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hal : a.toNat % 4096 = 0)
    (hsz4 : size % 4096 = 0) (hfit : a.toNat + size ≤ addrTop)
    (hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none) :
    WellTyped fetch sys Ψ n Γ (s.mapZero a size) := by
  have hout : ∀ y : BitVec 64, s.canRead y 8 = true →
      ∀ j : BitVec 64, j < 8 → ¬ ((y + j) - a).toNat < size := by
    intro y hy j hj hin
    have hr := State.canRead_iff.mp hy j.toNat (by bv_omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hU _ hin] at hr
    exact absurd hr (by decide)
  have hwr : ∀ (y : BitVec 64) (m : Nat), s.canWrite y m = true →
      (s.mapZero a size).canWrite y m = true := by
    intro y m hy
    rw [State.canWrite_iff] at hy ⊢
    intro i hi
    rw [State.perm_mapZero s hal hsz4 hfit]
    split
    · rfl
    · exact hy i hi
  have hrd : ∀ (y : BitVec 64) (m : Nat), s.canRead y m = true →
      (s.mapZero a size).canRead y m = true := by
    intro y m hy
    rw [State.canRead_iff] at hy ⊢
    intro i hi
    rw [State.perm_mapZero s hal hsz4 hfit]
    split
    · rfl
    · exact hy i hi
  exact {
    val := h.val
    known := h.known
    flags := h.flags
    heapPerm := fun x l hl =>
      ⟨hrd _ _ (h.heapPerm x l hl).1, fun hw => hwr _ _ ((h.heapPerm x l hl).2 hw)⟩
    heap := fun x l hl p hp => by
      have hr := State.canRead_sub (h.heapPerm x l hl).1 (o := p.1) (m := 8)
        (by have := hΨ.fits x l hl p hp; simp only [Layout.size]; omega)
      rw [State.load64_mapZero_out s hal hsz4 hfit (hout _ hr)]
      exact h.heap x l hl p hp
    text := fun x l hl ht => by
      rw [State.mem_mapZero s hal hsz4 hfit]
      split
      · next hin =>
        have hr := State.canRead_iff.mp (h.heapPerm x l hl).1 (l.size - 1) (by
          have := hΨ.nonempty x l hl; omega)
        have hn := hU _ hin
        rw [hn] at hr
      · exact h.text x l hl ht
    said := fun x l b hl hb k hk => by
      have hlb := (hΨ.said x l b hl hb).2
      rw [State.mem_mapZero s hal hsz4 hfit]
      split
      · next hin =>
        have hr := State.canRead_iff.mp (h.heapPerm x l hl).1 k (by omega)
        have hn := hU _ hin
        rw [hn] at hr
        exact absurd hr (by decide)
      · exact h.said x l b hl hb k hk
    held :=
      { perm := fun b hb' => hwr _ _ (h.held.perm b hb')
        size_lt := h.held.size_lt
        fits := h.held.fits
        vals := fun b hb' p hp => by
          have hr := State.canRead_of_canWrite (State.canWrite_sub (h.held.perm b hb')
            (o := p.1) (m := 8) (h.held.fits b hb' p hp))
          rw [State.load64_mapZero_out s hal hsz4 hfit (hout _ hr)]
          exact h.held.vals b hb' p hp
        heap := h.held.heap
        apart := h.held.apart } }

/-- **Fresh memory may be held**, as a region of plain bytes. -/
theorem WellTyped.mapZero_held {a : BitVec 64} {size : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hal : a.toNat % 4096 = 0)
    (hsz4 : size % 4096 = 0) (hfit64 : a.toNat + size ≤ addrTop)
    (hlt : size < 2 ^ 64) (hun : s.unmapped a size = true) :
    WellTyped fetch sys Ψ n { Γ with held := (a, ⟨size, []⟩) :: Γ.held } (s.mapZero a size) := by
  have hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none :=
    fun x hx => Linux.perm_of_unmapped hal hfit64 hun hx
  have hZ := h.mapZero hΨ hal hsz4 hfit64 hU
  have hnew : (s.mapZero a size).canWrite a size = true := by
    rw [State.canWrite_iff]
    intro i hi
    rw [State.perm_mapZero s hal hsz4 hfit64]
    have : (a + BitVec.ofNat 64 i - a).toNat < size := by bv_omega
    simp only [this, ↓reduceIte]
    rfl
  refine hZ.addHeld (b := (a, ⟨size, []⟩)) hnew hlt (fun _ hp => nomatch hp)
    (fun _ hp => nomatch hp) ?_ ?_
  · intro x l hl
    exact Linux.disjoint_of_unmapped hU (by omega) (Nat.le_refl _) (hΨ.size_lt x l hl)
      (h.heapPerm x l hl).1
  · intro c hc'
    exact Linux.disjoint_of_unmapped hU (by omega) (Nat.le_refl _) (h.held.size_lt c hc')
      (State.canRead_of_canWrite (h.held.perm c hc'))

end TypedAsm.U
