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

/-- **Fresh memory appearing where nothing was accessible is held**: the
state then matches the context it matched with one region more, of plain
bytes. It must be held: the context says all that is held, and the bytes
are now the program's. -/
theorem WellTyped.mapZero {a : BitVec 64} {size : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hal : a.toNat % 4096 = 0)
    (hsz4 : size % 4096 = 0) (hfit : a.toNat + size ≤ addrTop) (hlt : size < 2 ^ 64)
    (hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none) (hrows : Γ.rows = []) :
    WellTyped fetch sys Ψ n { Γ with held := (a, ⟨size, []⟩) :: Γ.held } (s.mapZero a size) := by
  have hnew : (s.mapZero a size).canWrite a size = true := by
    rw [State.canWrite_iff]
    intro i hi
    rw [State.perm_mapZero s hal hsz4 hfit]
    have : (a + BitVec.ofNat 64 i - a).toNat < size := by bv_omega
    simp only [this, ↓reduceIte]
    rfl
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
    rows := fun r hr => by
      have hr' : r ∈ Γ.rows := hr
      rw [hrows] at hr'
      cases hr'
    fed := fun r hr => by
      have hr' : r ∈ Γ.rows := hr
      rw [hrows] at hr'
      cases hr'
    complete := fun x hx => by
      rw [State.perm_mapZero s hal hsz4 hfit] at hx
      split at hx
      · next hin => exact .inl ⟨_, List.mem_cons_self, hin⟩
      · rcases h.complete x hx with ⟨c, hc, hl⟩ | hr
        · exact .inl ⟨c, List.mem_cons_of_mem _ hc, hl⟩
        · exact .inr hr
    held :=
      HeldOk.cons (Γ := Γ) (b := (a, ⟨size, []⟩))
        ({ perm := fun b hb' => hwr _ _ (h.held.perm b hb')
           size_lt := h.held.size_lt
           fits := h.held.fits
           vals := fun b hb' p hp => by
             have hr := State.canRead_of_canWrite (State.canWrite_sub (h.held.perm b hb')
               (o := p.1) (m := 8) (h.held.fits b hb' p hp))
             rw [State.load64_mapZero_out s hal hsz4 hfit (hout _ hr)]
             exact h.held.vals b hb' p hp
           heap := h.held.heap
           apart := h.held.apart } : HeldOk Ψ Γ (s.mapZero a size))
        hnew hlt (fun _ hp => nomatch hp) (fun _ hp => nomatch hp)
        (fun x l hl => Linux.disjoint_of_unmapped hU (by omega) (Nat.le_refl _)
          (hΨ.size_lt x l hl) (h.heapPerm x l hl).1)
        (fun c hc' => Linux.disjoint_of_unmapped hU (by omega) (Nat.le_refl _)
          (h.held.size_lt c hc') (State.canRead_of_canWrite (h.held.perm c hc'))) }

/-- The same, of memory the machine reports unmapped. -/
theorem WellTyped.mapZero_held {a : BitVec 64} {size : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hal : a.toNat % 4096 = 0)
    (hsz4 : size % 4096 = 0) (hfit64 : a.toNat + size ≤ addrTop)
    (hlt : size < 2 ^ 64) (hun : s.unmapped a size = true) (hrows : Γ.rows = []) :
    WellTyped fetch sys Ψ n { Γ with held := (a, ⟨size, []⟩) :: Γ.held } (s.mapZero a size) :=
  h.mapZero hΨ hal hsz4 hfit64 hlt (fun _ hx => Linux.perm_of_unmapped hal hfit64 hun hx) hrows

/-- **A call that hands back fresh memory** returns with an error number in
`rax`, or with the address of whole pages that the context then holds, as
plain bytes. The address is the start of a page, in the part of the address
space a program's memory is in. -/
theorem Steps.map {D : SysDesc} (hD : Describes sys D) {Γ : Ctx} {next : BitVec 64}
    (hk : D.kind (Γ.val .rax) = some .map) (hdi : Γ.val .rdi = 0)
    (hpre : ∀ n, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = next →
      WellTyped fetch sys Ψ' n Γ s → D.pre s) (hrows : Γ.rows = []) :
    Steps fetch sys Ψ .syscall next Γ fun t Γ' => t = next ∧ ∃ v r,
      (SysErr v ∧ Γ' = Γ.afterSys v r next) ∨
      (v.toNat % 4096 = 0 ∧ 0 < v.toNat ∧ v.toNat + pages (Γ.val .rsi) ≤ addrTop ∧
        Γ' = CtxOf.afterSys { Γ with held := (v, ⟨pages (Γ.val .rsi), []⟩) :: Γ.held } v r
          next) := by
  intro n Ψ' he hwf s hrip hw
  obtain ⟨t, hst, hmaps⟩ := hD s .map (by rw [hw.val]; exact hk) (hpre n Ψ' he hwf s hrip hw)
    (by rw [hw.val]; exact hdi)
  rw [hw.val .rsi] at hmaps
  rcases hmaps with ⟨v, w, hv, rfl⟩ | ⟨a, w, hal, hpos, hfit, hun, rfl⟩
  · refine ⟨_, hst, Γ.afterSys v (w.saved 0) next, ⟨hrip, v, _, .inl ⟨hv, rfl⟩⟩, ?_⟩
    rw [← hrip]
    exact hw.ret v w (.inr hrows)
  · refine ⟨_, hst, _, ⟨hrip, a, w.saved 0, .inr ⟨hal, hpos, hfit, rfl⟩⟩, ?_⟩
    have hT : addrTop = 0x7ffffffff000 := rfl
    have h4 : pages (Γ.val .rsi) % 4096 = 0 := Nat.mul_mod_left _ _
    have hH := hw.mapZero_held hwf hal h4 hfit (by omega) hun hrows
    rw [← hrip]
    exact hH.ret a w (.inr hrows)

end TypedAsm.U
