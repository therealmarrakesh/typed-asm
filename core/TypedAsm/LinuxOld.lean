import TypedAsm.Soundness
import TypedAsm.Linux

/-!
# The Linux model and the old type system

What the old type system proves of the model's calls. It goes with the old
core.
-/

namespace TypedAsm

namespace Linux

end Linux

/-- Whether zero is a value of the type, whatever the memory typing. Fresh
memory is all zero, so these are the types its values may be given. -/
def Ty.zeroOk : Ty → Bool
  | .int => true
  | .eq v => decide (v = 0)
  | .nullable _ => true
  | .orErr τ => τ.zeroOk
  | _ => false

theorem HasTy.zero {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat} :
    ∀ {τ : Ty}, τ.zeroOk = true → HasTy fetch sys Ψ n τ 0
  | .int, _ => HasTy.int _
  | .eq v, h => hasTy_eq.mpr (by simpa [Ty.zeroOk] using Eq.symm (of_decide_eq_true h))
  | .nullable _, _ => hasTy_nullable.mpr (.inl rfl)
  | .orErr _, h => hasTy_orErr.mpr (.inr (HasTy.zero h))

variable {fetch : Fetch} {Ψ : MemTy} {Γ : Ctx}

namespace Linux

variable {n : Nat} {s : State}

/-- Returning from a call keeps a state well typed, with `rax`, `rcx` and
`r11` integers and nothing known about the flags. -/
theorem ret_ok {sys : Syscall} (h : WellTyped fetch sys Ψ n Γ s) (v : BitVec 64) :
    WellTyped fetch sys Ψ n Γ.afterSyscall (ret s v) :=
  (((h.setReg (by decide) (HasTy.int _)).setReg (by decide) (HasTy.int _)).setReg
    (by decide) (HasTy.int _)).setFlags (P := Flags.Any) trivial

/-- Returning from a call with a result of a known type. -/
theorem ret_typed {sys : Syscall} {τ : Ty} {v : BitVec 64} (h : WellTyped fetch sys Ψ n Γ s)
    (hv : HasTy fetch sys Ψ n τ v) :
    WellTyped fetch sys Ψ n (Γ.afterSyscall.setReg .rax τ) (ret s v) :=
  (ret_ok h v).retype (by decide) (by rw [ret_rax]; exact hv)

/-- **Fresh memory is a new block.** An `mmap` in the modelled form returns
an error number, or the address of memory that was not accessible before.
Nothing typed could point into such memory, so it may be given any shape
whose typed values all admit zero, and the memory typing grows by that block; what
was well typed before still is. -/
theorem mmap_ok {sys : Syscall} {len : BitVec 64} {S : Shape} {tag : Option Nat} {τ : Ty}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22)
    (hfit : S.size ≤ len.toNat) (hne : 0 < S.size)
    (hin : ∀ p ∈ S.vals, p.1 + 8 ≤ S.size)
    (hzero : ∀ p ∈ S.vals, p.2.zeroOk = true)
    (hkind : ∀ t, tag = some t → Ψ.kinds t = some S)
    (hτ : ∀ (Ψ₂ : MemTy) (a : BitVec 64), Ψ₂ a = some ⟨S, true, tag, 0, none⟩ →
      HasTy fetch sys Ψ₂ n τ a) :
    ∃ Ψ₂ : MemTy, Ψ.Ext Ψ₂ ∧ Ψ₂.WF ∧
      WellTyped fetch sys Ψ₂ n (Γ.afterSyscall.setReg .rax (.orErr τ)) (mmap s) := by
  have hsi := h.eqReg (by decide) hlen
  have hdx := h.eqReg (by decide) hprot
  have h10 := h.eqReg (by decide) hflags
  have herr : ∀ (t : State) (v : BitVec 64), WellTyped fetch sys Ψ n Γ t → SysErr v →
      ∃ Ψ₂ : MemTy, Ψ.Ext Ψ₂ ∧ Ψ₂.WF ∧
        WellTyped fetch sys Ψ₂ n (Γ.afterSyscall.setReg .rax (.orErr τ)) (ret t v) :=
    fun t v ht hv => ⟨Ψ, .refl _, hΨ, ret_typed ht (hasTy_orErr.mpr (.inl hv))⟩
  simp only [mmap, hsi, hdx, h10, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
  split
  · exact herr s _ h (by decide)
  · next hc =>
    split
    · exact herr _ _ (h.congr rfl rfl rfl rfl) (by decide)
    · next a _ =>
      split
      · next hok =>
        obtain ⟨hal, -, htop, hun⟩ := hok
        have hsz4 : (len.toNat + 4095) / 4096 * 4096 % 4096 = 0 := by omega
        generalize hsize : (len.toNat + 4095) / 4096 * 4096 = size at htop hun hsz4 ⊢
        have hT : addrTop = 0x7ffffffff000 := rfl
        have hfit64 : a.toNat + size ≤ addrTop := by omega
        have hsz : len.toNat ≤ size := by omega
        have hpos : 0 < size := by omega
        have hsz64 : size < 2 ^ 64 := by omega
        have hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none :=
          fun x hx => perm_of_unmapped hal hfit64 hun hx
        -- nothing readable overlaps the new block
        have hR : ∀ (b : BitVec 64) (m : Nat), m < 2 ^ 64 → s.canRead b m = true →
            Disjoint a S.size b m := by
          intro b m hm hr
          rw [State.canRead_iff] at hr
          refine ⟨fun hm0 => ?_, fun _ => ?_⟩
          · apply Classical.byContradiction
            intro hlt
            have hb := hr 0 (by omega)
            rw [show b + BitVec.ofNat 64 0 = b by simp, hU b (by bv_omega)] at hb
            exact absurd hb (by decide)
          · apply Classical.byContradiction
            intro hlt
            have hb := hr (a - b).toNat (by bv_omega)
            rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, show b + (a - b) = a by bv_omega,
              hU a (by simpa using hpos)] at hb
            exact absurd hb (by decide)
        have hN : Ψ a = none := by
          cases hl : Ψ a with
          | none => rfl
          | some l =>
            have hr := State.canRead_iff.mp (h.heapPerm a l hl).1 0 (hΨ.nonempty a l hl)
            rw [show a + BitVec.ofNat 64 0 = a by simp, hU a (by simpa using hpos)] at hr
            exact absurd hr (by decide)
        let L : Layout := ⟨S, true, tag, 0, none⟩
        let Ψ₂ : MemTy := ⟨fun x => if x = a then some L else Ψ x, Ψ.kinds⟩
        have hcases : ∀ x l, Ψ₂ x = some l → (x = a ∧ l = L) ∨ (x ≠ a ∧ Ψ x = some l) := by
          intro x l hl
          change (if x = a then some L else Ψ x) = some l at hl
          split at hl
          · next hx => exact .inl ⟨hx, (Option.some.inj hl).symm⟩
          · next hx => exact .inr ⟨hx, hl⟩
        have hat : Ψ₂ a = some L := by
          show (if a = a then some L else Ψ a) = some L
          simp only [↓reduceIte]
        have hext : Ψ.Ext Ψ₂ := ⟨fun x l hl => by
          have hx : x ≠ a := fun e => by rw [e, hN] at hl; cases hl
          show (if x = a then some L else Ψ x) = some l
          simp only [hx, ↓reduceIte]
          exact hl, rfl⟩
        have hWF : Ψ₂.WF := by
          constructor
          · intro x l hl
            rcases hcases x l hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
            · show S.size < 2 ^ 64
              omega
            · exact hΨ.size_lt x l hl'
          · intro x y lx ly hx hy hxy
            rcases hcases x lx hx with ⟨rfl, rfl⟩ | ⟨hxa, hx'⟩
            · rcases hcases y ly hy with ⟨rfl, -⟩ | ⟨-, hy'⟩
              · exact absurd rfl hxy
              · exact hR y ly.size (hΨ.size_lt y ly hy') (h.heapPerm y ly hy').1
            · rcases hcases y ly hy with ⟨rfl, rfl⟩ | ⟨-, hy'⟩
              · exact (hR x lx.size (hΨ.size_lt x lx hx') (h.heapPerm x lx hx').1).symm
              · exact hΨ.disjoint x y lx ly hx' hy' hxy
          · intro x l hl
            rcases hcases x l hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
            · show 0 < S.size + 0
              omega
            · exact hΨ.nonempty x l hl'
          · intro x l hl p hp
            rcases hcases x l hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
            · exact hin p hp
            · exact hΨ.fits x l hl' p hp
          · intro x l hl t ht
            rcases hcases x l hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
            · exact hkind t ht
            · exact hΨ.kinds x l hl' t ht
          · intro x l b hl hb
            rcases hcases x l hl with ⟨-, hlL⟩ | ⟨-, hl'⟩
            · rw [hlL] at hb; cases hb
            · exact hΨ.said x l b hl' hb
        -- what was accessible before is as it was
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
          rw [State.perm_mapZero s hal hsz4 hfit64]
          split
          · rfl
          · exact hy i hi
        have hrd : ∀ (y : BitVec 64) (m : Nat), s.canRead y m = true →
            (s.mapZero a size).canRead y m = true := by
          intro y m hy
          rw [State.canRead_iff] at hy ⊢
          intro i hi
          rw [State.perm_mapZero s hal hsz4 hfit64]
          split
          · rfl
          · exact hy i hi
        have hnew : (s.mapZero a size).canWrite a S.size = true := by
          rw [State.canWrite_iff]
          intro i hi
          rw [State.perm_mapZero s hal hsz4 hfit64]
          have : (a + BitVec.ofNat 64 i - a).toNat < size := by bv_omega
          simp only [this, ↓reduceIte]
          rfl
        have hg : ∀ r, (s.mapZero a size).getReg r = s.getReg r := fun _ => rfl
        have hb : stackBase Γ (s.mapZero a size) = stackBase Γ s := rfl
        have hM₀ : WellTyped fetch sys Ψ₂ n Γ (s.mapZero a size) :=
          { regs := fun r hr => by rw [hg]; exact (h.regs r hr).ext hext
            flags := h.flags
            stackPerm := by rw [hb]; exact hwr _ _ h.stackPerm
            stackBound := h.stackBound
            stackFits := h.stackFits
            stack := fun k S hk p hp => by
              have hw := h.canWrite_stack (lo := stackOff Γ.stack k + p.1) (m := 8) (h.stack_in hk hp)
              rw [hg, State.load64_mapZero_out s hal hsz4 hfit64 (hout _ (State.canRead_of_canWrite hw))]
              exact (h.stack k S hk p hp).ext hext
            heapPerm := fun x l hl => by
              rcases hcases x l hl with ⟨hx, hlL⟩ | ⟨-, hl'⟩
              · rw [hx, hlL]
                exact ⟨State.canRead_of_canWrite hnew, fun _ => hnew⟩
              · exact ⟨hrd _ _ (h.heapPerm x l hl').1, fun hw => hwr _ _ ((h.heapPerm x l hl').2 hw)⟩
            heap := fun x l hl p hp => by
              rcases hcases x l hl with ⟨hx, hlL⟩ | ⟨-, hl'⟩
              · rw [hlL] at hp
                have hpf : p.1 + 8 ≤ S.size := hin p hp
                have hin' : ∀ j : BitVec 64, j < 8 →
                    ((a + BitVec.ofNat 64 p.1 + j) - a).toNat < size := by
                  intro j hj
                  bv_omega
                rw [hx, State.load64_mapZero_in s hal hsz4 hfit64 hin']
                exact HasTy.zero (hzero p hp)
              · have hr := h.canRead_bytes hl' (hΨ.fits x l hl' p hp)
                rw [State.load64_mapZero_out s hal hsz4 hfit64 (hout _ hr)]
                exact (h.heap x l hl' p hp).ext hext
            stackHeap := fun x l hl => by
              rw [hb]
              rcases hcases x l hl with ⟨hx, hlL⟩ | ⟨-, hl'⟩
              · rw [hx, hlL]
                exact (hR (stackBase Γ s) (stackSize Γ) h.stackSize_lt
                  (State.canRead_of_canWrite h.stackPerm)).symm
              · exact h.stackHeap x l hl'
            sp := by rw [hg]; exact h.sp.ext hext
            owned :=
              { perm := fun b hb' => hwr _ _ (h.owned.perm b hb')
                size_lt := h.owned.size_lt
                fits := h.owned.fits
                vals := fun b hb' p hp => by
                  have hr := State.canRead_of_canWrite (State.canWrite_sub (h.owned.perm b hb')
                    (o := p.1) (m := 8) (h.owned.fits b hb' p hp))
                  rw [State.load64_mapZero_out s hal hsz4 hfit64 (hout _ hr)]
                  exact (h.owned.vals b hb' p hp).ext hext
                stack := fun b hb' => by rw [hb]; exact h.owned.stack b hb'
                heap := fun b hb' x l hl => by
                  rcases hcases x l hl with ⟨hx, hlL⟩ | ⟨-, hl'⟩
                  · rw [hx, hlL]
                    show Disjoint _ _ _ (S.size + 0)
                    exact (hR b.1 b.2.size (h.owned.size_lt b hb')
                      (State.canRead_of_canWrite (h.owned.perm b hb'))).symm
                  · exact h.owned.heap b hb' x l hl'
                apart := h.owned.apart }
            text := fun x l hl ht => by
              rcases hcases x l hl with ⟨-, hlL⟩ | ⟨-, hl'⟩
              · rw [hlL] at ht
                exact absurd rfl ht
              · -- the byte is readable, so it is not in the fresh memory
                have hpos := hΨ.nonempty x l hl'
                have hr := State.canRead_iff.mp (h.heapPerm x l hl').1 (l.size - 1) (by omega)
                rw [State.mem_mapZero s hal hsz4 hfit64]
                split
                · next hin =>
                  have hn := hU _ hin
                  rw [hn] at hr
                · exact h.text x l hl' ht
            said := fun x l b hl hb k hk => by
              rcases hcases x l hl with ⟨-, hlL⟩ | ⟨-, hl'⟩
              · rw [hlL] at hb; cases hb
              · -- the byte is readable, so it is not in the fresh memory
                have hlb := (hΨ.said x l b hl' hb).2
                have hr := State.canRead_iff.mp (h.heapPerm x l hl').1 k (by omega)
                rw [State.mem_mapZero s hal hsz4 hfit64]
                split
                · next hin =>
                  have hn := hU _ hin
                  rw [hn] at hr
                  exact absurd hr (by decide)
                · exact h.said x l b hl' hb k hk }
        have hM : WellTyped fetch sys Ψ₂ n Γ
            { s.mapZero a size with world := { s.world with asked := s.world.asked + 1 } } :=
          hM₀.congr rfl rfl rfl rfl
        exact ⟨Ψ₂, hext, hWF, ret_typed hM (hasTy_orErr.mpr (.inr (hτ Ψ₂ a hat)))⟩
      · exact herr _ _ (h.congr rfl rfl rfl rfl) (by decide)

namespace OnlyWorld

variable {t : State}

theorem ok {sys : Syscall} (hf : OnlyWorld s t) (h : WellTyped fetch sys Ψ n Γ s) :
    WellTyped fetch sys Ψ n Γ.afterSyscall t := by
  obtain ⟨v, w, rfl⟩ := hf
  exact ret_ok (h.congr (t := { s with world := w }) rfl rfl rfl rfl) v

end OnlyWorld

/-- Bytes stored in plain bytes of a writable block leave the state well
typed, whatever they are. -/
theorem storeBytes_ok {sys : Syscall} {r : Reg} {S : Shape} {off cnt : Nat}
    {data : List (BitVec 8)} (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hr : r ≠ .rsp)
    (hbuf : Γ.regs r = .ptr S true off) (hle : off + cnt ≤ S.size)
    (hfree : S.free off cnt = true) (hlen : data.length ≤ cnt) :
    WellTyped fetch sys Ψ n Γ (s.storeBytes (s.getReg r) data) := by
  have hp := h.regs r hr
  rw [hbuf] at hp
  obtain ⟨a, l, hl, rfl, hwr, hva⟩ := hasTy_ptr.mp hp
  have hsz := hΨ.size_lt a l hl
  simp only [Layout.size] at hsz
  rw [hva]
  refine h.writeHeapFree hΨ hl (hwr rfl) (lo := off) (cnt := cnt) hle hfree rfl rfl rfl
    (fun y hd => ?_) (fun x hx => ?_)
  · by_cases hc : cnt = 0
    · have hz : data = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hz, State.storeBytes_nil]
    · refine (State.load64_congr (s := s.storeBytes _ _) rfl y).trans
        (State.load64_storeBytes_disjoint s _ (by omega) ?_ (hd.2 (by omega)))
      have h1 := hd.1 (by decide)
      bv_omega
  · show (s.storeBytes _ data).mem x = s.mem x
    by_cases hc : cnt = 0
    · have hz : data = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hz, State.storeBytes_nil]
    · rw [State.mem_storeBytes s _ x _ (by omega), List.getElem?_eq_none (by bv_omega)]
      rfl

/-- Bytes stored in a run of bytes of a piece of the stack leave the state
well typed, whatever they are and whatever was there: the run is plain bytes
from then on. -/
theorem storeBytes_ok_stack {sys : Syscall} {r : Reg} {v d : BitVec 64} {k i cnt : Nat}
    {S : Shape} {data : List (BitVec 8)} (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hr : r ≠ .rsp) (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs r = .eq (v + d))
    (hat : StackAt Γ.stack k S d.toNat i) (hle : i + cnt ≤ S.size) (hlen : data.length ≤ cnt) :
    WellTyped fetch sys Ψ n { Γ with stack := Γ.stack.set k (S.clear i cnt) }
      (s.storeBytes (s.getReg r) data) := by
  obtain ⟨hk, hd⟩ := hat
  have hv : s.getReg .rsp = v := by
    have := h.sp
    rwa [hsp, hasTy_eq] at this
  have hend := stackOff_add_le hk
  have hsz := h.stackSize_lt
  simp only [stackSize] at hsz
  have hbase : v + d = s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + i) := by
    rw [hv, ← hd]; simp
  rw [h.eqReg hr hbuf, hbase]
  refine h.writeStackClear hΨ hk (i := i) (cnt := cnt) hle rfl rfl rfl
    (fun y hd => ?_) (fun x hx => ?_)
  · by_cases hc : cnt = 0
    · have hz : data = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hz, State.storeBytes_nil]
    · refine (State.load64_congr (s := s.storeBytes _ _) rfl y).trans
        (State.load64_storeBytes_disjoint s _ (by omega) ?_ (hd.2 (by omega)))
      have h1 := hd.1 (by decide)
      bv_omega
  · show (s.storeBytes _ data).mem x = s.mem x
    by_cases hc : cnt = 0
    · have hz : data = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hz, State.storeBytes_nil]
    · rw [State.mem_storeBytes s _ x _ (by omega), List.getElem?_eq_none (by bv_omega)]
      rfl

/-- Bytes stored in a run of bytes of an owned block leave the state well
typed, whatever they are and whatever was there: the run is plain bytes from
then on. -/
theorem storeBytes_ok_owned {sys : Syscall} {r : Reg} {k lo cnt : Nat} {a v : BitVec 64}
    {S : Shape} {data : List (BitVec 8)} (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hr : r ≠ .rsp) (hbuf : Γ.regs r = .eq v) (hat : OwnedByte Γ.owned k a S v lo)
    (hle : lo + cnt ≤ S.size) (hlen : data.length ≤ cnt) :
    WellTyped fetch sys Ψ n { Γ with owned := Γ.owned.set k (a, S.clear lo cnt) }
      (s.storeBytes (s.getReg r) data) := by
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hat.entry
  have hin : (a, S) ∈ Γ.owned := hkeq ▸ List.getElem_mem hklt
  have hsz := h.owned.size_lt _ hin
  simp only at hsz
  rw [h.eqReg hr hbuf, hat.addr]
  refine h.writeOwnedClear hΨ hat.entry (lo := lo) (cnt := cnt) hle rfl rfl rfl
    (fun y hd => ?_) (fun x hx => ?_)
  · by_cases hc : cnt = 0
    · have hz : data = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hz, State.storeBytes_nil]
    · refine (State.load64_congr (s := s.storeBytes _ _) rfl y).trans
        (State.load64_storeBytes_disjoint s _ (by omega) ?_ (hd.2 (by omega)))
      have h1 := hd.1 (by decide)
      bv_omega
  · show (s.storeBytes _ data).mem x = s.mem x
    by_cases hc : cnt = 0
    · have hz : data = [] := List.length_eq_zero_iff.mp (by omega)
      rw [hz, State.storeBytes_nil]
    · rw [State.mem_storeBytes s _ x _ (by omega), List.getElem?_eq_none (by bv_omega)]
      rfl

namespace Fills

variable {t : State} {r : Reg} {room : Nat}

/-- A call that fills a buffer lying in plain bytes of a writable block
keeps the state well typed. -/
theorem ok {sys : Syscall} {S : Shape} {off : Nat}
    (hf : Fills s (s.getReg r) room t) (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hr : r ≠ .rsp) (hbuf : Γ.regs r = .ptr S true off)
    (hle : off + room ≤ S.size) (hfree : S.free off room = true) :
    WellTyped fetch sys Ψ n Γ.afterSyscall t := by
  rcases hf with hf | ⟨data, v, w, hlen, -, rfl⟩
  · exact hf.ok h
  · exact ret_ok ((storeBytes_ok (data := data) h hΨ hr hbuf hle hfree (by omega)).congr
      (t := { s.storeBytes (s.getReg r) data with world := w }) rfl rfl rfl rfl) v

/-- A call that fills a buffer lying in a piece of the stack keeps the state
well typed, whatever the bytes it covers held: they are plain bytes
afterwards. -/
theorem ok_stack {sys : Syscall} {v d : BitVec 64} {k i : Nat} {S : Shape}
    (hf : Fills s (s.getReg r) room t) (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hr : r ≠ .rsp) (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs r = .eq (v + d))
    (hat : StackAt Γ.stack k S d.toNat i) (hle : i + room ≤ S.size) :
    WellTyped fetch sys Ψ n
      ({ Γ with stack := Γ.stack.set k (S.clear i room) } : Ctx).afterSyscall t := by
  rcases hf with hf | ⟨data, v', w, hlen, -, rfl⟩
  · -- nothing was stored: the bytes are as they were, and are given up as plain
    have h0 := storeBytes_ok_stack (data := []) h hΨ hr hsp hbuf hat hle (Nat.zero_le _)
    rw [State.storeBytes_nil] at h0
    exact hf.ok (h0.congr rfl rfl rfl rfl)
  · exact ret_ok
      ((storeBytes_ok_stack (data := data) h hΨ hr hsp hbuf hat hle hlen).congr
        (t := { s.storeBytes (s.getReg r) data with world := w }) rfl rfl rfl rfl) v'

/-- A call that fills a buffer lying in an owned block keeps the state well
typed, whatever the bytes it covers held: they are plain bytes afterwards. -/
theorem ok_owned {sys : Syscall} {k lo : Nat} {a v : BitVec 64} {S : Shape}
    (hf : Fills s (s.getReg r) room t) (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hr : r ≠ .rsp) (hbuf : Γ.regs r = .eq v) (hat : OwnedByte Γ.owned k a S v lo)
    (hle : lo + room ≤ S.size) :
    WellTyped fetch sys Ψ n
      ({ Γ with owned := Γ.owned.set k (a, S.clear lo room) } : Ctx).afterSyscall t := by
  rcases hf with hf | ⟨data, v', w, hlen, -, rfl⟩
  · -- nothing was stored: the bytes are as they were, and are given up as plain
    have h0 := storeBytes_ok_owned (data := []) h hΨ hr hbuf hat hle (Nat.zero_le _)
    rw [State.storeBytes_nil] at h0
    exact hf.ok (h0.congr rfl rfl rfl rfl)
  · exact ret_ok
      ((storeBytes_ok_owned (data := data) h hΨ hr hbuf hat hle hlen).congr
        (t := { s.storeBytes (s.getReg r) data with world := w }) rfl rfl rfl rfl) v'

end Fills

/-- Fresh memory appearing where nothing was accessible leaves a state well
typed as it was. -/
theorem mapZero_ok {sys : Syscall} {a : BitVec 64} {size : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hal : a.toNat % 4096 = 0) (hsz4 : size % 4096 = 0)
    (hfit : a.toNat + size ≤ addrTop)
    (hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none)
    (hpos : ∀ x l, Ψ x = some l → 0 < l.size)
    (hin : ∀ x l, Ψ x = some l → ∀ p ∈ l.shape.vals, p.1 + 8 ≤ l.shape.size)
    (hsd : ∀ x l (b : List (BitVec 8)), Ψ x = some l → l.said = some b →
      l.writable = false ∧ b.length = l.size) :
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
  have hg : ∀ r, (s.mapZero a size).getReg r = s.getReg r := fun _ => rfl
  have hb : stackBase Γ (s.mapZero a size) = stackBase Γ s := rfl
  exact {
    regs := fun r hr => by rw [hg]; exact h.regs r hr
    flags := h.flags
    stackPerm := by rw [hb]; exact hwr _ _ h.stackPerm
    stackBound := h.stackBound
    stackFits := h.stackFits
    stack := fun k S hk p hp => by
      have hw := h.canWrite_stack (lo := stackOff Γ.stack k + p.1) (m := 8) (h.stack_in hk hp)
      rw [hg, State.load64_mapZero_out s hal hsz4 hfit (hout _ (State.canRead_of_canWrite hw))]
      exact h.stack k S hk p hp
    heapPerm := fun x l hl =>
      ⟨hrd _ _ (h.heapPerm x l hl).1, fun hw => hwr _ _ ((h.heapPerm x l hl).2 hw)⟩
    heap := fun x l hl p hp => by
      have hr := h.canRead_bytes hl (hin x l hl p hp)
      rw [State.load64_mapZero_out s hal hsz4 hfit (hout _ hr)]
      exact h.heap x l hl p hp
    stackHeap := fun x l hl => by rw [hb]; exact h.stackHeap x l hl
    sp := by rw [hg]; exact h.sp
    owned :=
      { perm := fun b hb' => hwr _ _ (h.owned.perm b hb')
        size_lt := h.owned.size_lt
        fits := h.owned.fits
        vals := fun b hb' p hp => by
          have hr := State.canRead_of_canWrite (State.canWrite_sub (h.owned.perm b hb')
            (o := p.1) (m := 8) (h.owned.fits b hb' p hp))
          rw [State.load64_mapZero_out s hal hsz4 hfit (hout _ hr)]
          exact h.owned.vals b hb' p hp
        stack := fun b hb' => by rw [hb]; exact h.owned.stack b hb'
        heap := h.owned.heap
        apart := h.owned.apart }
    text := fun x l hl ht => by
      rw [State.mem_mapZero s hal hsz4 hfit]
      split
      · next hin =>
        -- the byte is readable, so it is not in the fresh memory
        have hr := State.canRead_iff.mp (h.heapPerm x l hl).1 (l.size - 1) (by
          have := hpos x l hl; omega)
        have hn := hU _ hin
        rw [hn] at hr
      · exact h.text x l hl ht
    said := fun x l b hl hb k hk => by
      have hlb := (hsd x l b hl hb).2
      rw [State.mem_mapZero s hal hsz4 hfit]
      split
      · next hin =>
        have hr := State.canRead_iff.mp (h.heapPerm x l hl).1 k (by omega)
        have hn := hU _ hin
        rw [hn] at hr
        exact absurd hr (by decide)
      · exact h.said x l b hl hb k hk }

/-- Fresh memory, found where nothing was accessible, may be owned as a block
of plain bytes. -/
theorem mapZero_owned {sys : Syscall} {a : BitVec 64} {size : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hal : a.toNat % 4096 = 0)
    (hsz4 : size % 4096 = 0) (hfit64 : a.toNat + size ≤ addrTop)
    (hlt : size < 2 ^ 64) (hun : s.unmapped a size = true) :
    WellTyped fetch sys Ψ n { Γ with owned := (a, ShapeOf.raw size) :: Γ.owned }
      (s.mapZero a size) := by
  have hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none :=
    fun x hx => perm_of_unmapped hal hfit64 hun hx
  have hZ := mapZero_ok h hal hsz4 hfit64 hU hΨ.nonempty hΨ.fits hΨ.said
  have hnew : (s.mapZero a size).canWrite a size = true := by
    rw [State.canWrite_iff]
    intro i hi
    rw [State.perm_mapZero s hal hsz4 hfit64]
    have : (a + BitVec.ofNat 64 i - a).toNat < size := by bv_omega
    simp only [this, ↓reduceIte]
    rfl
  refine hZ.addOwned (b := (a, ShapeOf.raw size)) hnew hlt (fun _ hp => nomatch hp)
    (fun _ hp => nomatch hp) ?_ ?_ ?_
  · exact (disjoint_of_unmapped hU (by omega) (Nat.le_refl _) h.stackSize_lt
      (State.canRead_of_canWrite h.stackPerm)).symm
  · intro x l hl
    exact disjoint_of_unmapped hU (by omega) (Nat.le_refl _) (hΨ.size_lt x l hl)
      (h.heapPerm x l hl).1
  · intro c hc'
    exact disjoint_of_unmapped hU (by omega) (Nat.le_refl _) (h.owned.size_lt c hc')
      (State.canRead_of_canWrite (h.owned.perm c hc'))

/-- What follows an `mmap` whose memory the program is to own: an error
number in `rax`, or the address of whole pages, zeroed, that the context now
owns as a block of plain bytes. The address is the start of a page and lies
where the kernel puts a program's memory, in the lower half of the address
space; so it is never an error number. -/
def mmapOwnCtx (Γ : Ctx) (len : BitVec 64) :
    ({ e : BitVec 64 // SysErr e } ⊕
      { a : BitVec 64 // a.toNat % 4096 = 0 ∧ a < 0x800000000000 }) → Ctx
  | .inl e => Γ.afterSyscall.setReg .rax (.eq e.1)
  | .inr a =>
    { Γ.afterSyscall.setReg .rax (.eq a.1) with
      owned := (a.1, ShapeOf.raw ((len.toNat + 4095) / 4096 * 4096)) :: Γ.owned }

/-- **Fresh memory may be owned.** An `mmap` in the modelled form returns an
error number, or the address of memory that was not accessible before, which
the context may then own. -/
theorem mmapOwn_ok {sys : Syscall} {len : BitVec 64}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22) :
    ∃ x, WellTyped fetch sys Ψ n (mmapOwnCtx Γ len x) (mmap s) := by
  have hsi := h.eqReg (by decide) hlen
  have hdx := h.eqReg (by decide) hprot
  have h10 := h.eqReg (by decide) hflags
  have herr : ∀ (t : State) (v : BitVec 64) (hv : SysErr v), WellTyped fetch sys Ψ n Γ t →
      ∃ x, WellTyped fetch sys Ψ n (mmapOwnCtx Γ len x) (ret t v) :=
    fun t v hv ht => ⟨.inl ⟨v, hv⟩, ret_typed ht (hasTy_eq.mpr rfl)⟩
  simp only [mmap, hsi, hdx, h10, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
  split
  · exact herr s _ (by decide) h
  · next hc =>
    split
    · exact herr _ _ (by decide) (h.congr rfl rfl rfl rfl)
    · next a _ =>
      split
      · next hok =>
        obtain ⟨hal, -, htop, hun⟩ := hok
        have hT : addrTop = 0x7ffffffff000 := rfl
        have hOwn := mapZero_owned h hΨ hal
          (size := (len.toNat + 4095) / 4096 * 4096) (by omega) (by omega) (by omega) hun
        have hlow : a < 0x800000000000 := by
          rw [BitVec.lt_def]
          show a.toNat < 0x800000000000
          omega
        exact ⟨.inr ⟨a, hal, hlow⟩, ret_typed
          (hOwn.congr (t := { s.mapZero a ((len.toNat + 4095) / 4096 * 4096) with
            world := { s.world with asked := s.world.asked + 1 } }) rfl rfl rfl rfl)
          (hasTy_eq.mpr rfl)⟩
      · exact herr _ _ (by decide) (h.congr rfl rfl rfl rfl)

/-- **Memory the program owns may be given back.** A `munmap` of exactly an
owned block leaves a state matching the context without it, whether or not
the kernel did as asked. -/
theorem munmap_ok {sys : Syscall} {k : Nat} {a len : BitVec 64} {S : Shape}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hdi : Γ.regs .rdi = .eq a) (hsi : Γ.regs .rsi = .eq len)
    (hk : Γ.owned[k]? = some (a, S))
    (hsz : S.size = (len.toNat + 4095) / 4096 * 4096) :
    WellTyped fetch sys Ψ n { Γ.afterSyscall with owned := Γ.owned.eraseIdx k } (munmap s) := by
  have hrdi := h.eqReg (by decide) hdi
  have hrsi := h.eqReg (by decide) hsi
  simp only [munmap, hrdi, hrsi]
  split
  · next hok =>
    obtain ⟨hal, -, htop, -⟩ := hok
    have hsz4 : (len.toNat + 4095) / 4096 * 4096 % 4096 = 0 := by omega
    rw [← hsz] at htop hsz4 ⊢
    have hT : addrTop = 0x7ffffffff000 := rfl
    have hfit : a.toNat + S.size ≤ addrTop := by omega
    exact ret_ok (h.eraseOwned hΨ hk (s' := s.unmap a (S.size)) rfl rfl rfl (fun x => by
      rw [State.perm_unmap s hal hsz4 hfit]
      split
      · next hin => exact .inr hin
      · exact .inl rfl)) _
  · exact ret_ok (h.eraseOwned hΨ hk rfl rfl rfl (fun _ => .inl rfl)) _

end Linux

/-- `exit`: with 60 in `rax`, the program ends. -/
theorem linux_exit (hΓ : Γ.regs .rax = .eq 60) : SysExits fetch linux Ψ Γ := by
  intro _ _ _ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨s.readReg .w32 .rdi, by simp [linux, hax]⟩

/-- `exit_group`: with 231 in `rax`, the program ends. -/
theorem linux_exit_group (hΓ : Γ.regs .rax = .eq 231) : SysExits fetch linux Ψ Γ := by
  intro _ _ _ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨s.readReg .w32 .rdi, by simp [linux, hax]⟩

/-- `exit`, where only a status satisfying `Q` is let through: with 60 in
`rax` and a status in `rdi` that is exactly known and satisfies `Q`, the
program ends. -/
theorem linux_exit_only {Q : BitVec 32 → Prop} {v : BitVec 64} (hΓ : Γ.regs .rax = .eq 60)
    (hd : Γ.regs .rdi = .eq v) (hQ : Q (v.setWidth 32)) :
    SysExits fetch (linux.exitsOnly Q) Ψ Γ := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hdi := h.eqReg (by decide) hd
  exact ⟨v.setWidth 32,
    Syscall.exitsOnly_exit (by simp [linux, hax, State.readReg, hdi]) hQ⟩

/-- `exit_group`, likewise. -/
theorem linux_exit_group_only {Q : BitVec 32 → Prop} {v : BitVec 64}
    (hΓ : Γ.regs .rax = .eq 231) (hd : Γ.regs .rdi = .eq v) (hQ : Q (v.setWidth 32)) :
    SysExits fetch (linux.exitsOnly Q) Ψ Γ := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hdi := h.eqReg (by decide) hd
  exact ⟨v.setWidth 32,
    Syscall.exitsOnly_exit (by simp [linux, hax, State.readReg, hdi]) hQ⟩

variable {sys : Syscall} [LikeLinuxNW sys]

/-- `write`: with 1 in `rax`, the call returns, whatever its arguments. A
buffer that cannot be read is refused by the kernel, not a fault. -/
theorem linux_write {sys : Syscall} [LikeLinux sys] (hΓ : Γ.regs .rax = .eq 1) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.write s, LikeLinux.next (by simp [linux, hax]), (Linux.write_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.write_only s).ok h⟩

/-- The bytes at an address inside a block that says its bytes are that
part of what it says. -/
theorem WellTyped.loadBytes_said {sys : Syscall} {base : BitVec 64} {l : Layout}
    {bs : List (BitVec 8)} {off cnt : Nat} (h : WellTyped fetch sys Ψ n Γ s)
    (hl : Ψ base = some l) (hs : l.said = some bs) (hin : off + cnt ≤ bs.length) :
    s.loadBytes (base + BitVec.ofNat 64 off) cnt = (bs.drop off).take cnt := by
  apply List.ext_getElem
  · simp only [State.loadBytes, List.length_map, List.length_range, List.length_take,
      List.length_drop]
    omega
  · intro k hk₁ hk₂
    simp only [State.loadBytes, List.length_map, List.length_range] at hk₁
    simp only [State.loadBytes, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    have := h.said base l bs hl hs (off + k) (by omega)
    rw [← this]
    congr 1
    bv_omega

/-- **`write`, where only what satisfies `R` is let through**: with 1 in
`rax`, the descriptor exactly known, and the buffer an exactly known place
in a block that says its bytes, as many of them as `rdx` exactly says, the
call returns if that part of what the block says satisfies `R`. -/
theorem linux_write_only {sys : Syscall} [LikeLinux sys]
    {R : BitVec 64 → List (BitVec 8) → Prop} {fd a cnt base : BitVec 64} {l : Layout}
    {bs : List (BitVec 8)} {off : Nat}
    (hΓ : Γ.regs .rax = .eq 1) (hfd : Γ.regs .rdi = .eq fd) (hbuf : Γ.regs .rsi = .eq a)
    (hcnt : Γ.regs .rdx = .eq cnt) (hl : Ψ base = some l) (hs : l.said = some bs)
    (ha : a = base + BitVec.ofNat 64 off) (hin : off + cnt.toNat ≤ bs.length)
    (hR : R fd ((bs.drop off).take cnt.toNat)) :
    SysReturns fetch (sys.writesOnly R) Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ he hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hdi := h.eqReg (by decide) hfd
  have hsi := h.eqReg (by decide) hbuf
  have hdx := h.eqReg (by decide) hcnt
  have hoff : s.offered = (bs.drop off).take cnt.toNat := by
    unfold State.offered
    rw [hsi, hdx, ha]
    exact h.loadBytes_said (he.blocks base l hl) hs hin
  have hgo : (sys.writesOnly R) s = sys s :=
    Syscall.writesOnly_eq (fun _ => by rw [hdi, hoff]; exact hR)
  exact ⟨Linux.write s, hgo.trans (LikeLinux.next (by simp [linux, hax])), (Linux.write_only s).rip,
    Ψ₁, .refl _, hΨ, (Linux.write_only s).ok h⟩

/-- A call that ends the program under some system ends it under that
system made to refuse unwanted writes: it is no `write`. -/
theorem linux_exit_writes {R : BitVec 64 → List (BitVec 8) → Prop} (hΓ : Γ.regs .rax = .eq 60) :
    SysExits fetch (linux.writesOnly R) Ψ Γ := by
  intro _ _ _ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨s.readReg .w32 .rdi, by
    rw [Syscall.writesOnly_eq (fun e => by rw [hax] at e; exact absurd e (by decide))]
    simp [linux, hax]⟩

theorem linux_exit_group_writes {R : BitVec 64 → List (BitVec 8) → Prop}
    (hΓ : Γ.regs .rax = .eq 231) : SysExits fetch (linux.writesOnly R) Ψ Γ := by
  intro _ _ _ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨s.readReg .w32 .rdi, by
    rw [Syscall.writesOnly_eq (fun e => by rw [hax] at e; exact absurd e (by decide))]
    simp [linux, hax]⟩

/-- `exit` where both what the program writes and what it ends with are
being shown: it is no `write`, and the status must be as wanted. -/
theorem linux_exit_only_writes {Q : BitVec 32 → Prop} {R : BitVec 64 → List (BitVec 8) → Prop}
    {v : BitVec 64} (hΓ : Γ.regs .rax = .eq 60) (hd : Γ.regs .rdi = .eq v)
    (hQ : Q (v.setWidth 32)) : SysExits fetch ((linux.exitsOnly Q).writesOnly R) Ψ Γ := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hdi := h.eqReg (by decide) hd
  exact ⟨v.setWidth 32, by
    rw [Syscall.writesOnly_eq (fun e => by rw [hax] at e; exact absurd e (by decide))]
    exact Syscall.exitsOnly_exit (by simp [linux, hax, State.readReg, hdi]) hQ⟩

theorem linux_exit_group_only_writes {Q : BitVec 32 → Prop}
    {R : BitVec 64 → List (BitVec 8) → Prop} {v : BitVec 64} (hΓ : Γ.regs .rax = .eq 231)
    (hd : Γ.regs .rdi = .eq v) (hQ : Q (v.setWidth 32)) :
    SysExits fetch ((linux.exitsOnly Q).writesOnly R) Ψ Γ := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hdi := h.eqReg (by decide) hd
  exact ⟨v.setWidth 32, by
    rw [Syscall.writesOnly_eq (fun e => by rw [hax] at e; exact absurd e (by decide))]
    exact Syscall.exitsOnly_exit (by simp [linux, hax, State.readReg, hdi]) hQ⟩

/-- `sys.EndsWhen E`: a call with 60 or 231 in `rax` ends the program, where
`E` holds of what is known of `rdi`: the value it holds exactly, if any. -/
def Syscall.EndsWhen (sys : Syscall) (E : Option (BitVec 64) → Prop) : Prop :=
  ∀ (fetch : Fetch) (Ψ : MemTy) (Γ : Ctx) (o : Option (BitVec 64)), E o →
    (Γ.regs .rax = .eq 60 ∨ Γ.regs .rax = .eq 231) → (∀ v, o = some v → Γ.regs .rdi = .eq v) →
    SysExits fetch sys Ψ Γ

/-- Any status will do. -/
def ExitAny : Option (BitVec 64) → Prop := fun _ => True

/-- The status must be exactly known, and as `Q` wants. -/
def ExitAs (Q : BitVec 32 → Prop) : Option (BitVec 64) → Prop :=
  fun o => ∃ v, o = some v ∧ Q (v.setWidth 32)

/-- No call is taken to end the program. -/
def ExitNever : Option (BitVec 64) → Prop := fun _ => False

theorem Syscall.endsWhen_never (sys : Syscall) : sys.EndsWhen ExitNever :=
  fun _ _ _ _ h => h.elim

theorem linux_endsWhen : linux.EndsWhen ExitAny :=
  fun _ _ _ _ _ hax _ => hax.elim (fun h => linux_exit h) (fun h => linux_exit_group h)

theorem linux_endsWhen_only (Q : BitVec 32 → Prop) : (linux.exitsOnly Q).EndsWhen (ExitAs Q) :=
  fun _ _ _ _ ⟨v, ho, hQ⟩ hax hd =>
    hax.elim (fun h => linux_exit_only h (hd v ho) hQ)
      (fun h => linux_exit_group_only h (hd v ho) hQ)

theorem linux_endsWhen_writes (R : BitVec 64 → List (BitVec 8) → Prop) :
    (linux.writesOnly R).EndsWhen ExitAny :=
  fun _ _ _ _ _ hax _ => hax.elim (fun h => linux_exit_writes h) (fun h => linux_exit_group_writes h)

theorem linux_endsWhen_only_writes (Q : BitVec 32 → Prop)
    (R : BitVec 64 → List (BitVec 8) → Prop) :
    ((linux.exitsOnly Q).writesOnly R).EndsWhen (ExitAs Q) :=
  fun _ _ _ _ ⟨v, ho, hQ⟩ hax hd =>
    hax.elim (fun h => linux_exit_only_writes h (hd v ho) hQ)
      (fun h => linux_exit_group_only_writes h (hd v ho) hQ)

/-- `openat`: with 257 in `rax`, the call returns, whatever its arguments. A
name that cannot be read is refused by the kernel, not a fault. -/
theorem linux_openat (hΓ : Γ.regs .rax = .eq 257) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.openat s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), (Linux.openat_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.openat_only s).ok h⟩

/-- `close`: with 3 in `rax`, the call returns, whatever its argument. -/
theorem linux_close (hΓ : Γ.regs .rax = .eq 3) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.close s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), (Linux.close_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.close_only s).ok h⟩

/-- `fsync`: with 74 in `rax`, the call returns, whatever its argument. -/
theorem linux_fsync (hΓ : Γ.regs .rax = .eq 74) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.fsync s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), (Linux.fsync_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.fsync_only s).ok h⟩

/-- `fdatasync`: with 75 in `rax`, likewise. -/
theorem linux_fdatasync (hΓ : Γ.regs .rax = .eq 75) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.fsync s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), (Linux.fsync_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.fsync_only s).ok h⟩

/-- `getpid`: with 39 in `rax`, the call returns. -/
theorem linux_getpid (hΓ : Γ.regs .rax = .eq 39) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.getpid s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), (Linux.getpid_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.getpid_only s).ok h⟩

/-- `lseek`: with 8 in `rax`, the call returns, whatever its arguments. -/
theorem linux_lseek (hΓ : Γ.regs .rax = .eq 8) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.lseek s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), (Linux.lseek_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.lseek_only s).ok h⟩

/-- `read`: with 0 in `rax`, the call returns, provided the buffer in `rsi`
points into a writable block and the `rdx` bytes from there are plain bytes
of it. Without that the kernel could overwrite a typed pointer. -/
theorem linux_read {S : Shape} {off : Nat} {len : BitVec 64} (hΓ : Γ.regs .rax = .eq 0)
    (hbuf : Γ.regs .rsi = .ptr S true off) (hlen : Γ.regs .rdx = .eq len)
    (hle : off + len.toNat ≤ S.size) (hfree : S.free off len.toNat = true) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.read_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.read s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok h hΨ (by decide) hbuf hle hfree⟩

/-- `read` into the stack: with 0 in `rax`, the call returns, provided the
stack pointer's value is known, the buffer in `rsi` is a known distance
above it, and the `rdx` bytes from there lie in one piece of the stack.
Whatever they held, they are plain bytes afterwards. -/
theorem linux_read_stack {v d len : BitVec 64} {k i : Nat} {S : Shape}
    (hΓ : Γ.regs .rax = .eq 0)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs .rsi = .eq (v + d))
    (hat : StackAt Γ.stack k S d.toNat i) (hlen : Γ.regs .rdx = .eq len)
    (hle : i + len.toNat ≤ S.size) :
    SysReturns fetch sys Ψ Γ
      ({ Γ with stack := Γ.stack.set k (S.clear i len.toNat) } : Ctx).afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.read_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.read s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_stack h hΨ (by decide) hsp hbuf hat hle⟩

/-- `fstat`: with 5 in `rax`, the call returns, provided the buffer in `rsi`
points into a writable block and the 144 bytes from there, which is what the
kernel stores, are plain bytes of it. -/
theorem linux_fstat {S : Shape} {off : Nat} (hΓ : Γ.regs .rax = .eq 5)
    (hbuf : Γ.regs .rsi = .ptr S true off)
    (hle : off + 144 ≤ S.size) (hfree : S.free off 144 = true) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.fstat_fills s
  exact ⟨Linux.fstat s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok h hΨ (by decide) hbuf hle hfree⟩

/-- `fstat` into the stack: as `linux_fstat`, with the buffer a known
distance above the stack pointer and its 144 bytes in one piece of the stack. -/
theorem linux_fstat_stack {v d : BitVec 64} {k i : Nat} {S : Shape}
    (hΓ : Γ.regs .rax = .eq 5)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs .rsi = .eq (v + d))
    (hat : StackAt Γ.stack k S d.toNat i) (hle : i + 144 ≤ S.size) :
    SysReturns fetch sys Ψ Γ
      ({ Γ with stack := Γ.stack.set k (S.clear i 144) } : Ctx).afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.fstat_fills s
  exact ⟨Linux.fstat s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_stack h hΨ (by decide) hsp hbuf hat hle⟩

/-- `clock_gettime`: with 228 in `rax`, the call returns, provided the buffer
in `rsi` points into a writable block and the 16 bytes from there are plain
bytes of it. -/
theorem linux_clock_gettime {S : Shape} {off : Nat} (hΓ : Γ.regs .rax = .eq 228)
    (hbuf : Γ.regs .rsi = .ptr S true off)
    (hle : off + 16 ≤ S.size) (hfree : S.free off 16 = true) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.clockGettime_fills s
  exact ⟨Linux.clockGettime s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok h hΨ (by decide) hbuf hle hfree⟩

/-- `clock_gettime` into the stack. -/
theorem linux_clock_gettime_stack {v d : BitVec 64} {k i : Nat} {S : Shape}
    (hΓ : Γ.regs .rax = .eq 228)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs .rsi = .eq (v + d))
    (hat : StackAt Γ.stack k S d.toNat i) (hle : i + 16 ≤ S.size) :
    SysReturns fetch sys Ψ Γ
      ({ Γ with stack := Γ.stack.set k (S.clear i 16) } : Ctx).afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.clockGettime_fills s
  exact ⟨Linux.clockGettime s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_stack h hΨ (by decide) hsp hbuf hat hle⟩

/-- `getrandom`: with 318 in `rax`, the call returns, provided the buffer in
`rdi` points into a writable block and the `rsi` bytes from there are plain
bytes of it. -/
theorem linux_getrandom {S : Shape} {off : Nat} {len : BitVec 64}
    (hΓ : Γ.regs .rax = .eq 318) (hbuf : Γ.regs .rdi = .ptr S true off)
    (hlen : Γ.regs .rsi = .eq len)
    (hle : off + len.toNat ≤ S.size) (hfree : S.free off len.toNat = true) :
    SysReturns fetch sys Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.getrandom_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.getrandom s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok h hΨ (by decide) hbuf hle hfree⟩

/-- `getrandom` into the stack. -/
theorem linux_getrandom_stack {v d len : BitVec 64} {k i : Nat} {S : Shape}
    (hΓ : Γ.regs .rax = .eq 318)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs .rdi = .eq (v + d))
    (hat : StackAt Γ.stack k S d.toNat i) (hlen : Γ.regs .rsi = .eq len)
    (hle : i + len.toNat ≤ S.size) :
    SysReturns fetch sys Ψ Γ
      ({ Γ with stack := Γ.stack.set k (S.clear i len.toNat) } : Ctx).afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.getrandom_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.getrandom s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_stack h hΨ (by decide) hsp hbuf hat hle⟩

/-- `read` into memory the program owns: the buffer lies inside an owned
block. Whatever the bytes it covers held, they are plain bytes afterwards. -/
theorem linux_read_owned {k lo : Nat} {a v : BitVec 64} {S : Shape} {len : BitVec 64}
    (hΓ : Γ.regs .rax = .eq 0) (hbuf : Γ.regs .rsi = .eq v)
    (hat : OwnedByte Γ.owned k a S v lo)
    (hlen : Γ.regs .rdx = .eq len)
    (hle : lo + len.toNat ≤ S.size) :
    SysReturns fetch sys Ψ Γ
      ({ Γ with owned := Γ.owned.set k (a, S.clear lo len.toNat) } : Ctx).afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.read_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.read s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_owned h hΨ (by decide) hbuf hat hle⟩

/-- `fstat` into memory the program owns: the buffer lies inside an owned
block. Whatever the bytes it covers held, they are plain bytes afterwards. -/
theorem linux_fstat_owned {k lo : Nat} {a v : BitVec 64} {S : Shape}
    (hΓ : Γ.regs .rax = .eq 5) (hbuf : Γ.regs .rsi = .eq v)
    (hat : OwnedByte Γ.owned k a S v lo)
    (hle : lo + 144 ≤ S.size) :
    SysReturns fetch sys Ψ Γ
      ({ Γ with owned := Γ.owned.set k (a, S.clear lo 144) } : Ctx).afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.fstat_fills s
  exact ⟨Linux.fstat s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_owned h hΨ (by decide) hbuf hat hle⟩

/-- `clock_gettime` into memory the program owns: the buffer lies inside an owned
block. Whatever the bytes it covers held, they are plain bytes afterwards. -/
theorem linux_clock_gettime_owned {k lo : Nat} {a v : BitVec 64} {S : Shape}
    (hΓ : Γ.regs .rax = .eq 228) (hbuf : Γ.regs .rsi = .eq v)
    (hat : OwnedByte Γ.owned k a S v lo)
    (hle : lo + 16 ≤ S.size) :
    SysReturns fetch sys Ψ Γ
      ({ Γ with owned := Γ.owned.set k (a, S.clear lo 16) } : Ctx).afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.clockGettime_fills s
  exact ⟨Linux.clockGettime s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_owned h hΨ (by decide) hbuf hat hle⟩

/-- `getrandom` into memory the program owns: the buffer lies inside an owned
block. Whatever the bytes it covers held, they are plain bytes afterwards. -/
theorem linux_getrandom_owned {k lo : Nat} {a v : BitVec 64} {S : Shape} {len : BitVec 64}
    (hΓ : Γ.regs .rax = .eq 318) (hbuf : Γ.regs .rdi = .eq v)
    (hat : OwnedByte Γ.owned k a S v lo)
    (hlen : Γ.regs .rsi = .eq len)
    (hle : lo + len.toNat ≤ S.size) :
    SysReturns fetch sys Ψ Γ
      ({ Γ with owned := Γ.owned.set k (a, S.clear lo len.toNat) } : Ctx).afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.getrandom_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.getrandom s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_owned h hΨ (by decide) hbuf hat hle⟩

/-- `mmap` for a block of a given shape: with 9 in `rax`, the length in
`rsi`, 3 in `rdx`, 0x22 in `r10` and zero in `rdi`, which leaves the place to
the kernel, the call returns an error number or a
writable pointer to a new block of that shape. The shape must fit in the
length and each of its typed values must admit zero, since that is what fresh
memory holds. -/
theorem linux_mmap {len : BitVec 64} {S : Shape} (hΓ : Γ.regs .rax = .eq 9)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22) (hhint : Γ.regs .rdi = .eq 0)
    (hfit : S.size ≤ len.toNat)
    (hne : 0 < S.size) (hin : S.fits = true)
    (hzero : S.vals.all (fun p => p.2.zeroOk) = true) :
    SysReturns fetch sys Ψ Γ (Γ.afterSyscall.setReg .rax (.orErr (.ptr S true 0))) := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  obtain ⟨Ψ₂, he₂, hΨ₂, hw⟩ := Linux.mmap_ok (tag := none) h hΨ hlen hprot hflags hfit hne
    (ShapeOf.fits_mem hin) (List.all_eq_true.mp hzero) (fun _ ht => nomatch ht)
    (fun Ψ₂ a hl => hasTy_ptr.mpr ⟨a, _, hl, rfl, fun _ => rfl, by
      show a = a + BitVec.ofNat 64 0
      simp⟩)
  have hdi := h.eqReg (by decide) hhint
  exact ⟨Linux.mmap s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax, hdi]), Linux.mmap_rip s, Ψ₂, he₂, hΨ₂, hw⟩

/-- `mmap` for a block of a declared kind: as `linux_mmap`, but the new
block is of kind `tag`, has that kind's shape, and the result is a pointer
to a block of that kind. This is how a record that points to others of its
kind is allocated. -/
theorem linux_mmap_kind {len : BitVec 64} {tag : Nat} {S : Shape}
    (hΓ : Γ.regs .rax = .eq 9) (hkind : Ψ.kinds tag = some S)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22) (hhint : Γ.regs .rdi = .eq 0)
    (hfit : S.size ≤ len.toNat)
    (hne : 0 < S.size) (hin : S.fits = true)
    (hzero : S.vals.all (fun p => p.2.zeroOk) = true) :
    SysReturns fetch sys Ψ Γ (Γ.afterSyscall.setReg .rax (.orErr (.ref tag true 0))) := by
  intro Ψ₁ he hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  obtain ⟨Ψ₂, he₂, hΨ₂, hw⟩ := Linux.mmap_ok (tag := some tag) h hΨ hlen hprot hflags hfit hne
    (ShapeOf.fits_mem hin) (List.all_eq_true.mp hzero)
    (fun t ht => by cases ht; rw [he.kinds]; exact hkind)
    (fun Ψ₂ a hl => hasTy_ref.mpr ⟨a, _, hl, rfl, fun _ => rfl, by
      show a = a + BitVec.ofNat 64 0
      simp⟩)
  have hdi := h.eqReg (by decide) hhint
  exact ⟨Linux.mmap s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax, hdi]), Linux.mmap_rip s, Ψ₂, he₂, hΨ₂, hw⟩

/-- `mmap` for memory the program is to own: with 9 in `rax`, the length in
`rsi`, 3 in `rdx` and 0x22 in `r10`, the call continues with an error number
in `rax`, or with the address of whole pages that the context now owns as a
block of integers. -/
theorem linux_mmap_own {next : BitVec 64} {len : BitVec 64} (hΓ : Γ.regs .rax = .eq 9)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22) (hhint : Γ.regs .rdi = .eq 0) :
    StepsTo fetch sys Ψ next Γ .syscall (Linux.mmapOwnCtx Γ len) := by
  intro Ψ₁ _ hΨ n s h _
  have hax := h.eqReg (by decide) hΓ
  obtain ⟨x, hw⟩ := Linux.mmapOwn_ok h hΨ hlen hprot hflags
  have hdi := h.eqReg (by decide) hhint
  exact ⟨Linux.mmap s, x, (LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax, hdi]) : sys s = _), Linux.mmap_rip s, Ψ₁,
    .refl _,
    hΨ, hw⟩

/-- `munmap` of a block the context owns: with 11 in `rax`, the block's
address in `rdi` and a length in `rsi` that covers exactly the block, the
call returns and the context no longer owns the block. -/
theorem linux_munmap {k : Nat} {a len : BitVec 64} {S : Shape} (hΓ : Γ.regs .rax = .eq 11)
    (hdi : Γ.regs .rdi = .eq a) (hsi : Γ.regs .rsi = .eq len)
    (hk : Γ.owned[k]? = some (a, S))
    (hsz : S.size = (len.toNat + 4095) / 4096 * 4096) :
    SysReturns fetch sys Ψ Γ { Γ.afterSyscall with owned := Γ.owned.eraseIdx k } := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.munmap s, LikeLinuxNW.next (by rw [hax]; decide) (by simp [linux, hax]), Linux.munmap_rip s, Ψ₁, .refl _, hΨ,
    Linux.munmap_ok h hΨ hdi hsi hk hsz⟩

end TypedAsm

