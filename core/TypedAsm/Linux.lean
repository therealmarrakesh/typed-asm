import TypedAsm.Soundness
import TypedAsm.Frame

/-!
# A small model of Linux

Four system calls: `exit`, `write`, `read` and `mmap`. Every other call
number is modelled as failing with `-ENOSYS`, but that is not what the real
kernel does with them, so the type system has no rule for them: a `syscall`
is typed only when the number in `rax` is exactly known and is one of the four.

What the model leaves out of the calls it does have:

* A `write` to a closed pipe raises a signal in the real kernel. Here it
  does not.
* Only file descriptors 0 (for `read`) and 1 and 2 (for `write`) exist.
* A `read` into memory that is not writable fails without consuming input.
  The real kernel may deliver part of the data first.

* `mmap` is modelled in one form only: fresh, private, zeroed memory that
  can be read and written (`PROT_READ|PROT_WRITE`,
  `MAP_PRIVATE|MAP_ANONYMOUS`), at an address the kernel chooses. Any other
  form is modelled as failing, which is not what the kernel does, so the
  type system types the call only in that form. Where the memory goes is the
  outside world's choice (`World.place`); all that is assumed of it is what
  the kernel guarantees: whole pages that were not accessible before.
* There is no `munmap`: memory, once given, is never taken back.

None of these changes what the types rely on: the call returns to the next
instruction, memory that was accessible is changed only inside the buffer of
a `read`, and `rcx`, `r11` and the flags hold values nothing is known about.
-/

namespace TypedAsm

namespace Linux

/-- The state a call returns in, with result `v`. Like the real kernel, a
returning call overwrites `rcx` and `r11` and leaves the flags unknown. -/
def ret (s : State) (v : BitVec 64) : State :=
  { ((s.setReg .rax v).setReg .rcx s.rip).setReg .r11 0 with flags := .unknown }

/-- `write(fd, buf, count)`: append bytes from `buf` to the output. The
world says how many of the `count` this call accepts; the result is that
number, and a program that wants everything written must go round again. -/
def write (s : State) : State :=
  let fd := s.getReg .rdi
  let buf := s.getReg .rsi
  let count := (s.getReg .rdx).toNat
  if fd ≠ 1 ∧ fd ≠ 2 then ret s (-9)
  else if s.canRead buf count then
    let n := match s.world.writeCaps with
      | [] => count
      | cap :: _ => min count cap
    ret { s with
        world := { s.world with
          writes := s.loadBytes buf n :: s.world.writes, writeCaps := s.world.writeCaps.tail } }
      (BitVec.ofNat 64 n)
  else ret s (-14)

/-- `read(fd, buf, count)`: take the next input event. Bytes are stored at
`buf`, at most `count` of them; what does not fit stays for the next call.
With no input left the call returns 0. -/
def read (s : State) : State :=
  let fd := s.getReg .rdi
  let buf := s.getReg .rsi
  let count := (s.getReg .rdx).toNat
  if fd ≠ 0 then ret s (-9)
  else if s.canWrite buf count then
    match s.world.input with
    | [] => ret s 0
    | .error e :: rest => ret { s with world := { s.world with input := rest } } e
    | .bytes data :: rest =>
      let chunk := data.take count
      let left := data.drop count
      ret { s.storeBytes buf chunk with
          world := { s.world with input := if left.isEmpty then rest else .bytes left :: rest } }
        (BitVec.ofNat 64 chunk.length)
  else ret s (-14)

/-- `mmap(addr, length, prot, flags, fd, offset)`, for fresh memory only:
`prot` must be 3 (read and write) and `flags` 0x22 (private, not backed by a
file). The kernel ignores `addr` and `fd` in this form, apart from treating
`addr` as a hint; `offset` must be a multiple of the page size. The length
is rounded up to whole pages. The world proposes where the memory goes; a
place that is not page-aligned, not within reach of a program, or not
entirely inaccessible beforehand is not one the kernel would choose, and the
call fails instead. On success the pages are readable, writable and zero,
and the result is their address. -/
def mmap (s : State) : State :=
  let len := (s.getReg .rsi).toNat
  let size := (len + 4095) / 4096 * 4096
  let w := { s.world with asked := s.world.asked + 1 }
  if s.getReg .rdx ≠ 3 ∨ s.getReg .r10 ≠ 0x22 then ret s (-22)
  else if len = 0 ∨ (s.getReg .r9).toNat % 4096 ≠ 0 then ret s (-22)
  else match s.world.place s.world.asked with
    | none => ret { s with world := w } (-12)
    | some a =>
      if a.toNat % 4096 = 0 ∧ 0 < a.toNat ∧ a.toNat + size ≤ 2 ^ 47 ∧
          s.unmapped a size = true then
        ret { s.mapZero a size with world := w } a
      else ret { s with world := w } (-12)

end Linux

/-- `exit` is call 60, `write` is 1, `read` is 0 and `mmap` is 9. -/
def linux : Syscall := fun s =>
  if s.getReg .rax = 60 then .exit (s.readReg .w32 .rdi)
  else if s.getReg .rax = 1 then .next (Linux.write s)
  else if s.getReg .rax = 0 then .next (Linux.read s)
  else if s.getReg .rax = 9 then .next (Linux.mmap s)
  else .next (Linux.ret s (-38))

/-- Whether zero is a value of the type, whatever the memory typing. Fresh
memory is all zero, so these are the types its fields may be given. -/
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

theorem write_ok {sys : Syscall} (h : WellTyped fetch sys Ψ n Γ s) :
    WellTyped fetch sys Ψ n Γ.afterSyscall (write s) := by
  simp only [write]
  split
  · exact ret_ok h _
  · split
    · exact ret_ok (by exact h.congr rfl rfl rfl rfl) _
    · exact ret_ok h _

theorem write_rip (s : State) : (write s).rip = s.rip := by
  simp only [write]
  split
  · rfl
  · split <;> rfl

theorem read_rip (s : State) : (read s).rip = s.rip := by
  simp only [read]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem ret_rax (s : State) (v : BitVec 64) : (ret s v).getReg .rax = v := by
  show (((s.setReg .rax v).setReg .rcx s.rip).setReg .r11 0).getReg .rax = v
  rw [State.getReg_setReg_other _ _ _ _ (by decide), State.getReg_setReg_other _ _ _ _ (by decide),
    State.getReg_setReg_same]

/-- Returning from a call with a result of a known type. -/
theorem ret_typed {sys : Syscall} {τ : Ty} {v : BitVec 64} (h : WellTyped fetch sys Ψ n Γ s)
    (hv : HasTy fetch sys Ψ n τ v) :
    WellTyped fetch sys Ψ n (Γ.afterSyscall.setReg .rax τ) (ret s v) :=
  (ret_ok h v).retype (by decide) (by rw [ret_rax]; exact hv)

theorem mmap_rip (s : State) : (mmap s).rip = s.rip := by
  simp only [mmap]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- A byte in a range found inaccessible is inaccessible. -/
theorem perm_of_unmapped {a : BitVec 64} {size : Nat} (hal : a.toNat % 4096 = 0)
    (hfit : a.toNat + size ≤ 2 ^ 64) (h : s.unmapped a size = true)
    {x : BitVec 64} (hx : (x - a).toNat < size) : s.perm x = .none := by
  have := (State.unmapped_iff hal hfit).mp h _ hx
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show a + (x - a) = x by bv_omega] at this

/-- **Fresh memory is a new block.** An `mmap` in the modelled form returns
an error number, or the address of memory that was not accessible before.
Nothing typed could point into such memory, so it may be given any layout
whose fields all admit zero, and the memory typing grows by that block; what
was well typed before still is. -/
theorem mmap_ok {sys : Syscall} {len : BitVec 64} {fields : List Ty} {tag : Option Nat} {τ : Ty}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22)
    (hfit : 8 * fields.length ≤ len.toNat) (hne : fields ≠ [])
    (hzero : ∀ υ ∈ fields, υ.zeroOk = true)
    (hkind : ∀ t, tag = some t → Ψ.kinds t = some fields)
    (hτ : ∀ (Ψ₂ : MemTy) (a : BitVec 64), Ψ₂ a = some ⟨fields, true, tag⟩ →
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
        have hfit64 : a.toNat + size ≤ 2 ^ 64 := by omega
        have hsz : len.toNat ≤ size := by omega
        have hpos : 0 < size := by omega
        have hsz64 : size < 2 ^ 64 := by omega
        have hk0 : 0 < fields.length := List.length_pos_iff.mpr hne
        have hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none :=
          fun x hx => perm_of_unmapped hal hfit64 hun hx
        -- nothing readable overlaps the new block
        have hR : ∀ (b : BitVec 64) (m : Nat), m < 2 ^ 64 → s.canRead b m = true →
            Disjoint a (8 * fields.length) b m := by
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
            have hr := State.canRead_iff.mp (h.heapPerm a l hl).1 0 (by
              have := List.length_pos_iff.mpr (hΨ.nonempty a l hl)
              simp only [Layout.size]; omega)
            rw [show a + BitVec.ofNat 64 0 = a by simp, hU a (by simpa using hpos)] at hr
            exact absurd hr (by decide)
        let L : Layout := ⟨fields, true, tag⟩
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
            · show 8 * fields.length < 2 ^ 64
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
            · exact hne
            · exact hΨ.nonempty x l hl'
          · intro x l hl t ht
            rcases hcases x l hl with ⟨-, rfl⟩ | ⟨-, hl'⟩
            · exact hkind t ht
            · exact hΨ.kinds x l hl' t ht
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
        have hnew : (s.mapZero a size).canWrite a (8 * fields.length) = true := by
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
            stackSize_lt := h.stackSize_lt
            stack := fun i υ hi => by
              have hw := h.canWrite_slot (i := i) (List.getElem?_eq_some_iff.mp hi).1
              rw [hg, State.load64_mapZero_out s hal hsz4 hfit64 (hout _ (State.canRead_of_canWrite hw))]
              exact (h.stack i υ hi).ext hext
            heapPerm := fun x l hl => by
              rcases hcases x l hl with ⟨hx, hlL⟩ | ⟨-, hl'⟩
              · rw [hx, hlL]
                exact ⟨State.canRead_of_canWrite hnew, fun _ => hnew⟩
              · exact ⟨hrd _ _ (h.heapPerm x l hl').1, fun hw => hwr _ _ ((h.heapPerm x l hl').2 hw)⟩
            heap := fun x l hl i υ hi => by
              rcases hcases x l hl with ⟨hx, hlL⟩ | ⟨-, hl'⟩
              · rw [hlL] at hi
                have hi' : i < fields.length := (List.getElem?_eq_some_iff.mp hi).1
                have hin : ∀ j : BitVec 64, j < 8 →
                    ((a + BitVec.ofNat 64 (8 * i) + j) - a).toNat < size := by
                  intro j hj
                  bv_omega
                rw [hx, State.load64_mapZero_in s hal hsz4 hfit64 hin]
                exact HasTy.zero (hzero υ (List.mem_of_getElem? hi))
              · have hr := h.canRead_field hl' (List.getElem?_eq_some_iff.mp hi).1
                rw [State.load64_mapZero_out s hal hsz4 hfit64 (hout _ hr)]
                exact (h.heap x l hl' i υ hi).ext hext
            stackHeap := fun x l hl => by
              rw [hb]
              rcases hcases x l hl with ⟨hx, hlL⟩ | ⟨-, hl'⟩
              · rw [hx, hlL]
                exact (hR (stackBase Γ s) (stackSize Γ) h.stackSize_lt
                  (State.canRead_of_canWrite h.stackPerm)).symm
              · exact h.stackHeap x l hl'
            sp := by rw [hg]; exact h.sp.ext hext }
        have hM : WellTyped fetch sys Ψ₂ n Γ
            { s.mapZero a size with world := { s.world with asked := s.world.asked + 1 } } :=
          hM₀.congr rfl rfl rfl rfl
        exact ⟨Ψ₂, hext, hWF, ret_typed hM (hasTy_orErr.mpr (.inr (hτ Ψ₂ a hat)))⟩
      · exact herr _ _ (h.congr rfl rfl rfl rfl) (by decide)

/-- A `read` into a buffer that lies in integer fields of a writable block
keeps the state well typed, whatever arrives. -/
theorem read_ok {sys : Syscall} {fields : List Ty} {off : Nat} {len : BitVec 64}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hbuf : Γ.regs .rsi = .ptr fields true off)
    (hlen : Γ.regs .rdx = .eq len)
    (hints : ∀ j, j < (len.toNat + 7) / 8 → fields[off + j]? = some .int) :
    WellTyped fetch sys Ψ n Γ.afterSyscall (read s) := by
  have hp := h.regs .rsi (by decide)
  rw [hbuf] at hp
  obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
  have hdx := h.eqReg (by decide) hlen
  simp only [read]
  split
  · exact ret_ok h _
  · split
    · split
      · exact ret_ok h _
      · exact ret_ok (by exact h.congr rfl rfl rfl rfl) _
      · next data rest _ =>
        refine ret_ok ?_ _
        rw [hdx, hva]
        by_cases hc : (len.toNat + 7) / 8 = 0
        · -- nothing is asked for, so nothing is stored
          have hz : len.toNat = 0 := by omega
          rw [hz, List.take_zero, State.storeBytes_nil]
          exact h.congr rfl rfl rfl rfl
        · have hlast := hints ((len.toNat + 7) / 8 - 1) (by omega)
          have hle : off + (len.toNat + 7) / 8 ≤ l.fields.length := by
            have := (List.getElem?_eq_some_iff.mp hlast).1
            omega
          have hsz := hΨ.size_lt a l hl
          simp only [Layout.size] at hsz
          refine h.writeInts hΨ hl (lo := off) (cnt := (len.toNat + 7) / 8) (by omega) hle
            (fun j hj hj' => by
              have := hints (j - off) (by omega)
              rwa [show off + (j - off) = j by omega] at this)
            rfl rfl rfl (fun y hd => ?_)
          have htake : (data.take len.toNat).length ≤ len.toNat := by
            simp only [List.length_take]; omega
          refine (State.load64_congr (s := s.storeBytes _ _) rfl y).trans
            (State.load64_storeBytes_disjoint s _ (by omega) ?_ (hd.2 (by omega)))
          have h1 := hd.1 (by decide)
          bv_omega
    · exact ret_ok h _

/-- A `read` into a buffer that lies in integer stack slots keeps the state
well typed, whatever arrives. -/
theorem read_ok_stack {sys : Syscall} {v d len : BitVec 64}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hsp : Γ.regs .rsp = .eq v)
    (hbuf : Γ.regs .rsi = .eq (v + d)) (h8 : d.toNat % 8 = 0) (hlen : Γ.regs .rdx = .eq len)
    (hints : ∀ j, j < (len.toNat + 7) / 8 → Γ.stack[d.toNat / 8 + j]? = some .int) :
    WellTyped fetch sys Ψ n Γ.afterSyscall (read s) := by
  have hv : s.getReg .rsp = v := by
    have := h.sp
    rwa [hsp, hasTy_eq] at this
  have hsi := h.eqReg (by decide) hbuf
  have hdx := h.eqReg (by decide) hlen
  have hbase : v + d = s.getReg .rsp + BitVec.ofNat 64 (8 * (d.toNat / 8)) := by
    rw [hv]; congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  simp only [read]
  split
  · exact ret_ok h _
  · split
    · split
      · exact ret_ok h _
      · exact ret_ok (by exact h.congr rfl rfl rfl rfl) _
      · next data rest _ =>
        refine ret_ok ?_ _
        rw [hdx, hsi]
        by_cases hc : (len.toNat + 7) / 8 = 0
        · have hz : len.toNat = 0 := by omega
          rw [hz, List.take_zero, State.storeBytes_nil]
          exact h.congr rfl rfl rfl rfl
        · have hlast := hints ((len.toNat + 7) / 8 - 1) (by omega)
          have hle : d.toNat / 8 + (len.toNat + 7) / 8 ≤ Γ.stack.length := by
            have := (List.getElem?_eq_some_iff.mp hlast).1
            omega
          have hsz := h.stackSize_lt
          simp only [stackSize] at hsz
          refine h.writeSlotsInt hΨ (lo := d.toNat / 8) (cnt := (len.toNat + 7) / 8) (by omega) hle
            (fun j hj hj' => by
              have := hints (j - d.toNat / 8) (by omega)
              rwa [show d.toNat / 8 + (j - d.toNat / 8) = j by omega] at this)
            rfl rfl rfl (fun y hd => ?_)
          have htake : (data.take len.toNat).length ≤ len.toNat := by
            simp only [List.length_take]; omega
          rw [hbase]
          refine (State.load64_congr (s := s.storeBytes _ _) rfl y).trans
            (State.load64_storeBytes_disjoint s _ (by omega) ?_ (hd.2 (by omega)))
          have h1 := hd.1 (by decide)
          bv_omega
    · exact ret_ok h _

end Linux

/-! ## The three calls, as the type system sees them -/

/-- `exit`: with 60 in `rax`, the program ends. -/
theorem linux_exit (hΓ : Γ.regs .rax = .eq 60) : SysExits fetch linux Ψ Γ := by
  intro _ _ _ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨s.readReg .w32 .rdi, by simp [linux, hax]⟩

/-- `write`: with 1 in `rax`, the call returns, whatever its arguments. A
buffer that cannot be read is refused by the kernel, not a fault. -/
theorem linux_write (hΓ : Γ.regs .rax = .eq 1) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  refine ⟨Linux.write s, ?_, Linux.write_rip s, Ψ₁, .refl _, hΨ, Linux.write_ok h⟩
  simp [linux, hax]

/-- `read`: with 0 in `rax`, the call returns, provided the buffer in `rsi`
points into a writable block and the `rdx` bytes from there are all in
integer fields. Without that the kernel could overwrite a typed pointer. -/
theorem linux_read {fields : List Ty} {off : Nat} {len : BitVec 64} (hΓ : Γ.regs .rax = .eq 0)
    (hbuf : Γ.regs .rsi = .ptr fields true off) (hlen : Γ.regs .rdx = .eq len)
    (hints : ∀ j, j < (len.toNat + 7) / 8 → fields[off + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  refine ⟨Linux.read s, ?_, Linux.read_rip s, Ψ₁, .refl _, hΨ,
    Linux.read_ok h hΨ hbuf hlen hints⟩
  simp [linux, hax]

/-- Whether a type is the integer type. -/
def Ty.isInt : Ty → Bool
  | .int => true
  | _ => false

/-- The condition of `linux_read` on the fields, from a check that can be
computed when the fields and the count are known. -/
theorem ints_of_check {fields : List Ty} {off k : Nat}
    (h : (List.range k).all (fun j => (fields[off + j]?).elim false Ty.isInt) = true) :
    ∀ j, j < k → fields[off + j]? = some .int := by
  intro j hj
  have hj' := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  cases hf : fields[off + j]? with
  | none => rw [hf] at hj'; exact absurd hj' (by simp)
  | some τ =>
    rw [hf] at hj'
    cases τ <;> first | rfl | exact absurd hj' (by simp [Ty.isInt])

/-- `read` into the stack: with 0 in `rax`, the call returns, provided the
stack pointer's value is known, the buffer in `rsi` is a known distance
above it, and the `rdx` bytes from there are all in integer stack slots. -/
theorem linux_read_stack {v d len : BitVec 64} (hΓ : Γ.regs .rax = .eq 0)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs .rsi = .eq (v + d)) (h8 : d.toNat % 8 = 0)
    (hlen : Γ.regs .rdx = .eq len)
    (hints : ∀ j, j < (len.toNat + 7) / 8 → Γ.stack[d.toNat / 8 + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  refine ⟨Linux.read s, ?_, Linux.read_rip s, Ψ₁, .refl _, hΨ,
    Linux.read_ok_stack h hΨ hsp hbuf h8 hlen hints⟩
  simp [linux, hax]

/-- `mmap` for a block of plain fields: with 9 in `rax`, the length in `rsi`,
3 in `rdx` and 0x22 in `r10`, the call returns an error number or a writable
pointer to a new block with the fields asked for. The fields must fit in the
length and each must admit zero, since that is what fresh memory holds. -/
theorem linux_mmap {len : BitVec 64} {fields : List Ty} (hΓ : Γ.regs .rax = .eq 9)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22) (hfit : 8 * fields.length ≤ len.toNat)
    (hne : fields ≠ []) (hzero : fields.all Ty.zeroOk = true) :
    SysReturns fetch linux Ψ Γ (Γ.afterSyscall.setReg .rax (.orErr (.ptr fields true 0))) := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  obtain ⟨Ψ₂, he₂, hΨ₂, hw⟩ := Linux.mmap_ok (tag := none) h hΨ hlen hprot hflags hfit hne
    (List.all_eq_true.mp hzero) (fun _ ht => nomatch ht)
    (fun Ψ₂ a hl => hasTy_ptr.mpr ⟨a, _, hl, rfl, fun _ => rfl, by
      show a = a + BitVec.ofNat 64 (8 * 0)
      simp⟩)
  exact ⟨Linux.mmap s, by simp [linux, hax], Linux.mmap_rip s, Ψ₂, he₂, hΨ₂, hw⟩

/-- `mmap` for a block of a declared kind: as `linux_mmap`, but the new
block is of kind `tag`, has that kind's fields, and the result is a pointer
to a block of that kind. This is how a record that points to others of its
kind is allocated. -/
theorem linux_mmap_kind {len : BitVec 64} {tag : Nat} {fields : List Ty}
    (hΓ : Γ.regs .rax = .eq 9) (hkind : Ψ.kinds tag = some fields)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22) (hfit : 8 * fields.length ≤ len.toNat)
    (hne : fields ≠ []) (hzero : fields.all Ty.zeroOk = true) :
    SysReturns fetch linux Ψ Γ (Γ.afterSyscall.setReg .rax (.orErr (.ref tag true 0))) := by
  intro Ψ₁ he hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  obtain ⟨Ψ₂, he₂, hΨ₂, hw⟩ := Linux.mmap_ok (tag := some tag) h hΨ hlen hprot hflags hfit hne
    (List.all_eq_true.mp hzero) (fun t ht => by cases ht; rw [he.kinds]; exact hkind)
    (fun Ψ₂ a hl => hasTy_ref.mpr ⟨a, _, hl, rfl, fun _ => rfl, by
      show a = a + BitVec.ofNat 64 (8 * 0)
      simp⟩)
  exact ⟨Linux.mmap s, by simp [linux, hax], Linux.mmap_rip s, Ψ₂, he₂, hΨ₂, hw⟩

/-! ## Memory the program cannot write stays as it was -/

/-- No system call changes the permission of an accessible byte, or an
accessible byte that is not writable. -/
theorem linux_frame (s : State) : (linux s).All (Frame s) := by
  unfold linux
  split
  · trivial
  · split
    · show Frame s (Linux.write s)
      simp only [Linux.write]
      split
      · exact Frame.of_eq rfl rfl
      · split <;> exact Frame.of_eq rfl rfl
    · split
      · show Frame s (Linux.read s)
        simp only [Linux.read]
        split
        · exact Frame.of_eq rfl rfl
        · split
          · next hw =>
            split
            · exact Frame.of_eq rfl rfl
            · exact Frame.of_eq rfl rfl
            · next data rest _ =>
              refine .of_perm rfl (fun x hx => ?_)
              show (s.storeBytes _ _).mem x = s.mem x
              have hlen : (data.take (s.getReg .rdx).toNat).length ≤ 2 ^ 64 := by
                have := (s.getReg .rdx).isLt
                simp only [List.length_take]; omega
              rw [State.mem_storeBytes s _ x _ hlen]
              by_cases hin : (x - s.getReg .rsi).toNat < (data.take (s.getReg .rdx).toNat).length
              · -- a byte inside the buffer is writable, so it is not one of these
                rw [State.canWrite_iff] at hw
                have hlt : (x - s.getReg .rsi).toNat < (s.getReg .rdx).toNat := by
                  simp only [List.length_take] at hin; omega
                have := hw _ hlt
                rw [show s.getReg .rsi + BitVec.ofNat 64 (x - s.getReg .rsi).toNat = x by
                  bv_omega] at this
                rw [this] at hx
                cases hx
              · rw [List.getElem?_eq_none (by omega)]
                rfl
          · exact Frame.of_eq rfl rfl
      · split
        · show Frame s (Linux.mmap s)
          simp only [Linux.mmap]
          split
          · exact Frame.of_eq rfl rfl
          · split
            · exact Frame.of_eq rfl rfl
            · split
              · exact Frame.of_eq rfl rfl
              · split
                · next a _ hok =>
                  -- only bytes that were not accessible change
                  obtain ⟨hal, -, htop, hun⟩ := hok
                  have hsz4 : ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 % 4096 = 0 := by omega
                  generalize ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 = size at htop hun hsz4 ⊢
                  have hfit64 : a.toNat + size ≤ 2 ^ 64 := by omega
                  refine ⟨fun x hx => ?_, fun x hx _ => ?_⟩
                  · show (s.mapZero a size).perm x = s.perm x
                    rw [State.perm_mapZero s hal hsz4 hfit64]
                    split
                    · next hin => exact absurd (Linux.perm_of_unmapped hal hfit64 hun hin) hx
                    · rfl
                  · show (s.mapZero a size).mem x = s.mem x
                    rw [State.mem_mapZero s hal hsz4 hfit64]
                    split
                    · next hin => exact absurd (Linux.perm_of_unmapped hal hfit64 hun hin) hx
                    · rfl
                · exact Frame.of_eq rfl rfl
        · exact Frame.of_eq rfl rfl

end TypedAsm
