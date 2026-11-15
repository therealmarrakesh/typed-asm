import TypedAsm.Soundness
import TypedAsm.Frame

/-!
# A small model of Linux

The system calls a program can be typed to make: `exit` and `exit_group`,
`read`, `write`, `openat`, `close`, `lseek`, `fstat`, `mmap`, `munmap`,
`clock_gettime` and `getrandom`. Every other call number is modelled as
failing with `-ENOSYS`, but that is not what the real kernel does with them,
so the type system has no rule for them: a `syscall` is typed only when the
number in `rax` is exactly known and is one of these.

What the types rely on is the same for every one of them, and is true of
the real kernel whatever the arguments: the call returns to the next
instruction (or ends the program), memory that was accessible is changed
only inside a buffer the call was handed, and `rax`, `rcx`, `r11` and the
flags hold values nothing is known about. What a call *answers* is the
outside world's business, and nothing is proved from it.

What the model leaves out, none of which touches the above:

* A `write` to a closed pipe raises a signal in the real kernel. Here it
  does not.
* A `read` into memory that is not writable fails without consuming input.
  The real kernel may deliver part of the data first.
* There are no directories. A file is found by its whole name, spelled
  exactly as in `World.files`, and a relative name needs `AT_FDCWD`.
* `openat` understands the access mode and `O_CREAT`, `O_EXCL`, `O_TRUNC`
  and `O_APPEND`; other flags are ignored. Permissions are two switches per
  file, not owners and modes.
* The standard streams are not files: they cannot be sought, and `fstat`
  describes them as pipes. `fstat` fills in the kind, the size and the block
  counts; every field the model does not track is zero.
* Every clock tells the same time, the one the world supplies.
* `mmap` is modelled in one form only: fresh, private, zeroed memory that
  can be read and written (`PROT_READ|PROT_WRITE`,
  `MAP_PRIVATE|MAP_ANONYMOUS`), at an address the kernel chooses. Any other
  form is modelled as failing, which is not what the kernel does, so the
  type system types the call only in that form: this is the one call whose
  answer the types do rely on. Where the memory goes is the outside world's
  choice (`World.place`); all that is assumed of it is what the kernel
  guarantees: whole pages that were not accessible before.
* `munmap` gives back only memory that is writable; see `Linux.munmap`.
-/

namespace TypedAsm

namespace Linux

/-- The state a call returns in, with result `v`. Like the real kernel, a
returning call overwrites `rcx` and `r11` and leaves the flags unknown. -/
def ret (s : State) (v : BitVec 64) : State :=
  { ((s.setReg .rax v).setReg .rcx s.rip).setReg .r11 0 with flags := .unknown }

/-- The state a call returns in after storing `data` at `buf`, with result
`v` and the world as `w`. -/
def give (s : State) (buf : BitVec 64) (data : List (BitVec 8)) (v : BitVec 64) (w : World) :
    State :=
  ret { s.storeBytes buf data with world := w } v

/-- The file descriptor in a register. The kernel takes an `int`, which is
the low half of the register. -/
def fdArg (s : State) (r : Reg) : Nat :=
  ((s.getReg r).setWidth 32).toNat

/-- How many of `count` bytes the next `write` accepts. -/
def accepted (w : World) (count : Nat) : Nat :=
  match w.writeCaps with
  | [] => count
  | cap :: _ => min count cap

/-- `write(fd, buf, count)`: append bytes from `buf` to the output, or store
them in a file at the descriptor's position. The world says how many of the
`count` this call accepts; the result is that number, and a program that
wants everything written must go round again. -/
def write (s : State) : State :=
  let fd := fdArg s .rdi
  let buf := s.getReg .rsi
  let count := (s.getReg .rdx).toNat
  match s.world.fd? fd with
  | some .stdout =>
    if s.canRead buf count then
      let n := accepted s.world count
      ret { s with
          world := { s.world with
            writes := s.loadBytes buf n :: s.world.writes, writeCaps := s.world.writeCaps.tail } }
        (BitVec.ofNat 64 n)
    else ret s (-14)
  | some (.file i pos r w app) =>
    if !w then ret s (-9)
    else if s.canRead buf count then
      match s.world.files[i]? with
      | none => ret s (-9)
      | some f =>
        let n := accepted s.world count
        let start := if app then f.size else pos
        ret { s with
            world := { s.world.setFd fd (.file i (start + n) r w app) with
              files := s.world.files.setIfInBounds i (f.write start (s.loadBytes buf n))
              writeCaps := s.world.writeCaps.tail } }
          (BitVec.ofNat 64 n)
    else ret s (-14)
  | _ => ret s (-9)

/-- `read(fd, buf, count)`. From the program's input: take the next input
event; bytes are stored at `buf`, at most `count` of them, and what does not
fit stays for the next call; with no input left the call returns 0. From a
file: the bytes at the descriptor's position, up to the end of the file. -/
def read (s : State) : State :=
  let fd := fdArg s .rdi
  let buf := s.getReg .rsi
  let count := (s.getReg .rdx).toNat
  match s.world.fd? fd with
  | some .stdin =>
    if s.canWrite buf count then
      match s.world.input with
      | [] => ret s 0
      | .error e :: rest => ret { s with world := { s.world with input := rest } } e
      | .bytes data :: rest =>
        let chunk := data.take count
        let left := data.drop count
        give s buf chunk (BitVec.ofNat 64 chunk.length)
          { s.world with input := if left.isEmpty then rest else .bytes left :: rest }
    else ret s (-14)
  | some (.file i pos r w app) =>
    if !r then ret s (-9)
    else if s.canWrite buf count then
      match s.world.files[i]? with
      | none => ret s (-9)
      | some f =>
        let data := (f.read pos count).take count
        give s buf data (BitVec.ofNat 64 data.length)
          (s.world.setFd fd (.file i (pos + data.length) r w app))
    else ret s (-14)
  | _ => ret s (-9)

/-- The bytes of a zero-terminated string at `a`, without the zero: a name
as a program hands it to the kernel. It fails if a byte cannot be read, or
if no zero comes within `fuel` bytes. -/
def cstring (s : State) : Nat → BitVec 64 → Except (BitVec 64) (List (BitVec 8))
  | 0, _ => .error (-36)
  | fuel + 1, a =>
    if (s.perm a).readable then
      let b := s.mem a
      if b = 0 then .ok [] else (cstring s fuel (a + 1)).map (b :: ·)
    else .error (-14)

/-- `openat(dirfd, path, flags, mode)`: open the file with that name, making
it first if `O_CREAT` asks and there is none. The result is the lowest
descriptor not in use. -/
def openat (s : State) : State :=
  match cstring s 4096 (s.getReg .rsi) with
  | .error e => ret s e
  | .ok path =>
    let flags := ((s.getReg .rdx).setWidth 32).toNat
    let access := flags % 4
    let creat := flags / 0x40 % 2 == 1
    let excl := flags / 0x80 % 2 == 1
    let trunc := flags / 0x200 % 2 == 1
    let app := flags / 0x400 % 2 == 1
    let r := access != 1
    let w := access != 0
    let fd := s.world.freeFd
    if access == 3 then ret s (-22)
    else if path.isEmpty then ret s (-2)
    else if path.head? != some 0x2f && (s.getReg .rdi).setWidth 32 != (-100 : BitVec 32) then
      ret s (-9)
    else
      match s.world.find? path with
      | some i =>
        match s.world.files[i]? with
        | none => ret s (-2)
        | some f =>
          if creat && excl then ret s (-17)
          else if (r && !f.mayRead) || (w && !f.mayWrite) then ret s (-13)
          else
            ret { s with
                world := { s.world.setFd fd (.file i 0 r w app) with
                  files := s.world.files.setIfInBounds i (if trunc && w then f.truncate else f) } }
              (BitVec.ofNat 64 fd)
      | none =>
        if creat then
          if s.world.mayCreate then
            ret { s with
                world := { s.world.setFd fd (.file s.world.files.size 0 r w app) with
                  files := s.world.files.push { path := path } } }
              (BitVec.ofNat 64 fd)
          else ret s (-13)
        else ret s (-2)

/-- `close(fd)`. -/
def close (s : State) : State :=
  let fd := fdArg s .rdi
  match s.world.fd? fd with
  | some _ => ret { s with world := s.world.closeFd fd } 0
  | none => ret s (-9)

/-- `lseek(fd, offset, whence)`: move a file descriptor's position, counted
from the start of the file, from where it is, or from the end. The result
is the new position. -/
def lseek (s : State) : State :=
  let fd := fdArg s .rdi
  let whence := s.getReg .rdx
  match s.world.fd? fd with
  | some (.file i pos r w app) =>
    let size := ((s.world.files[i]?).map (·.size)).getD 0
    let from? : Option Nat :=
      if whence = 0 then some 0 else if whence = 1 then some pos
      else if whence = 2 then some size else none
    match from? with
    | none => ret s (-22)
    | some b =>
      let to : Int := b + (s.getReg .rsi).toInt
      if to < 0 then ret s (-22)
      else
        ret { s with world := s.world.setFd fd (.file i to.toNat r w app) }
          (BitVec.ofNat 64 to.toNat)
  | some _ => ret s (-29)
  | none => ret s (-9)

/-- The low `n` bytes of a number, least significant first. -/
def leBytes (n v : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => BitVec.ofNat 8 (v >>> (8 * i))

/-- `fstat(fd, buf)`: store a description of what the descriptor refers to,
144 bytes of it, at `buf`. -/
def fstat (s : State) : State :=
  let buf := s.getReg .rsi
  match s.world.fd? (fdArg s .rdi) with
  | none => ret s (-9)
  | some d =>
    -- a regular file that its owner may read and write, or a pipe
    let (mode, size) := match d with
      | .file i _ _ _ _ => (0x81a4, ((s.world.files[i]?).map (·.size)).getD 0)
      | _ => (0x1180, 0)
    let data :=
      leBytes 8 0 ++ leBytes 8 0 ++ leBytes 8 1 ++ leBytes 4 mode ++ leBytes 4 0 ++ leBytes 4 0 ++
      leBytes 4 0 ++ leBytes 8 0 ++ leBytes 8 size ++ leBytes 8 4096 ++
      leBytes 8 ((size + 511) / 512) ++ List.replicate 72 0
    if s.canWrite buf 144 then give s buf (data.take 144) 0 s.world else ret s (-14)

/-- `clock_gettime(clock, buf)`: store the time, seconds then nanoseconds,
16 bytes, at `buf`. -/
def clockGettime (s : State) : State :=
  let buf := s.getReg .rsi
  if 12 ≤ fdArg s .rdi then ret s (-22)
  else if s.canWrite buf 16 then
    let now := s.world.time s.world.asks
    give s buf ((leBytes 8 now.1.toNat ++ leBytes 8 now.2.toNat).take 16) 0
      { s.world with asks := s.world.asks + 1 }
  else ret s (-14)

/-- `getrandom(buf, length, flags)`: store random bytes at `buf`. The result
is how many, which is all that were asked for up to the kernel's limit. -/
def getrandom (s : State) : State :=
  let buf := s.getReg .rdi
  let n := min (s.getReg .rsi).toNat 33554431
  if s.canWrite buf n then
    give s buf (((List.range n).map fun i => s.world.random (s.world.drawn + i)).take n)
      (BitVec.ofNat 64 n) { s.world with drawn := s.world.drawn + n }
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

/-- `munmap(addr, length)`: give whole pages back. The model does so only
for memory that is writable or already inaccessible; asked to take away
anything else, such as the program's own code, it refuses, which the kernel
would not, so the call is typed only for memory the program owns. -/
def munmap (s : State) : State :=
  let a := s.getReg .rdi
  let len := (s.getReg .rsi).toNat
  let size := (len + 4095) / 4096 * 4096
  if a.toNat % 4096 = 0 ∧ len ≠ 0 ∧ a.toNat + size ≤ 2 ^ 47 ∧
      State.allBelow (fun i =>
        decide ((s.perm (a + BitVec.ofNat 64 i)).writable = true ∨
          s.perm (a + BitVec.ofNat 64 i) = .none)) size = true then
    ret (s.unmap a size) 0
  else ret s (-22)

end Linux

/-- The calls, by number: `read` 0, `write` 1, `close` 3, `fstat` 5, `lseek`
8, `mmap` 9, `munmap` 11, `exit` 60, `clock_gettime` 228, `exit_group` 231, `openat` 257
and `getrandom` 318. -/
def linux : Syscall := fun s =>
  if s.getReg .rax = 60 then .exit (s.readReg .w32 .rdi)
  else if s.getReg .rax = 231 then .exit (s.readReg .w32 .rdi)
  else if s.getReg .rax = 1 then .next (Linux.write s)
  else if s.getReg .rax = 0 then .next (Linux.read s)
  else if s.getReg .rax = 9 then .next (Linux.mmap s)
  else if s.getReg .rax = 11 then .next (Linux.munmap s)
  else if s.getReg .rax = 3 then .next (Linux.close s)
  else if s.getReg .rax = 5 then .next (Linux.fstat s)
  else if s.getReg .rax = 8 then .next (Linux.lseek s)
  else if s.getReg .rax = 228 then .next (Linux.clockGettime s)
  else if s.getReg .rax = 257 then .next (Linux.openat s)
  else if s.getReg .rax = 318 then .next (Linux.getrandom s)
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
    (hτ : ∀ (Ψ₂ : MemTy) (a : BitVec 64), Ψ₂ a = some ⟨fields, true, tag, 0⟩ →
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
            have hr := State.canRead_iff.mp (h.heapPerm a l hl).1 0 (hΨ.nonempty a l hl)
            rw [show a + BitVec.ofNat 64 0 = a by simp, hU a (by simpa using hpos)] at hr
            exact absurd hr (by decide)
        let L : Layout := ⟨fields, true, tag, 0⟩
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
            · show 0 < 8 * fields.length + 0
              omega
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
            sp := by rw [hg]; exact h.sp.ext hext
            owned :=
              { perm := fun b hb' => hwr _ _ (h.owned.perm b hb')
                size_lt := h.owned.size_lt
                vals := fun b hb' i υ hi => by
                  have hlt := (List.getElem?_eq_some_iff.mp hi).1
                  have hr := State.canRead_of_canWrite (State.canWrite_sub (h.owned.perm b hb')
                    (o := 8 * i) (m := 8) (by omega))
                  rw [State.load64_mapZero_out s hal hsz4 hfit64 (hout _ hr)]
                  exact (h.owned.vals b hb' i υ hi).ext hext
                stack := fun b hb' => by rw [hb]; exact h.owned.stack b hb'
                heap := fun b hb' x l hl => by
                  rcases hcases x l hl with ⟨hx, hlL⟩ | ⟨-, hl'⟩
                  · rw [hx, hlL]
                    show Disjoint _ _ _ (8 * fields.length + 0)
                    exact (hR b.1 (8 * b.2.length) (h.owned.size_lt b hb')
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
                · exact h.text x l hl' ht }
        have hM : WellTyped fetch sys Ψ₂ n Γ
            { s.mapZero a size with world := { s.world with asked := s.world.asked + 1 } } :=
          hM₀.congr rfl rfl rfl rfl
        exact ⟨Ψ₂, hext, hWF, ret_typed hM (hasTy_orErr.mpr (.inr (hτ Ψ₂ a hat)))⟩
      · exact herr _ _ (h.congr rfl rfl rfl rfl) (by decide)

/-! ## The two things a call can do to the program

Apart from `mmap`, every call either leaves the machine alone, changing only
the outside world and the registers a call always changes, or does that and
also stores bytes in a buffer it was handed. Each fact a call must satisfy
is proved once for each of the two. -/

/-- `t` is `s` after a call that touched nothing of the program's. -/
def OnlyWorld (s t : State) : Prop :=
  ∃ v w, t = ret { s with world := w } v

namespace OnlyWorld

variable {t : State}

theorem same (s : State) (v : BitVec 64) : OnlyWorld s (ret s v) :=
  ⟨v, s.world, rfl⟩

theorem intro (s : State) (v : BitVec 64) (w : World) :
    OnlyWorld s (ret { s with world := w } v) :=
  ⟨v, w, rfl⟩

theorem ok {sys : Syscall} (hf : OnlyWorld s t) (h : WellTyped fetch sys Ψ n Γ s) :
    WellTyped fetch sys Ψ n Γ.afterSyscall t := by
  obtain ⟨v, w, rfl⟩ := hf
  exact ret_ok (h.congr (t := { s with world := w }) rfl rfl rfl rfl) v

theorem rip (hf : OnlyWorld s t) : t.rip = s.rip := by
  obtain ⟨v, w, rfl⟩ := hf
  rfl

theorem frame (hf : OnlyWorld s t) : Frame s t := by
  obtain ⟨v, w, rfl⟩ := hf
  exact Frame.of_eq rfl rfl

end OnlyWorld

/-- `t` is `s` after a call that at most stored up to `room` bytes at `buf`,
all of them in writable memory. -/
def Fills (s : State) (buf : BitVec 64) (room : Nat) (t : State) : Prop :=
  OnlyWorld s t ∨
    ∃ data v w, data.length ≤ room ∧ s.canWrite buf data.length = true ∧ t = give s buf data v w

theorem Fills.same (s : State) (buf : BitVec 64) (room : Nat) (v : BitVec 64) :
    Fills s buf room (ret s v) :=
  .inl (.same s v)

theorem Fills.only (s : State) (buf : BitVec 64) (room : Nat) (v : BitVec 64) (w : World) :
    Fills s buf room (ret { s with world := w } v) :=
  .inl (.intro s v w)

theorem canWrite_le {a : BitVec 64} {m k : Nat} (h : s.canWrite a m = true) (hle : k ≤ m) :
    s.canWrite a k = true := by
  rw [State.canWrite_iff] at h ⊢
  exact fun i hi => h i (by omega)

theorem fills_give {buf : BitVec 64} {room : Nat} {data : List (BitVec 8)} {v : BitVec 64}
    {w : World} (hw : s.canWrite buf room = true) (hlen : data.length ≤ room) :
    Fills s buf room (give s buf data v w) :=
  .inr ⟨data, v, w, hlen, canWrite_le hw hlen, rfl⟩

/-- Bytes stored in integer fields of a writable block leave the state well
typed, whatever they are. -/
theorem storeBytes_ok {sys : Syscall} {r : Reg} {fields : List Ty} {off cnt : Nat}
    {data : List (BitVec 8)} (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hr : r ≠ .rsp)
    (hbuf : Γ.regs r = .ptr fields true off)
    (hints : ∀ j, j < cnt → fields[off + j]? = some .int) (hlen : data.length ≤ 8 * cnt) :
    WellTyped fetch sys Ψ n Γ (s.storeBytes (s.getReg r) data) := by
  have hp := h.regs r hr
  rw [hbuf] at hp
  obtain ⟨a, l, hl, rfl, -, hva⟩ := hasTy_ptr.mp hp
  rw [hva]
  by_cases hc : cnt = 0
  · -- nothing can be stored
    have hz : data = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hz, State.storeBytes_nil]
    exact h.congr rfl rfl rfl rfl
  · have hlast := hints (cnt - 1) (by omega)
    have hle : off + cnt ≤ l.fields.length := by
      have := (List.getElem?_eq_some_iff.mp hlast).1
      omega
    have hsz := hΨ.size_lt a l hl
    simp only [Layout.size] at hsz
    refine h.writeInts hΨ hl (lo := off) (cnt := cnt) (by omega) hle
      (fun j hj hj' => by
        have := hints (j - off) (by omega)
        rwa [show off + (j - off) = j by omega] at this)
      rfl rfl rfl (fun y hd => ?_) (fun x hx => by
        show (s.storeBytes _ data).mem x = s.mem x
        rw [State.mem_storeBytes s _ x _ (by omega), List.getElem?_eq_none (by bv_omega)]
        rfl)
    refine (State.load64_congr (s := s.storeBytes _ _) rfl y).trans
      (State.load64_storeBytes_disjoint s _ (by omega) ?_ (hd.2 (by omega)))
    have h1 := hd.1 (by decide)
    bv_omega

/-- Bytes stored in integer stack slots leave the state well typed, whatever
they are. -/
theorem storeBytes_ok_stack {sys : Syscall} {r : Reg} {v d : BitVec 64} {cnt : Nat}
    {data : List (BitVec 8)} (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hr : r ≠ .rsp)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs r = .eq (v + d)) (h8 : d.toNat % 8 = 0)
    (hints : ∀ j, j < cnt → Γ.stack[d.toNat / 8 + j]? = some .int)
    (hlen : data.length ≤ 8 * cnt) :
    WellTyped fetch sys Ψ n Γ (s.storeBytes (s.getReg r) data) := by
  have hv : s.getReg .rsp = v := by
    have := h.sp
    rwa [hsp, hasTy_eq] at this
  have hsi := h.eqReg hr hbuf
  have hbase : v + d = s.getReg .rsp + BitVec.ofNat 64 (8 * (d.toNat / 8)) := by
    rw [hv]; congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  rw [hsi]
  by_cases hc : cnt = 0
  · have hz : data = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hz, State.storeBytes_nil]
    exact h.congr rfl rfl rfl rfl
  · have hlast := hints (cnt - 1) (by omega)
    have hle : d.toNat / 8 + cnt ≤ Γ.stack.length := by
      have := (List.getElem?_eq_some_iff.mp hlast).1
      omega
    have hsz := h.stackSize_lt
    simp only [stackSize] at hsz
    refine h.writeSlotsInt hΨ (lo := d.toNat / 8) (cnt := cnt) (by omega) hle
      (fun j hj hj' => by
        have := hints (j - d.toNat / 8) (by omega)
        rwa [show d.toNat / 8 + (j - d.toNat / 8) = j by omega] at this)
      rfl rfl rfl (fun y hd => ?_) (fun x hx => by
        show (s.storeBytes _ data).mem x = s.mem x
        rw [hbase]
        rw [State.mem_storeBytes s _ x _ (by omega), List.getElem?_eq_none (by bv_omega)]
        rfl)
    rw [hbase]
    refine (State.load64_congr (s := s.storeBytes _ _) rfl y).trans
      (State.load64_storeBytes_disjoint s _ (by omega) ?_ (hd.2 (by omega)))
    have h1 := hd.1 (by decide)
    bv_omega

namespace Fills

variable {t : State} {r : Reg} {room : Nat}

/-- A call that fills a buffer lying in integer fields of a writable block
keeps the state well typed. -/
theorem ok {sys : Syscall} {fields : List Ty} {off cnt : Nat}
    (hf : Fills s (s.getReg r) room t) (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hr : r ≠ .rsp) (hbuf : Γ.regs r = .ptr fields true off)
    (hints : ∀ j, j < cnt → fields[off + j]? = some .int) (hroom : room ≤ 8 * cnt) :
    WellTyped fetch sys Ψ n Γ.afterSyscall t := by
  rcases hf with hf | ⟨data, v, w, hlen, -, rfl⟩
  · exact hf.ok h
  · exact ret_ok ((storeBytes_ok (data := data) h hΨ hr hbuf hints (by omega)).congr
      (t := { s.storeBytes (s.getReg r) data with world := w }) rfl rfl rfl rfl) v

/-- A call that fills a buffer lying in integer stack slots keeps the state
well typed. -/
theorem ok_stack {sys : Syscall} {v d : BitVec 64} {cnt : Nat}
    (hf : Fills s (s.getReg r) room t) (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hr : r ≠ .rsp) (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs r = .eq (v + d))
    (h8 : d.toNat % 8 = 0) (hints : ∀ j, j < cnt → Γ.stack[d.toNat / 8 + j]? = some .int)
    (hroom : room ≤ 8 * cnt) : WellTyped fetch sys Ψ n Γ.afterSyscall t := by
  rcases hf with hf | ⟨data, v', w, hlen, -, rfl⟩
  · exact hf.ok h
  · exact ret_ok
      ((storeBytes_ok_stack (data := data) h hΨ hr hsp hbuf h8 hints (by omega)).congr
        (t := { s.storeBytes (s.getReg r) data with world := w }) rfl rfl rfl rfl) v'

theorem rip {buf : BitVec 64} (hf : Fills s buf room t) : t.rip = s.rip := by
  rcases hf with hf | ⟨data, v, w, -, -, rfl⟩
  · exact hf.rip
  · rfl

/-- Only bytes of the buffer change, and those were writable. -/
theorem frame {buf : BitVec 64} (hf : Fills s buf room t) (hroom : room ≤ 2 ^ 64) : Frame s t := by
  rcases hf with hf | ⟨data, v, w, hlen, hw, rfl⟩
  · exact hf.frame
  · refine .of_perm rfl (fun x hx => ?_)
    show (s.storeBytes buf data).mem x = s.mem x
    rw [State.mem_storeBytes s _ x _ (by omega)]
    by_cases hin : (x - buf).toNat < data.length
    · -- a byte inside the buffer is writable, so it is not one of these
      rw [State.canWrite_iff] at hw
      have := hw _ hin
      rw [show buf + BitVec.ofNat 64 (x - buf).toNat = x by bv_omega] at this
      rw [this] at hx
      cases hx
    · rw [List.getElem?_eq_none (by omega)]
      rfl

end Fills

/-! ## Each call is one of the two -/

/-- Settles a call that only changes the world: every way it can end is a
plain return. -/
local macro "only_world" : tactic =>
  `(tactic| repeat' (first
    | (with_reducible exact OnlyWorld.same _ _)
    | (with_reducible exact OnlyWorld.intro _ _ _)
    | split))

/-- Settles a call that fills a buffer: every way it can end is a plain
return, or a store of no more than was asked for into memory found writable. -/
local macro "fills" : tactic =>
  `(tactic| repeat' (first
    | (with_reducible exact Fills.same _ _ _ _)
    | (with_reducible exact Fills.only _ _ _ _ _)
    | (with_reducible exact fills_give (by assumption) (List.length_take_le _ _))
    | split))

theorem write_only (s : State) : OnlyWorld s (write s) := by
  simp only [write]
  only_world

theorem openat_only (s : State) : OnlyWorld s (openat s) := by
  simp only [openat]
  only_world

theorem close_only (s : State) : OnlyWorld s (close s) := by
  simp only [close]
  only_world

theorem lseek_only (s : State) : OnlyWorld s (lseek s) := by
  simp only [lseek]
  only_world

theorem read_fills (s : State) : Fills s (s.getReg .rsi) (s.getReg .rdx).toNat (read s) := by
  simp only [read]
  fills

theorem fstat_fills (s : State) : Fills s (s.getReg .rsi) 144 (fstat s) := by
  simp only [fstat]
  fills

theorem clockGettime_fills (s : State) : Fills s (s.getReg .rsi) 16 (clockGettime s) := by
  simp only [clockGettime]
  fills

theorem getrandom_fills (s : State) :
    Fills s (s.getReg .rdi) (s.getReg .rsi).toNat (getrandom s) := by
  simp only [getrandom]
  split
  · next hw =>
    refine .inr ⟨_, _, _, ?_, ?_, rfl⟩
    · exact Nat.le_trans (List.length_take_le _ _) (Nat.min_le_left _ _)
    · exact canWrite_le hw (List.length_take_le _ _)
  · exact Fills.same _ _ _ _

/-- Only bytes that were not accessible change. -/
theorem mmap_frame (s : State) : Frame s (mmap s) := by
  simp only [mmap]
  split
  · exact Frame.of_eq rfl rfl
  · split
    · exact Frame.of_eq rfl rfl
    · split
      · exact Frame.of_eq rfl rfl
      · split
        · next a _ hok =>
          obtain ⟨hal, -, htop, hun⟩ := hok
          have hsz4 : ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 % 4096 = 0 := by omega
          generalize ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 = size at htop hun hsz4 ⊢
          have hfit64 : a.toNat + size ≤ 2 ^ 64 := by omega
          refine ⟨fun x hx _ => ?_, fun x hx _ => ?_⟩
          · show (s.mapZero a size).perm x = s.perm x
            rw [State.perm_mapZero s hal hsz4 hfit64]
            split
            · next hin => exact absurd (perm_of_unmapped hal hfit64 hun hin) hx
            · rfl
          · show (s.mapZero a size).mem x = s.mem x
            rw [State.mem_mapZero s hal hsz4 hfit64]
            split
            · next hin => exact absurd (perm_of_unmapped hal hfit64 hun hin) hx
            · rfl
        · exact Frame.of_eq rfl rfl

/-! ## Memory the program owns -/

/-- Anything readable lies apart from a range found inaccessible. -/
theorem disjoint_of_unmapped {a b : BitVec 64} {size m k : Nat}
    (hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none) (hsize : size < 2 ^ 64)
    (hk : k ≤ size) (hm : m < 2 ^ 64) (hr : s.canRead b m = true) : Disjoint a k b m := by
  rw [State.canRead_iff] at hr
  refine ⟨fun hm0 => ?_, fun hk0 => ?_⟩
  · apply Classical.byContradiction
    intro hlt
    have hb := hr 0 (by omega)
    rw [show b + BitVec.ofNat 64 0 = b by simp, hU b (by bv_omega)] at hb
    exact absurd hb (by decide)
  · apply Classical.byContradiction
    intro hlt
    have hb := hr (a - b).toNat (by bv_omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, show b + (a - b) = a by bv_omega,
      hU a (by simp; omega)] at hb
    exact absurd hb (by decide)

/-- Fresh memory appearing where nothing was accessible leaves a state well
typed as it was. -/
theorem mapZero_ok {sys : Syscall} {a : BitVec 64} {size : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hal : a.toNat % 4096 = 0) (hsz4 : size % 4096 = 0)
    (hfit : a.toNat + size ≤ 2 ^ 64)
    (hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none)
    (hpos : ∀ x l, Ψ x = some l → 0 < l.size) :
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
    stackSize_lt := h.stackSize_lt
    stack := fun i υ hi => by
      have hw := h.canWrite_slot (i := i) (List.getElem?_eq_some_iff.mp hi).1
      rw [hg, State.load64_mapZero_out s hal hsz4 hfit (hout _ (State.canRead_of_canWrite hw))]
      exact h.stack i υ hi
    heapPerm := fun x l hl =>
      ⟨hrd _ _ (h.heapPerm x l hl).1, fun hw => hwr _ _ ((h.heapPerm x l hl).2 hw)⟩
    heap := fun x l hl i υ hi => by
      have hr := h.canRead_field hl (List.getElem?_eq_some_iff.mp hi).1
      rw [State.load64_mapZero_out s hal hsz4 hfit (hout _ hr)]
      exact h.heap x l hl i υ hi
    stackHeap := fun x l hl => by rw [hb]; exact h.stackHeap x l hl
    sp := by rw [hg]; exact h.sp
    owned :=
      { perm := fun b hb' => hwr _ _ (h.owned.perm b hb')
        size_lt := h.owned.size_lt
        vals := fun b hb' i υ hi => by
          have hlt := (List.getElem?_eq_some_iff.mp hi).1
          have hr := State.canRead_of_canWrite (State.canWrite_sub (h.owned.perm b hb')
            (o := 8 * i) (m := 8) (by omega))
          rw [State.load64_mapZero_out s hal hsz4 hfit (hout _ hr)]
          exact h.owned.vals b hb' i υ hi
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
      · exact h.text x l hl ht }

/-- Fresh memory, found where nothing was accessible, may be owned as a block
of integers. -/
theorem mapZero_owned {sys : Syscall} {a : BitVec 64} {size cnt : Nat}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF) (hal : a.toNat % 4096 = 0)
    (hsz4 : size % 4096 = 0) (hfit64 : a.toNat + size ≤ 2 ^ 64)
    (hlt : size < 2 ^ 64) (hun : s.unmapped a size = true) (hG : 8 * cnt = size) :
    WellTyped fetch sys Ψ n { Γ with owned := (a, List.replicate cnt .int) :: Γ.owned }
      (s.mapZero a size) := by
  have hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none :=
    fun x hx => perm_of_unmapped hal hfit64 hun hx
  have hZ := mapZero_ok h hal hsz4 hfit64 hU hΨ.nonempty
  have hnew : (s.mapZero a size).canWrite a size = true := by
    rw [State.canWrite_iff]
    intro i hi
    rw [State.perm_mapZero s hal hsz4 hfit64]
    have : (a + BitVec.ofNat 64 i - a).toNat < size := by bv_omega
    simp only [this, ↓reduceIte]
    rfl
  refine hZ.addOwned (b := (a, List.replicate cnt .int)) ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [List.length_replicate, hG]; exact hnew
  · simp only [List.length_replicate, hG]; omega
  · intro i τ hi
    rw [List.getElem?_replicate] at hi
    split at hi
    · cases hi; exact HasTy.int _
    · cases hi
  · simp only [List.length_replicate, hG]
    exact (disjoint_of_unmapped hU (by omega) (Nat.le_refl _) h.stackSize_lt
      (State.canRead_of_canWrite h.stackPerm)).symm
  · intro x l hl
    simp only [List.length_replicate, hG]
    exact disjoint_of_unmapped hU (by omega) (Nat.le_refl _) (hΨ.size_lt x l hl)
      (h.heapPerm x l hl).1
  · intro c hc'
    simp only [List.length_replicate, hG]
    exact disjoint_of_unmapped hU (by omega) (Nat.le_refl _) (h.owned.size_lt c hc')
      (State.canRead_of_canWrite (h.owned.perm c hc'))

/-- What follows an `mmap` whose memory the program is to own: an error
number in `rax`, or the address of whole pages, zeroed, that the context now
owns as a block of integers. The address is the start of a page and lies
where the kernel puts a program's memory, in the lower half of the address
space; so it is never an error number. -/
def mmapOwnCtx (Γ : Ctx) (len : BitVec 64) :
    ({ e : BitVec 64 // SysErr e } ⊕
      { a : BitVec 64 // a.toNat % 4096 = 0 ∧ a < 0x800000000000 }) → Ctx
  | .inl e => Γ.afterSyscall.setReg .rax (.eq e.1)
  | .inr a =>
    { Γ.afterSyscall.setReg .rax (.eq a.1) with
      owned := (a.1, List.replicate ((len.toNat + 4095) / 4096 * 512) .int) :: Γ.owned }

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
        have hOwn := mapZero_owned h hΨ hal (cnt := (len.toNat + 4095) / 4096 * 512)
          (size := (len.toNat + 4095) / 4096 * 4096) (by omega) (by omega) (by omega)
          hun (by omega)
        have hlow : a < 0x800000000000 := by
          rw [BitVec.lt_def]
          show a.toNat < 0x800000000000
          omega
        exact ⟨.inr ⟨a, hal, hlow⟩, ret_typed
          (hOwn.congr (t := { s.mapZero a ((len.toNat + 4095) / 4096 * 4096) with
            world := { s.world with asked := s.world.asked + 1 } }) rfl rfl rfl rfl)
          (hasTy_eq.mpr rfl)⟩
      · exact herr _ _ (by decide) (h.congr rfl rfl rfl rfl)

theorem munmap_rip (s : State) : (munmap s).rip = s.rip := by
  simp only [munmap]
  split <;> rfl

/-- Only writable memory is given back. -/
theorem munmap_frame (s : State) : Frame s (munmap s) := by
  simp only [munmap]
  split
  · next hok =>
    obtain ⟨hal, -, htop, hall⟩ := hok
    have hsz4 : ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 % 4096 = 0 := by omega
    generalize ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 = size at htop hall hsz4 ⊢
    have hfit : (s.getReg .rdi).toNat + size ≤ 2 ^ 64 := by omega
    refine ⟨fun x hx hw => ?_, fun x _ _ => rfl⟩
    show (s.unmap _ size).perm x = s.perm x
    rw [State.perm_unmap s hal hsz4 hfit]
    split
    · next hin =>
      have := State.allBelow_iff.mp hall _ hin
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq,
        show s.getReg .rdi + (x - s.getReg .rdi) = x by bv_omega] at this
      rcases of_decide_eq_true this with hwr | hnone
      · rw [hwr] at hw; cases hw
      · exact absurd hnone hx
    · rfl
  · exact Frame.of_eq rfl rfl

/-- **Memory the program owns may be given back.** A `munmap` of exactly an
owned block leaves a state matching the context without it, whether or not
the kernel did as asked. -/
theorem munmap_ok {sys : Syscall} {k : Nat} {a len : BitVec 64} {F : List Ty}
    (h : WellTyped fetch sys Ψ n Γ s) (hΨ : Ψ.WF)
    (hdi : Γ.regs .rdi = .eq a) (hsi : Γ.regs .rsi = .eq len)
    (hk : Γ.owned[k]? = some (a, F))
    (hsz : 8 * F.length = (len.toNat + 4095) / 4096 * 4096) :
    WellTyped fetch sys Ψ n { Γ.afterSyscall with owned := Γ.owned.eraseIdx k } (munmap s) := by
  have hrdi := h.eqReg (by decide) hdi
  have hrsi := h.eqReg (by decide) hsi
  simp only [munmap, hrdi, hrsi]
  split
  · next hok =>
    obtain ⟨hal, -, htop, -⟩ := hok
    have hsz4 : (len.toNat + 4095) / 4096 * 4096 % 4096 = 0 := by omega
    rw [← hsz] at htop hsz4 ⊢
    have hfit : a.toNat + 8 * F.length ≤ 2 ^ 64 := by omega
    exact ret_ok (h.eraseOwned hΨ hk (s' := s.unmap a (8 * F.length)) rfl rfl rfl (fun x => by
      rw [State.perm_unmap s hal hsz4 hfit]
      split
      · next hin => exact .inr hin
      · exact .inl rfl)) _
  · exact ret_ok (h.eraseOwned hΨ hk rfl rfl rfl (fun _ => .inl rfl)) _

end Linux

/-! ## The calls, as the type system sees them -/

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

/-- `write`: with 1 in `rax`, the call returns, whatever its arguments. A
buffer that cannot be read is refused by the kernel, not a fault. -/
theorem linux_write (hΓ : Γ.regs .rax = .eq 1) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.write s, by simp [linux, hax], (Linux.write_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.write_only s).ok h⟩

/-- `openat`: with 257 in `rax`, the call returns, whatever its arguments. A
name that cannot be read is refused by the kernel, not a fault. -/
theorem linux_openat (hΓ : Γ.regs .rax = .eq 257) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.openat s, by simp [linux, hax], (Linux.openat_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.openat_only s).ok h⟩

/-- `close`: with 3 in `rax`, the call returns, whatever its argument. -/
theorem linux_close (hΓ : Γ.regs .rax = .eq 3) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.close s, by simp [linux, hax], (Linux.close_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.close_only s).ok h⟩

/-- `lseek`: with 8 in `rax`, the call returns, whatever its arguments. -/
theorem linux_lseek (hΓ : Γ.regs .rax = .eq 8) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.lseek s, by simp [linux, hax], (Linux.lseek_only s).rip, Ψ₁, .refl _, hΨ,
    (Linux.lseek_only s).ok h⟩

/-- `read`: with 0 in `rax`, the call returns, provided the buffer in `rsi`
points into a writable block and the `rdx` bytes from there are all in
integer fields. Without that the kernel could overwrite a typed pointer. -/
theorem linux_read {fields : List Ty} {off : Nat} {len : BitVec 64} (hΓ : Γ.regs .rax = .eq 0)
    (hbuf : Γ.regs .rsi = .ptr fields true off) (hlen : Γ.regs .rdx = .eq len)
    (hints : ∀ j, j < (len.toNat + 7) / 8 → fields[off + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.read_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.read s, by simp [linux, hax], hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok h hΨ (by decide) hbuf hints (by omega)⟩

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
  have hf := Linux.read_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.read s, by simp [linux, hax], hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_stack h hΨ (by decide) hsp hbuf h8 hints (by omega)⟩

/-- `fstat`: with 5 in `rax`, the call returns, provided the buffer in `rsi`
points into a writable block and the 144 bytes from there, which is what the
kernel stores, are all in integer fields. -/
theorem linux_fstat {fields : List Ty} {off : Nat} (hΓ : Γ.regs .rax = .eq 5)
    (hbuf : Γ.regs .rsi = .ptr fields true off)
    (hints : ∀ j, j < 18 → fields[off + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.fstat_fills s
  exact ⟨Linux.fstat s, by simp [linux, hax], hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok h hΨ (by decide) hbuf hints (by omega)⟩

/-- `fstat` into the stack: as `linux_fstat`, with the buffer a known
distance above the stack pointer and its 144 bytes in integer stack slots. -/
theorem linux_fstat_stack {v d : BitVec 64} (hΓ : Γ.regs .rax = .eq 5)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs .rsi = .eq (v + d)) (h8 : d.toNat % 8 = 0)
    (hints : ∀ j, j < 18 → Γ.stack[d.toNat / 8 + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.fstat_fills s
  exact ⟨Linux.fstat s, by simp [linux, hax], hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_stack h hΨ (by decide) hsp hbuf h8 hints (by omega)⟩

/-- `clock_gettime`: with 228 in `rax`, the call returns, provided the buffer
in `rsi` points into a writable block and the 16 bytes from there are in
integer fields. -/
theorem linux_clock_gettime {fields : List Ty} {off : Nat} (hΓ : Γ.regs .rax = .eq 228)
    (hbuf : Γ.regs .rsi = .ptr fields true off)
    (hints : ∀ j, j < 2 → fields[off + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.clockGettime_fills s
  exact ⟨Linux.clockGettime s, by simp [linux, hax], hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok h hΨ (by decide) hbuf hints (by omega)⟩

/-- `clock_gettime` into the stack. -/
theorem linux_clock_gettime_stack {v d : BitVec 64} (hΓ : Γ.regs .rax = .eq 228)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs .rsi = .eq (v + d)) (h8 : d.toNat % 8 = 0)
    (hints : ∀ j, j < 2 → Γ.stack[d.toNat / 8 + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.clockGettime_fills s
  exact ⟨Linux.clockGettime s, by simp [linux, hax], hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_stack h hΨ (by decide) hsp hbuf h8 hints (by omega)⟩

/-- `getrandom`: with 318 in `rax`, the call returns, provided the buffer in
`rdi` points into a writable block and the `rsi` bytes from there are all in
integer fields. -/
theorem linux_getrandom {fields : List Ty} {off : Nat} {len : BitVec 64}
    (hΓ : Γ.regs .rax = .eq 318) (hbuf : Γ.regs .rdi = .ptr fields true off)
    (hlen : Γ.regs .rsi = .eq len)
    (hints : ∀ j, j < (len.toNat + 7) / 8 → fields[off + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.getrandom_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.getrandom s, by simp [linux, hax], hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok h hΨ (by decide) hbuf hints (by omega)⟩

/-- `getrandom` into the stack. -/
theorem linux_getrandom_stack {v d len : BitVec 64} (hΓ : Γ.regs .rax = .eq 318)
    (hsp : Γ.regs .rsp = .eq v) (hbuf : Γ.regs .rdi = .eq (v + d)) (h8 : d.toNat % 8 = 0)
    (hlen : Γ.regs .rsi = .eq len)
    (hints : ∀ j, j < (len.toNat + 7) / 8 → Γ.stack[d.toNat / 8 + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hf := Linux.getrandom_fills s
  rw [h.eqReg (by decide) hlen] at hf
  exact ⟨Linux.getrandom s, by simp [linux, hax], hf.rip, Ψ₁, .refl _, hΨ,
    hf.ok_stack h hΨ (by decide) hsp hbuf h8 hints (by omega)⟩

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

/-- `mmap` for memory the program is to own: with 9 in `rax`, the length in
`rsi`, 3 in `rdx` and 0x22 in `r10`, the call continues with an error number
in `rax`, or with the address of whole pages that the context now owns as a
block of integers. -/
theorem linux_mmap_own {next : BitVec 64} {len : BitVec 64} (hΓ : Γ.regs .rax = .eq 9)
    (hlen : Γ.regs .rsi = .eq len) (hprot : Γ.regs .rdx = .eq 3)
    (hflags : Γ.regs .r10 = .eq 0x22) :
    StepsTo fetch linux Ψ next Γ .syscall (Linux.mmapOwnCtx Γ len) := by
  intro Ψ₁ _ hΨ n s h _
  have hax := h.eqReg (by decide) hΓ
  obtain ⟨x, hw⟩ := Linux.mmapOwn_ok h hΨ hlen hprot hflags
  exact ⟨Linux.mmap s, x, by show linux s = _; simp [linux, hax], Linux.mmap_rip s, Ψ₁, .refl _,
    hΨ, hw⟩

/-- `munmap` of a block the context owns: with 11 in `rax`, the block's
address in `rdi` and a length in `rsi` that covers exactly the block, the
call returns and the context no longer owns the block. -/
theorem linux_munmap {k : Nat} {a len : BitVec 64} {F : List Ty} (hΓ : Γ.regs .rax = .eq 11)
    (hdi : Γ.regs .rdi = .eq a) (hsi : Γ.regs .rsi = .eq len)
    (hk : Γ.owned[k]? = some (a, F))
    (hsz : 8 * F.length = (len.toNat + 4095) / 4096 * 4096) :
    SysReturns fetch linux Ψ Γ { Γ.afterSyscall with owned := Γ.owned.eraseIdx k } := by
  intro Ψ₁ _ hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨Linux.munmap s, by simp [linux, hax], Linux.munmap_rip s, Ψ₁, .refl _, hΨ,
    Linux.munmap_ok h hΨ hdi hsi hk hsz⟩

/-! ## Memory the program cannot write stays as it was -/

/-- No system call changes a byte that is accessible but not writable, in
permission or in contents. -/
theorem linux_frame (s : State) : (linux s).All (Frame s) := by
  unfold linux
  by_cases h : s.getReg .rax = 60
  · rw [h]
    simp only [↓reduceIte]
    trivial
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 231
  · rw [h]
    simp only [↓reduceIte]
    trivial
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 1
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.write_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 0
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.read_fills s).frame (Nat.le_of_lt (s.getReg .rdx).isLt)
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 9
  · rw [h]
    simp only [↓reduceIte]
    exact Linux.mmap_frame s
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 11
  · rw [h]
    simp only [↓reduceIte]
    exact Linux.munmap_frame s
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 3
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.close_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 5
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.fstat_fills s).frame (by decide)
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 8
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.lseek_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 228
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.clockGettime_fills s).frame (by decide)
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 257
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.openat_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 318
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.getrandom_fills s).frame (Nat.le_of_lt (s.getReg .rsi).isLt)
  simp only [h, ↓reduceIte]
  clear h
  exact Frame.of_eq rfl rfl

end TypedAsm
