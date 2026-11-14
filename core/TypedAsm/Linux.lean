import TypedAsm.Soundness
import TypedAsm.Frame

/-!
# A small model of Linux

Three system calls: `exit`, `write` and `read`. Every other call number is
modelled as failing with `-ENOSYS`, but that is not what the real kernel
does with them, so the type system has no rule for them: a `syscall` is
typed only when the number in `rax` is exactly known and is one of the three.

What the model leaves out of the calls it does have:

* A `write` always writes everything it is given. The real kernel may write
  less, or raise a signal (a write to a closed pipe).
* Only file descriptors 0 (for `read`) and 1 and 2 (for `write`) exist.
* A `read` into memory that is not writable fails without consuming input.
  The real kernel may deliver part of the data first.

None of these changes what the types rely on: the call returns to the next
instruction, memory is changed only inside the buffer of a `read`, and
`rax`, `rcx`, `r11` and the flags hold values nothing is known about.
-/

namespace TypedAsm

namespace Linux

/-- The state a call returns in, with result `v`. Like the real kernel, a
returning call overwrites `rcx` and `r11` and leaves the flags unknown. -/
def ret (s : State) (v : BitVec 64) : State :=
  { ((s.setReg .rax v).setReg .rcx s.rip).setReg .r11 0 with flags := .unknown }

/-- `write(fd, buf, count)`: append `count` bytes from `buf` to the output. -/
def write (s : State) : State :=
  let fd := s.getReg .rdi
  let buf := s.getReg .rsi
  let count := (s.getReg .rdx).toNat
  if fd ≠ 1 ∧ fd ≠ 2 then ret s (-9)
  else if s.canRead buf count then
    ret { s with world := { s.world with output := s.world.output ++ s.loadBytes buf count } }
      (BitVec.ofNat 64 count)
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
      let n := min count data.length
      let left := data.drop n
      ret { s.storeBytes buf (data.take n) with
          world := { s.world with input := if left.isEmpty then rest else .bytes left :: rest } }
        (BitVec.ofNat 64 n)
  else ret s (-14)

end Linux

/-- `exit` is call 60, `write` is 1 and `read` is 0. -/
def linux : Syscall := fun s =>
  if s.getReg .rax = 60 then .exit (s.readReg .w32 .rdi)
  else if s.getReg .rax = 1 then .next (Linux.write s)
  else if s.getReg .rax = 0 then .next (Linux.read s)
  else .next (Linux.ret s (-38))

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
          have hz : min len.toNat data.length = 0 := by omega
          refine h.congr rfl rfl ?_ rfl
          funext x
          simp [State.storeBytes, hz]
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
          have htake : (data.take (min len.toNat data.length)).length ≤ len.toNat := by
            simp only [List.length_take]; omega
          refine (State.load64_congr (s := s.storeBytes _ _) rfl y).trans
            (State.load64_storeBytes_disjoint s _ (by omega) ?_ hd.2)
          have h1 := hd.1
          bv_omega
    · exact ret_ok h _

end Linux

/-! ## The three calls, as the type system sees them -/

/-- `exit`: with 60 in `rax`, the program ends. -/
theorem linux_exit (hΓ : Γ.regs .rax = .eq 60) : SysExits fetch linux Ψ Γ := by
  intro n s h
  have hax := h.eqReg (by decide) hΓ
  exact ⟨s.readReg .w32 .rdi, by simp [linux, hax]⟩

/-- `write`: with 1 in `rax`, the call returns, whatever its arguments. A
buffer that cannot be read is refused by the kernel, not a fault. -/
theorem linux_write (hΓ : Γ.regs .rax = .eq 1) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro _ n s h
  have hax := h.eqReg (by decide) hΓ
  refine ⟨Linux.write s, ?_, Linux.write_rip s, Linux.write_ok h⟩
  simp [linux, hax]

/-- `read`: with 0 in `rax`, the call returns, provided the buffer in `rsi`
points into a writable block and the `rdx` bytes from there are all in
integer fields. Without that the kernel could overwrite a typed pointer. -/
theorem linux_read {fields : List Ty} {off : Nat} {len : BitVec 64} (hΓ : Γ.regs .rax = .eq 0)
    (hbuf : Γ.regs .rsi = .ptr fields true off) (hlen : Γ.regs .rdx = .eq len)
    (hints : ∀ j, j < (len.toNat + 7) / 8 → fields[off + j]? = some .int) :
    SysReturns fetch linux Ψ Γ Γ.afterSyscall := by
  intro hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  refine ⟨Linux.read s, ?_, Linux.read_rip s, Linux.read_ok h hΨ hbuf hlen hints⟩
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

/-! ## Memory the program cannot write stays as it was -/

/-- No system call changes a permission, or memory that is not writable. -/
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
              refine ⟨rfl, fun x hx => ?_⟩
              show (s.storeBytes _ _).mem x = s.mem x
              simp only [State.storeBytes]
              split
              · next hin =>
                -- a byte inside the buffer is writable, so it is not one of these
                rw [State.canWrite_iff] at hw
                have hlt : (x - s.getReg .rsi).toNat < (s.getReg .rdx).toNat := by
                  simp only [List.length_take] at hin; omega
                have := hw _ hlt
                rw [show s.getReg .rsi + BitVec.ofNat 64 (x - s.getReg .rsi).toNat = x by
                  bv_omega] at this
                rw [this] at hx
                cases hx
              · rfl
          · exact Frame.of_eq rfl rfl
      · exact Frame.of_eq rfl rfl

end TypedAsm
