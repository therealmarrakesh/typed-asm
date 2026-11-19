import TypedAsm.Linux

/-!
# What a system call looks at

A system call takes its number in `rax` and its arguments in six registers,
and the kernel uses two more on the way back. It has nothing to do with the
rest: with any other value in one of them, each call the model has does the
same, returns the same, and leaves that value where it was. This is proved
call by call, and then of them all.
-/

namespace TypedAsm
open TypedAsm

/-- The registers a system call may look at or change: the call number and
its six arguments, and the two the kernel uses. -/
def sysRegs : List Reg := [.rax, .rdi, .rsi, .rdx, .r10, .r8, .r9, .rcx, .r11]

namespace Linux

theorem world_setReg (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).world = s.world := rfl

theorem withWorld_setReg (s : State) (r : Reg) (v : BitVec 64) (w : World) :
    ({ s.setReg r v with world := w } : State) = ({ s with world := w } : State).setReg r v := rfl

theorem ret_setReg (s : State) (x : BitVec 64) {r : Reg} (h1 : r ≠ .rax) (h2 : r ≠ .rcx)
    (h3 : r ≠ .r11) (v : BitVec 64) : ret (s.setReg r v) x = (ret s x).setReg r v := by
  cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | rfl

theorem runFrom_setReg (s : State) (r : Reg) (v : BitVec 64) (p : Perm → Bool) (a : BitVec 64) :
    ∀ fuel i, runFrom (s.setReg r v) p a i fuel = runFrom s p a i fuel
  | 0, _ => rfl
  | fuel + 1, i => by
    simp only [runFrom]
    rw [runFrom_setReg s r v p a fuel]
    rfl

theorem readableRun_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) :
    readableRun (s.setReg r v) a n = readableRun s a n := runFrom_setReg s r v _ a _ _

theorem writableRun_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) :
    writableRun (s.setReg r v) a n = writableRun s a n := runFrom_setReg s r v _ a _ _

theorem give_setReg (s : State) (buf : BitVec 64) (data : List (BitVec 8)) (x : BitVec 64)
    (w : World) {r : Reg} (h1 : r ≠ .rax) (h2 : r ≠ .rcx) (h3 : r ≠ .r11) (v : BitVec 64) :
    give (s.setReg r v) buf data x w = (give s buf data x w).setReg r v :=
  ret_setReg { s.storeBytes buf data with world := w } x h1 h2 h3 v

theorem canWrite_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) :
    (s.setReg r v).canWrite a n = s.canWrite a n := rfl

theorem canRead_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) :
    (s.setReg r v).canRead a n = s.canRead a n := rfl

theorem loadBytes_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) :
    (s.setReg r v).loadBytes a n = s.loadBytes a n := rfl

theorem cstring_setReg (s : State) (r : Reg) (v : BitVec 64) :
    ∀ fuel a, cstring (s.setReg r v) fuel a = cstring s fuel a
  | 0, _ => rfl
  | fuel + 1, a => by
    simp only [cstring]
    rw [cstring_setReg s r v fuel]
    rfl

theorem unmapped_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) :
    (s.setReg r v).unmapped a n = s.unmapped a n := rfl

theorem perm_setReg (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).perm = s.perm := rfl

theorem mapZero_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) (w : World) :
    ({ (s.setReg r v).mapZero a n with world := w } : State)
      = ({ s.mapZero a n with world := w } : State).setReg r v := rfl

theorem unmap_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) :
    (s.setReg r v).unmap a n = (s.unmap a n).setReg r v := rfl

theorem ne_of_not_sys {r : Reg} (h : r ∉ sysRegs) :
    (r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .r10 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .rcx ∧
      r ≠ .r11) ∧
    ((.rax : Reg) ≠ r ∧ (.rdi : Reg) ≠ r ∧ (.rsi : Reg) ≠ r ∧ (.rdx : Reg) ≠ r ∧ (.r10 : Reg) ≠ r ∧
      (.r8 : Reg) ≠ r ∧ (.r9 : Reg) ≠ r ∧ (.rcx : Reg) ≠ r ∧ (.r11 : Reg) ≠ r) := by
  cases r <;> first | exact absurd (by decide) h | decide

/-- Settles one call, for a register it has nothing to do with: what the
call looks at is the same, each construction it returns through passes the
register's new value out, and each case of it is then the same case. -/
local macro "sys_local" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (intro r hr
             obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ :=
               ne_of_not_sys hr
             simp (config := { maxSteps := 2000000 }) (disch := assumption) only [$ts,*, nextFate,
               fdArg, world_setReg, withWorld_setReg, State.getReg_setReg_other, ret_setReg,
               readableRun_setReg, writableRun_setReg, give_setReg, canWrite_setReg, canRead_setReg,
               loadBytes_setReg, cstring_setReg]
             repeat' (split <;> (try simp only [*, ↓reduceIte]))
             all_goals (first | rfl | contradiction | (simp only [*, ↓reduceIte] <;> rfl) |
               (exfalso; simp_all))))

/-- The same, for a call whose cases are few. -/
local macro "sys_plain" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (intro r hr
             obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ :=
               ne_of_not_sys hr
             simp (disch := assumption) only [$ts,*, nextFate, fdArg, world_setReg,
               withWorld_setReg, State.getReg_setReg_other, ret_setReg, unmapped_setReg,
               perm_setReg, mapZero_setReg, unmap_setReg]
             repeat' split
             all_goals (first | rfl | contradiction | (simp only [*, ↓reduceIte] <;> rfl) |
               (exfalso; simp_all))))

theorem close_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → close (s.setReg r v) = (close s).setReg r v := by
  sys_local [close, closeBy]

theorem lseek_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → lseek (s.setReg r v) = (lseek s).setReg r v := by
  sys_local [lseek]

theorem fsync_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → fsync (s.setReg r v) = (fsync s).setReg r v := by
  sys_local [fsync, fsyncBy]

theorem getpid_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → getpid (s.setReg r v) = (getpid s).setReg r v := by
  sys_local [getpid]

theorem write_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → write (s.setReg r v) = (write s).setReg r v := by
  sys_local [write, writeBy]

theorem read_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → read (s.setReg r v) = (read s).setReg r v := by
  sys_local [read, readBy]

theorem openatIn_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → openatIn (s.setReg r v) = (openatIn s).setReg r v := by
  sys_local [openatIn]

theorem openat_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → openat (s.setReg r v) = (openat s).setReg r v := by
  sys_local [openat, openatIn_setReg]

theorem fstat_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → fstat (s.setReg r v) = (fstat s).setReg r v := by
  sys_local [fstat]

theorem clockGettime_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → clockGettime (s.setReg r v) = (clockGettime s).setReg r v := by
  sys_local [clockGettime]

theorem getrandom_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → getrandom (s.setReg r v) = (getrandom s).setReg r v := by
  sys_local [getrandom, grndBad, grndMayRefuse, grndMayStop, grndMost, grndDeliver]

theorem mmap_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → mmap (s.setReg r v) = (mmap s).setReg r v := by
  sys_plain [mmap]

theorem munmap_setReg (s : State) (v : BitVec 64) :
    ∀ r, r ∉ sysRegs → munmap (s.setReg r v) = (munmap s).setReg r v := by
  sys_plain [munmap]

end Linux

/-- **A system call does not look at a register that is not one of its
own**: with any other value in it, the call returns the same, and leaves
that value there. -/
theorem linux_setReg {s t : State} (h : linux s = .next t) {r : Reg} (hr : r ∉ sysRegs)
    (v : BitVec 64) : linux (s.setReg r v) = .next (t.setReg r v) := by
  obtain ⟨⟨h1, h2, -, -, -, -, -, h8, h9⟩, -⟩ := Linux.ne_of_not_sys hr
  have hax : (s.setReg r v).getReg .rax = s.getReg .rax :=
    State.getReg_setReg_other _ _ _ _ (Ne.symm h1)
  have hdi : (s.setReg r v).getReg .rdi = s.getReg .rdi :=
    State.getReg_setReg_other _ _ _ _ (Ne.symm h2)
  simp only [linux, hax, hdi] at h ⊢
  by_cases hc : s.getReg .rax = 60
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 231
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 1
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.write_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 0
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.read_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 9
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    split at h
    · next hz =>
      cases h
      simp only [hz, ↓reduceIte]
      rw [Linux.mmap_setReg s v r hr]
    · cases h
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 11
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.munmap_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 3
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.close_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 5
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.fstat_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 8
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.lseek_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 228
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.clockGettime_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 257
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.openat_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 74
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.fsync_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 75
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.fsync_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 39
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.getpid_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  by_cases hc : s.getReg .rax = 318
  · rw [hc] at h ⊢
    simp only [↓reduceIte] at h ⊢
    cases h
    rw [Linux.getrandom_setReg s v r hr]
  simp only [hc, ↓reduceIte] at h ⊢
  clear hc
  cases h
  rw [Linux.ret_setReg s _ h1 h8 h9 v]

end TypedAsm
