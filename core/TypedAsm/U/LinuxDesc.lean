import TypedAsm.U.SysMem

/-!
# Linux, described

Which of the few things each Linux call does to a program; and the same of
a system that refuses exits whose status is not as wanted, or writes whose
bytes are not, which is how what a program ends with and what it writes are
shown. Those are not other rules for the calls: they are other systems, and
what they ask of the state to let a call through.
-/

namespace TypedAsm.U

/-- What the Linux call of each number does to the program. `munmap` takes
memory away, and is described by itself. A
number that is no call's is refused by the kernel, which is to do nothing. -/
def linuxKind (nr : BitVec 64) : Option SysKind :=
  if nr = 60 ∨ nr = 231 then some .ends
  else if nr = 0 then some (.fills .rsi (.inl .rdx))
  else if nr = 5 then some (.fills .rsi (.inr 144))
  else if nr = 228 then some (.fills .rsi (.inr 16))
  else if nr = 318 then some (.fills .rdi (.inl .rsi))
  else if nr = 9 then some .map
  else if nr = 11 then none
  else some .world

def linuxDesc : SysDesc := { kind := linuxKind }

/-- The model's `mmap` hands back an error number, or fresh pages. -/
theorem mmap_maps (s : State) : Maps s (pages (s.getReg .rsi)) (Linux.mmap s) := by
  unfold Linux.mmap
  simp only
  split
  · exact .inl ⟨_, s.world, by decide, rfl⟩
  · split
    · exact .inl ⟨_, s.world, by decide, rfl⟩
    · split
      · exact .inl ⟨_, _, by decide, rfl⟩
      · next a _ =>
        split
        · next hok => exact .inr ⟨a, _, hok.1, hok.2.2.1, hok.2.2.2, rfl⟩
        · exact .inl ⟨_, _, by decide, rfl⟩

/-- **The Linux model does what it is described to do.** -/
theorem linux_describes : Describes linux linuxDesc := by
  intro s k hk _
  unfold linuxDesc linuxKind at hk
  simp only at hk
  split at hk
  · next h =>
    cases hk
    rcases h with h | h
    · exact ⟨s.readReg .w32 .rdi, by simp [linux, h]⟩
    · exact ⟨s.readReg .w32 .rdi, by simp [linux, h]⟩
  · next h60 =>
    split at hk
    · next h =>
      cases hk
      exact ⟨Linux.read s, by simp [linux, h], by simpa [roomOf] using Linux.read_fills s⟩
    · next h0 =>
      split at hk
      · next h => cases hk; exact ⟨Linux.fstat s, by simp [linux, h], Linux.fstat_fills s⟩
      · next h5 =>
        split at hk
        · next h =>
          cases hk
          exact ⟨Linux.clockGettime s, by simp [linux, h], Linux.clockGettime_fills s⟩
        · next h228 =>
          split at hk
          · next h =>
            cases hk
            exact ⟨Linux.getrandom s, by simp [linux, h],
              by simpa [roomOf] using Linux.getrandom_fills s⟩
          · next h318 =>
            split at hk
            · next h9 =>
              cases hk
              intro hdi
              exact ⟨Linux.mmap s, by simp [linux, h9, hdi], mmap_maps s⟩
            · next h9 =>
              split at hk
              · cases hk
              · next h11 =>
                cases hk
                have h60' : s.getReg .rax ≠ 60 := fun e => h60 (.inl e)
                have h231 : s.getReg .rax ≠ 231 := fun e => h60 (.inr e)
                show ∃ t, linux s = .next t ∧ Linux.OnlyWorld s t
                unfold linux
                simp only [h60', h231, h0, h9, h11, h5, h228, h318, ↓reduceIte]
                repeat' split
                all_goals first
                  | exact ⟨_, rfl, Linux.write_only s⟩
                  | exact ⟨_, rfl, Linux.close_only s⟩
                  | exact ⟨_, rfl, Linux.lseek_only s⟩
                  | exact ⟨_, rfl, Linux.openat_only s⟩
                  | exact ⟨_, rfl, Linux.fsync_only s⟩
                  | exact ⟨_, rfl, Linux.getpid_only s⟩
                  | exact ⟨_, rfl, Linux.OnlyWorld.same s _⟩

/-- A system that lets through only exits whose status is as wanted does
what the system under it is described to do, where the status of any exit
is as wanted. -/
theorem Describes.exitsOnly {sys : Syscall} {D : SysDesc} (h : Describes sys D)
    (Q : BitVec 32 → Prop) :
    Describes (sys.exitsOnly Q)
      { D with pre := fun s => D.pre s ∧ ∀ c, sys s = .exit c → Q c } := by
  intro s k hk hpre
  have := h s k hk hpre.1
  cases k with
  | world =>
    obtain ⟨t, ht, hw⟩ := this
    exact ⟨t, Syscall.exitsOnly_next ht, hw⟩
  | fills b room =>
    obtain ⟨t, ht, hw⟩ := this
    exact ⟨t, Syscall.exitsOnly_next ht, hw⟩
  | ends =>
    obtain ⟨c, hc⟩ := this
    exact ⟨c, Syscall.exitsOnly_exit hc (hpre.2 c hc)⟩
  | map =>
    intro hdi
    obtain ⟨t, ht, hm⟩ := this hdi
    exact ⟨t, Syscall.exitsOnly_next ht, hm⟩

/-- And one that lets through only writes whose bytes are as wanted,
likewise, where the bytes a `write` offers are. -/
theorem Describes.writesOnly {sys : Syscall} {D : SysDesc} (h : Describes sys D)
    (R : BitVec 64 → List (BitVec 8) → Prop) :
    Describes (sys.writesOnly R)
      { D with pre := fun s => D.pre s ∧ (s.getReg .rax = 1 → R (s.getReg .rdi) s.offered) } := by
  intro s k hk hpre
  have := h s k hk hpre.1
  rw [show sys.writesOnly R s = sys s from Syscall.writesOnly_eq hpre.2]
  exact this

/-- The status Linux ends a program with, at an `exit` or an `exit_group`,
is the low half of `rdi`. -/
theorem linux_exit_status {s : State} {c : BitVec 32}
    (hax : s.getReg .rax = 60 ∨ s.getReg .rax = 231) (h : linux s = .exit c) :
    c = s.readReg .w32 .rdi := by
  have e : linux s = .exit (s.readReg .w32 .rdi) := by
    rcases hax with h60 | h231
    · simp [linux, h60]
    · simp [linux, h231]
  rw [e] at h
  cases h
  rfl

end TypedAsm.U
