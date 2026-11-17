import TypedAsm.LinuxOld

/-!
# What a run adds to the record of writes

The world keeps the bytes of each `write` (`World.writes`). No instruction
but a system call changes the world at all, and no system call but `write`
adds to that record; a `write` adds nothing, or the first so many of the
bytes it was offered. `step_writes` says so of one step, and is what the
statement about everything a program writes rests on (`WritesOnly.output`).
-/

namespace TypedAsm

namespace State

theorem write_world (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.write w a v).All (fun t => t.world = s.world) := by
  unfold write
  split
  · show (_ : World) = _; cases w <;> rfl
  · trivial

theorem write64_world (s : State) (a v : BitVec 64) :
    (s.write64 a v).All (fun t => t.world = s.world) := by
  unfold write64
  split
  · show (_ : World) = _; rfl
  · trivial

theorem write8_world (s : State) (a : BitVec 64) (v : BitVec 8) :
    (s.write8 a v).All (fun t => t.world = s.world) := by
  unfold write8
  split
  · show (_ : World) = _; rfl
  · trivial

theorem write16_world (s : State) (a : BitVec 64) (v : BitVec 16) :
    (s.write16 a v).All (fun t => t.world = s.world) := by
  unfold write16
  split
  · show (_ : World) = _; rfl
  · trivial

theorem writeRM_world (s : State) (w : Width) (dst : RM) (v : BitVec w.bits) :
    (s.writeRM w dst v).All (fun t => t.world = s.world) := by
  cases dst with
  | reg r => show (_ : World) = _; rfl
  | mem m => exact (Result.all_through _ _ _).mpr (write_world s w _ v)

theorem writeRM8_world (s : State) (dst : RM) (v : BitVec 8) :
    (s.writeRM8 dst v).All (fun t => t.world = s.world) := by
  cases dst with
  | reg r => show (_ : World) = _; rfl
  | mem m => exact (Result.all_through _ _ _).mpr (write8_world s _ v)

theorem push64_world (s : State) (v : BitVec 64) :
    (s.push64 v).All (fun t => t.world = s.world) :=
  (Result.all_onStack _ _).mpr (write64_world (s.setReg .rsp (s.getReg .rsp - 8)) _ v)

theorem pop64_world (s : State) : (s.pop64).All (fun p => p.2.world = s.world) := by
  simp only [pop64, Result.all_bind, Result.all_pure, Result.all_onStack]
  exact Result.All.of_forall (fun _ => by show (_ : World) = _; rfl)

end State

/-- Works through the steps of an instruction: none of them touches the world. -/
local macro "world_steps" : tactic =>
  `(tactic| repeat (first
      | (show (_ : World) = _; rfl)
      | exact State.writeRM_world _ _ _ _
      | exact State.writeRM8_world _ _ _
      | exact State.write8_world _ _ _
      | exact State.write16_world _ _ _
      | exact State.push64_world _ _
      | (refine Result.All.mono (State.writeRM_world _ _ _ _) ?_; intro _ hF; exact hF)
      | (refine Result.All.mono (State.writeRM8_world _ _ _) ?_; intro _ hF; exact hF)
      | (refine Result.All.mono (State.push64_world _ _) ?_; intro _ hF; exact hF)
      | (refine Result.All.mono (State.pop64_world _) ?_; intro _ hF; exact hF)
      | simp only [Result.all_bind, Result.all_pure, Result.all_next, Result.all_fault,
          Result.all_stuck, Result.all_through, Result.all_onStack]
      | split
      | (apply Result.All.of_forall; intro _)))

/-- **No instruction but a system call changes the world.** -/
theorem exec_world {sys : Syscall} (i : Instr) (s : State) (hi : i ≠ .syscall) :
    (exec sys i s).All (fun t => t.world = s.world) := by
  cases i with
  | syscall => exact absurd rfl hi
  | ud2 => trivial
  | unary op w dst => cases op <;> (simp only [exec]; world_steps)
  | jmp t => cases t <;> (simp only [exec]; world_steps)
  | _ => simp only [exec]; world_steps

namespace Linux

/-- Settles a call that adds nothing to the record of writes, however it ends. -/
local macro "quiet" : tactic =>
  `(tactic| repeat (first
      | (show (_ : List (List (BitVec 8))) = _; rfl)
      | split))

theorem readBy_writes (d : Fate) (s : State) : (readBy d s).world.writes = s.world.writes := by
  simp only [readBy]; quiet
theorem read_writes (s : State) : (read s).world.writes = s.world.writes := by
  simp only [read]; split
  · exact readBy_writes _ _
  · exact readBy_writes _ _
theorem openatIn_writes (s : State) : (openatIn s).world.writes = s.world.writes := by
  simp only [openatIn]; quiet
theorem openat_writes (s : State) : (openat s).world.writes = s.world.writes := by
  simp only [openat]; quiet <;> exact openatIn_writes _
theorem close_writes (s : State) : (close s).world.writes = s.world.writes := by
  simp only [close, closeBy]; quiet
theorem lseek_writes (s : State) : (lseek s).world.writes = s.world.writes := by
  simp only [lseek]; quiet
theorem fsync_writes (s : State) : (fsync s).world.writes = s.world.writes := by
  simp only [fsync, fsyncBy]; quiet
theorem getpid_writes (s : State) : (getpid s).world.writes = s.world.writes := rfl
theorem fstat_writes (s : State) : (fstat s).world.writes = s.world.writes := by
  simp only [fstat]; quiet
theorem clockGettime_writes (s : State) : (clockGettime s).world.writes = s.world.writes := by
  simp only [clockGettime]; quiet
theorem getrandom_writes (s : State) : (getrandom s).world.writes = s.world.writes := by
  simp only [getrandom, grndDeliver]; quiet
theorem mmap_writes (s : State) : (mmap s).world.writes = s.world.writes := by
  simp only [mmap]; quiet
theorem munmap_writes (s : State) : (munmap s).world.writes = s.world.writes := by
  simp only [munmap]; quiet

/-- What a `write` adds to the record of writes: nothing, or the first so
many of the bytes it offered. -/
theorem writeBy_writes (d : Fate) (s : State) :
    (writeBy d s).world.writes = s.world.writes ∨
    ∃ n, n ≤ (s.getReg .rdx).toNat ∧
      (writeBy d s).world.writes = s.loadBytes (s.getReg .rsi) n :: s.world.writes := by
  have hn : taken d (readableRun s (s.getReg .rsi) (min (s.getReg .rdx).toNat 0x7ffff000))
      ≤ (s.getReg .rdx).toNat :=
    Nat.le_trans (taken_le _ _) (Nat.le_trans (readableRun_le _ _ _) (Nat.min_le_left _ _))
  simp only [writeBy]
  repeat (first
    | (refine .inl ?_; show (_ : List (List (BitVec 8))) = _; rfl)
    | exact .inr ⟨_, hn, rfl⟩
    | split)

theorem write_writes (s : State) :
    (write s).world.writes = s.world.writes ∨
    ∃ n, n ≤ (s.getReg .rdx).toNat ∧
      (write s).world.writes = s.loadBytes (s.getReg .rsi) n :: s.world.writes :=
  writeBy_writes (nextFate s).1 (nextFate s).2

end Linux

/-- The first bytes of what is in memory are what is in memory, cut short. -/
theorem State.loadBytes_take (s : State) (a : BitVec 64) {n m : Nat} (h : n ≤ m) :
    s.loadBytes a n = (s.loadBytes a m).take n := by
  simp only [State.loadBytes, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- What one system call adds to the record of writes: nothing, or, being a
`write`, the first so many of the bytes it offered. -/
theorem linux_writes (s : State) :
    (linux s).All (fun t => t.world.writes = s.world.writes ∨
      (s.getReg .rax = 1 ∧ ∃ n, t.world.writes = s.offered.take n :: s.world.writes)) := by
  have ite : ∀ {c : Prop} [Decidable c] {P : State → Prop} {a b : Result State},
      (c → a.All P) → (¬c → b.All P) → (if c then a else b).All P := by
    intro c _ P a b ha hb
    split
    · exact ha ‹_›
    · exact hb ‹_›
  unfold linux
  repeat' (first
    | trivial
    | (show _ ∨ _; refine .inl ?_;
       first
        | exact Linux.read_writes s | exact Linux.mmap_writes s | exact Linux.munmap_writes s
        | exact Linux.close_writes s | exact Linux.fstat_writes s | exact Linux.lseek_writes s
        | exact Linux.clockGettime_writes s | exact Linux.openat_writes s
        | exact Linux.fsync_writes s | exact Linux.getpid_writes s
        | exact Linux.getrandom_writes s | rfl)
    | (refine ite (fun _ => ?_) (fun _ => ?_)))
  next h =>
    show _ ∨ _
    rcases Linux.write_writes s with e | ⟨n, hn, e⟩
    · exact .inl e
    · exact .inr ⟨h, n, by rw [e, State.offered, ← State.loadBytes_take s _ hn]⟩

variable {fetch : Fetch}

/-- What one step adds to the record of writes. -/
theorem step_writes {s t : State} (h : step fetch linux s = .next t) :
    t.world.writes = s.world.writes ∨
    (∃ len, fetch s.rip = some (.syscall, len)) ∧ s.getReg .rax = 1 ∧
      ∃ n, t.world.writes = s.offered.take n :: s.world.writes := by
  unfold step at h
  split at h
  · cases h
  · next i len hf =>
    by_cases hi : i = .syscall
    · subst hi
      have := linux_writes { s with rip := s.rip + len }
      simp only [exec] at h
      rw [h] at this
      rcases this with e | ⟨hax, n, e⟩
      · exact .inl e
      · exact .inr ⟨⟨len, hf⟩, hax, n, e⟩
    · have := exec_world (sys := linux) i { s with rip := s.rip + len } hi
      rw [h] at this
      exact .inl (congrArg World.writes this)

end TypedAsm
