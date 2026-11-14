import TypedAsm.Step

/-!
# What an instruction can change in memory

`Frame s s'` says that going from `s` to `s'` changed no permission and no
byte that was not writable. Every instruction satisfies it, so code, which
is never writable, is never changed.
-/

namespace TypedAsm

/-- No permission changed, and no byte that was not writable changed. -/
structure Frame (s s' : State) : Prop where
  perm : s'.perm = s.perm
  mem : ∀ x, (s.perm x).writable = false → s'.mem x = s.mem x

namespace Frame

theorem refl (s : State) : Frame s s :=
  ⟨rfl, fun _ _ => rfl⟩

theorem trans {s t u : State} (h₁ : Frame s t) (h₂ : Frame t u) : Frame s u :=
  ⟨h₂.perm.trans h₁.perm, fun x hx => (h₂.mem x (by rw [h₁.perm]; exact hx)).trans (h₁.mem x hx)⟩

/-- A state with the same memory and permissions. -/
theorem of_eq {s s' : State} (hm : s'.mem = s.mem) (hp : s'.perm = s.perm) : Frame s s' :=
  ⟨hp, fun x _ => by rw [hm]⟩

/-- Changing only registers, flags or `rip` afterwards. -/
theorem congr {s t t' : State} (h : Frame s t) (hm : t'.mem = t.mem) (hp : t'.perm = t.perm) :
    Frame s t' :=
  h.trans (of_eq hm hp)

end Frame

namespace State

/-- A byte that is not writable is outside any writable range. -/
theorem outside_of_not_writable {s : State} {a x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64)
    (hc : s.canWrite a n = true) (hx : (s.perm x).writable = false) :
    BitVec.ofNat 64 n ≤ x - a := by
  rw [canWrite, List.all_eq_true] at hc
  apply Classical.byContradiction
  intro hlt
  have hj : (x - a).toNat < n := by bv_omega
  have := hc (x - a).toNat (List.mem_range.mpr hj)
  have e : a + BitVec.ofNat 64 (x - a).toNat = x := by bv_omega
  rw [e, hx] at this
  cases this

theorem write_frame (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    (s.write w a v).All (Frame s) := by
  unfold write
  split
  · next hc =>
    refine ⟨perm_store s w a v, fun x hx => mem_store_of_disjoint s w a x v ?_⟩
    have := outside_of_not_writable (n := w.bytes.toNat) (by cases w <;> decide) hc hx
    cases w <;> simpa [Width.bytes] using this
  · trivial

theorem write64_frame (s : State) (a v : BitVec 64) : (s.write64 a v).All (Frame s) := by
  unfold write64
  split
  · next hc =>
    refine ⟨perm_store s .w64 a v, fun x hx => mem_store_of_disjoint s .w64 a x v ?_⟩
    exact outside_of_not_writable (by decide) hc hx
  · trivial

theorem write8_frame (s : State) (a : BitVec 64) (v : BitVec 8) : (s.write8 a v).All (Frame s) := by
  unfold write8
  split
  · next hc =>
    refine ⟨rfl, fun x hx => ?_⟩
    have h := outside_of_not_writable (n := 1) (by decide) hc hx
    have hne : x ≠ a := by
      intro e; subst e; simp at h
    simp only [store8, hne, ite_false]
  · trivial

theorem writeRM_frame (s : State) (w : Width) (dst : RM) (v : BitVec w.bits) :
    (s.writeRM w dst v).All (Frame s) := by
  cases dst with
  | reg r => exact Frame.of_eq rfl rfl
  | mem m => exact write_frame s w _ v

theorem writeRM8_frame (s : State) (dst : RM) (v : BitVec 8) : (s.writeRM8 dst v).All (Frame s) := by
  cases dst with
  | reg r => exact Frame.of_eq rfl rfl
  | mem m => exact write8_frame s _ v

theorem push64_frame (s : State) (v : BitVec 64) : (s.push64 v).All (Frame s) :=
  (write64_frame (s.setReg .rsp (s.getReg .rsp - 8)) _ v).mono
    (fun _ h =>
      (Frame.of_eq (s := s) (s' := s.setReg .rsp (s.getReg .rsp - 8)) rfl rfl).trans h)

theorem pop64_frame (s : State) : (s.pop64).All (fun p => Frame s p.2) := by
  simp only [pop64, Result.all_bind, Result.all_pure]
  exact Result.All.of_forall (fun _ => Frame.of_eq rfl rfl)

end State

/-- Works through the steps of an instruction: a read constrains nothing, a
write is covered by its own lemma, and what follows a write only changes
registers, flags or `rip`. -/
macro "frame_steps" : tactic =>
  `(tactic| repeat (first
      | exact Frame.of_eq rfl rfl
      | exact State.writeRM_frame _ _ _ _
      | exact State.writeRM8_frame _ _ _
      | exact State.write8_frame _ _ _
      | exact State.push64_frame _ _
      | (refine Result.All.mono (State.writeRM_frame _ _ _ _) ?_; intro _ hF; exact hF.congr rfl rfl)
      | (refine Result.All.mono (State.writeRM8_frame _ _ _) ?_; intro _ hF; exact hF.congr rfl rfl)
      | (refine Result.All.mono (State.push64_frame _ _) ?_; intro _ hF; exact hF.congr rfl rfl)
      | (refine Result.All.mono (State.pop64_frame _) ?_; intro _ hF; exact hF.congr rfl rfl)
      | simp only [Result.all_bind, Result.all_pure, Result.all_next, Result.all_fault,
          Result.all_stuck]
      | split
      | (apply Result.All.of_forall; intro _)))

/-- **No instruction changes a permission or a byte that is not writable.**
A system call is covered by the assumption that the operating system does not. -/
theorem exec_frame {sys : Syscall} (hsys : ∀ s, (sys s).All (Frame s)) (i : Instr) (s : State) :
    (exec sys i s).All (Frame s) := by
  cases i with
  | syscall => exact hsys s
  | ud2 => trivial
  | unary op w dst => cases op <;> (simp only [exec]; frame_steps)
  | jmp t => cases t <;> (simp only [exec]; frame_steps)
  | _ => simp only [exec]; frame_steps

end TypedAsm
