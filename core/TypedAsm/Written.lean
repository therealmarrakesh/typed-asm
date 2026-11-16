import TypedAsm.Linux
import TypedAsm.Output
import TypedAsm.Encode

/-!
# What a program writes from what it stored

A value the program stores in a block it owns, or on its stack, is exactly
known where the type of the field says so; and its eight bytes in memory are
the bytes of the value, least significant first. So a `write` whose buffer is
a run of such fields offers bytes that are known: the first so many bytes of
those values. These are the rules for that, for the system that lets a
`write` through only where what is offered is as wanted (`Syscall.writesOnly`).
-/

namespace TypedAsm

/-- Eight bytes put together as a value, taken apart again, are the bytes. -/
theorem le64_of_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    le64 (((b7 ++ b6) ++ (b5 ++ b4)) ++ ((b3 ++ b2) ++ (b1 ++ b0)))
      = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [le64, le32, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i hi
     have key : ∀ (b : BitVec 8) (j : Nat), j = i → b.getLsbD j = b[i] := by
       rintro b _ rfl; exact BitVec.getLsbD_eq_getElem _
     simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
     repeat' split
     all_goals first
       | exact key _ _ (by omega)
       | (rw [decide_eq_true (by omega), Bool.true_and]; exact key _ _ (by omega))
       | (exfalso; omega))

/-- The eight bytes in memory at an address are the bytes of the value loaded
from there. -/
theorem State.loadBytes_eight (s : State) (a : BitVec 64) : s.loadBytes a 8 = le64 (s.load64 a) := by
  have e : s.loadBytes a 8 = [s.mem a, s.mem (a + 1), s.mem (a + 2), s.mem (a + 3), s.mem (a + 4),
      s.mem (a + 5), s.mem (a + 6), s.mem (a + 7)] := by
    simp [State.loadBytes, List.range, List.range.loop]
  rw [e]
  have h : s.load64 a = ((s.mem (a + 7) ++ s.mem (a + 6)) ++ (s.mem (a + 5) ++ s.mem (a + 4))) ++
      ((s.mem (a + 3) ++ s.mem (a + 2)) ++ (s.mem (a + 1) ++ s.mem a)) := by
    simp only [State.load64, State.load32, State.load16, State.load8, BitVec.add_assoc]
    rfl
  rw [h, le64_of_bytes]

/-- Bytes in memory, in two runs. -/
theorem State.loadBytes_append (s : State) (a : BitVec 64) (m n : Nat) :
    s.loadBytes a (m + n) = s.loadBytes a m ++ s.loadBytes (a + BitVec.ofNat 64 m) n := by
  simp only [State.loadBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show s.mem (a + BitVec.ofNat 64 (m + i)) = s.mem (a + BitVec.ofNat 64 m + BitVec.ofNat 64 i)
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- **The bytes of consecutive 8-byte fields are the bytes of the values
there**, least significant byte first. -/
theorem State.loadBytes_fields (s : State) : (vs : List (BitVec 64)) → (a : BitVec 64) →
    (∀ i, (h : i < vs.length) → s.load64 (a + BitVec.ofNat 64 (8 * i)) = vs[i]) →
    s.loadBytes a (8 * vs.length) = vs.flatMap le64
  | [], _, _ => rfl
  | v :: vs, a, h => by
    have h0 := h 0 (by simp)
    have z : a + BitVec.ofNat 64 (8 * 0) = a := by simp
    rw [z] at h0
    simp only [List.getElem_cons_zero] at h0
    have e : 8 * (v :: vs).length = 8 + 8 * vs.length := by simp only [List.length_cons]; omega
    rw [e, State.loadBytes_append, State.loadBytes_eight, h0, List.flatMap_cons]
    congr 1
    refine State.loadBytes_fields s vs _ (fun i hi => ?_)
    have := h (i + 1) (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_succ] at this
    rw [← this]
    congr 1
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega

variable {fetch : Fetch} {Ψ : MemTy} {Γ : Ctx}

/-- What a `write` offers, where the buffer is a run of 8-byte fields holding
exactly known values: the first so many bytes of those values. -/
theorem offered_of_fields {s : State} {a cnt : BitVec 64}
    {vs : List (BitVec 64)} (hsi : s.getReg .rsi = a) (hdx : s.getReg .rdx = cnt)
    (hvs : ∀ i, (h : i < vs.length) → s.load64 (a + BitVec.ofNat 64 (8 * i)) = vs[i])
    (hin : cnt.toNat ≤ 8 * vs.length) : s.offered = (vs.flatMap le64).take cnt.toNat := by
  unfold State.offered
  rw [hsi, hdx, State.loadBytes_take s a hin, State.loadBytes_fields s vs a hvs]

/-- **`write` of what the program stored in a block it owns, where only what
satisfies `R` is let through**: the buffer is an exactly known place in the
block, from which 8-byte fields hold exactly known values; the bytes offered
are the first so many bytes of those values, least significant byte first. -/
theorem linux_write_owned_only {sys : Syscall} [LikeLinux sys]
    {R : BitVec 64 → List (BitVec 8) → Prop} {fd a cnt base : BitVec 64} {k off : Nat}
    {S : Shape} {vs : List (BitVec 64)}
    (hΓ : Γ.regs .rax = .eq 1) (hfd : Γ.regs .rdi = .eq fd) (hbuf : Γ.regs .rsi = .eq a)
    (hcnt : Γ.regs .rdx = .eq cnt) (hk : Γ.owned[k]? = some (base, S))
    (ha : a = base + BitVec.ofNat 64 off)
    (hvs : ∀ i, (h : i < vs.length) → (off + 8 * i, Ty.eq vs[i]) ∈ S.vals)
    (hin : cnt.toNat ≤ 8 * vs.length) (hR : R fd ((vs.flatMap le64).take cnt.toNat)) :
    SysReturns fetch (sys.writesOnly R) Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ he hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hdi := h.eqReg (by decide) hfd
  have hsi := h.eqReg (by decide) hbuf
  have hdx := h.eqReg (by decide) hcnt
  have hoff : s.offered = (vs.flatMap le64).take cnt.toNat := by
    refine offered_of_fields hsi hdx (fun i hi => ?_) hin
    have hv := h.owned.vals (base, S) (List.mem_of_getElem? hk) _ (hvs i hi)
    rw [hasTy_eq] at hv
    rw [← hv, ha]
    congr 1
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hgo : (sys.writesOnly R) s = sys s :=
    Syscall.writesOnly_eq (fun _ => by rw [hdi, hoff]; exact hR)
  exact ⟨Linux.write s, hgo.trans (LikeLinux.next (by simp [linux, hax])), (Linux.write_only s).rip,
    Ψ₁, .refl _, hΨ, (Linux.write_only s).ok h⟩

/-- The same for what the program stored on the stack: each field is in a
piece of the stack, which need not be the same piece for all of them, as
after several pushes. -/
theorem linux_write_stack_only {sys : Syscall} [LikeLinux sys]
    {R : BitVec 64 → List (BitVec 8) → Prop} {fd v d cnt : BitVec 64}
    {vs : List (BitVec 64)}
    (hΓ : Γ.regs .rax = .eq 1) (hfd : Γ.regs .rdi = .eq fd) (hsp : Γ.regs .rsp = .eq v)
    (hbuf : Γ.regs .rsi = .eq (v + d)) (hcnt : Γ.regs .rdx = .eq cnt)
    (hvs : ∀ j, (h : j < vs.length) → ∃ k S i,
      StackAt Γ.stack k S (d.toNat + 8 * j) i ∧ (i, Ty.eq vs[j]) ∈ S.vals)
    (hin : cnt.toNat ≤ 8 * vs.length) (hR : R fd ((vs.flatMap le64).take cnt.toNat)) :
    SysReturns fetch (sys.writesOnly R) Ψ Γ Γ.afterSyscall := by
  intro Ψ₁ he hΨ n s h
  have hax := h.eqReg (by decide) hΓ
  have hdi := h.eqReg (by decide) hfd
  have hsi := h.eqReg (by decide) hbuf
  have hdx := h.eqReg (by decide) hcnt
  have hrsp : s.getReg .rsp = v := by
    have := h.sp
    rw [hsp, hasTy_eq] at this
    exact this
  have hoff : s.offered = (vs.flatMap le64).take cnt.toNat := by
    refine offered_of_fields hsi hdx (fun j hj => ?_) hin
    obtain ⟨k, S, i, hat, hm⟩ := hvs j hj
    have hv := h.stack k S hat.entry _ hm
    rw [hasTy_eq] at hv
    rw [← hv, hrsp]
    congr 1
    rw [BitVec.add_assoc]
    congr 1
    rw [← hat.off, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hgo : (sys.writesOnly R) s = sys s :=
    Syscall.writesOnly_eq (fun _ => by rw [hdi, hoff]; exact hR)
  exact ⟨Linux.write s, hgo.trans (LikeLinux.next (by simp [linux, hax])), (Linux.write_only s).rip,
    Ψ₁, .refl _, hΨ, (Linux.write_only s).ok h⟩

end TypedAsm
