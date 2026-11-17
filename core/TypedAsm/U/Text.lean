import TypedAsm.U.Shared

/-!
# Text

A block's text is bytes after its typed part, the last of them nought. A
pointer to text may be read through, a byte at a time. The byte read says
whether there is more: the last byte is nought, so where the byte read is
not nought the pointer is not at the last. And where there is more, the
address one on is a pointer to text again.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- **A byte of text, read through a pointer to it**: of the pointer it is
then known that there is more unless the byte read is nought. -/
theorem Reads.text {Γ : Ctx} {p c : BitVec 64} (hf : (p, Ty.str c) ∈ Γ.known) :
    Reads fetch sys Ψ Γ p 1 (fun x Γr => Γr = { Γ with known := [(p, .str x)] ++ Γ.known }) := by
  intro j Ψ' he hwf s hw
  obtain ⟨a, l, off, hl, hoff, _, rfl⟩ := hasTy_str.mp (hw.known _ hf)
  have hsub : (l.shape.size + off) + 1 ≤ l.size := by simp only [Layout.size]; omega
  refine ⟨State.canRead_sub (hw.heapPerm a l hl).1 hsub, _, rfl, rfl, rfl, ?_⟩
  refine hw.addKnown _ (fun f hf' => ?_)
  cases List.mem_singleton.mp hf'
  refine hasTy_str.mpr ⟨a, l, off, hl, hoff, fun hx => ?_, rfl⟩
  refine Decidable.byContradiction fun hlt => hx ?_
  have h0 := hw.text a l hl (by omega)
  have hlast : l.size - 1 = l.shape.size + off := by simp only [Layout.size]; omega
  rw [hlast] at h0
  show (s.load8 _).setWidth 64 = 0
  unfold State.load8
  rw [h0]
  rfl

/-- **Where there is more text, the address one on is a pointer to text.** -/
theorem hasTy_str_succ {n : Nat} {c v : BitVec 64} (h : HasTy fetch sys Ψ n (.str c) v)
    (hc : c ≠ 0) : HasTy fetch sys Ψ n (.str 0) (v + 1) := by
  obtain ⟨a, l, off, hl, _, hmore, rfl⟩ := hasTy_str.mp h
  refine hasTy_str.mpr ⟨a, l, off + 1, hl, hmore hc, fun h0 => absurd rfl h0, ?_⟩
  have e : BitVec.ofNat 64 (l.shape.size + (off + 1))
      = BitVec.ofNat 64 (l.shape.size + off) + 1 := by
    rw [← Nat.add_assoc, BitVec.ofNat_add]
    rfl
  rw [e, BitVec.add_assoc]

end TypedAsm.U
