import TypedAsm.U.Sys

/-!
# Where a system call may store

A context lets a call store bytes where it holds the region they are in, or
knows a value to point there through a pointer that may be written through,
at bytes that hold no typed value. It is the same finding of bytes that an
instruction's store asks for, with the bytes left unknown.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- Bytes stored change no register, flag or permission; no byte outside
their run; and no eight bytes apart from it. -/
theorem storeBytes_mem_out (s : State) (a x : BitVec 64) (data : List (BitVec 8))
    (hlen : data.length < 2 ^ 64) (h : BitVec.ofNat 64 data.length ≤ x - a) :
    (s.storeBytes a data).mem x = s.mem x := by
  rw [State.mem_storeBytes s a x data (Nat.le_of_lt hlen), List.getElem?_eq_none (by bv_omega)]
  rfl

theorem storeBytes_load64_out (s : State) (a y : BitVec 64) (data : List (BitVec 8))
    (hlen : data.length < 2 ^ 64) (h : Disjoint a data.length y 8) :
    (s.storeBytes a data).load64 y = s.load64 y := by
  by_cases h0 : data.length = 0
  · rw [List.length_eq_zero_iff.mp h0, State.storeBytes_nil]
  · have hd := h.of_pos h0 (by decide)
    exact State.load64_storeBytes_disjoint s data hlen hd.1 hd.2

/-- **A call may store in a region the context holds**: the region then
holds no value the bytes reach into. -/
theorem Havoc.held {Γ : Ctx} {k : Nat} {b : BitVec 64} {S : Held} {o n : Nat}
    (hk : Γ.held[k]? = some (b, S)) (hin : o + n ≤ S.size) (hrows : Γ.rows = []) :
    Havoc fetch sys Ψ Γ (b + BitVec.ofNat 64 o) n
      { Γ with held := Γ.held.set k (b, S.clear o n) } := by
  refine ⟨rfl, rfl, fun j Ψ' he hwf s hw data hlen _ => ?_⟩
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hmem : (b, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hsz := hw.held.size_lt _ hmem
  simp only at hsz
  have hl : data.length < 2 ^ 64 := by omega
  refine hw.writeHeld hwf hk (lo := o) (cnt := data.length) (by omega) rfl ?_ rfl rfl rfl
    (fun y hy => storeBytes_load64_out _ _ _ _ hl hy)
    (fun x hx => storeBytes_mem_out _ _ _ _ hl hx) ?_
    (by rw [hrows]; exact fun r hr => nomatch hr)
    (by rw [hrows]; exact fun r hr => nomatch hr)
  · intro p hp
    simp only [ShapeOf.clear, List.mem_filter] at hp
    exact hw.held.fits _ hmem p hp.1
  · intro p hp
    simp only [ShapeOf.clear, List.mem_filter, ShapeOf.clearOf, Bool.or_eq_true,
      decide_eq_true_eq] at hp
    exact .inl ⟨hp.1, by omega⟩

/-- **And the region then described anew**: by any values that were there
and keep clear of the bytes. So of a region whose values are found to keep
clear by what is known, which may be fewer than those that do. -/
theorem Havoc.heldTo {Γ : Ctx} {k : Nat} {b : BitVec 64} {S S' : Held} {o n : Nat}
    (hk : Γ.held[k]? = some (b, S)) (hin : o + n ≤ S.size) (hS' : S'.size = S.size)
    (hvals : ∀ p ∈ S'.vals, p ∈ S.vals ∧ (p.1 + 8 ≤ o ∨ o + n ≤ p.1)) (hrows : Γ.rows = []) :
    Havoc fetch sys Ψ Γ (b + BitVec.ofNat 64 o) n
      { Γ with held := Γ.held.set k (b, S') } := by
  refine ⟨rfl, rfl, fun j Ψ' he hwf s hw data hlen _ => ?_⟩
  obtain ⟨hklt, hkeq⟩ := List.getElem?_eq_some_iff.mp hk
  have hmem : (b, S) ∈ Γ.held := hkeq ▸ List.getElem_mem hklt
  have hsz := hw.held.size_lt _ hmem
  simp only at hsz
  have hl : data.length < 2 ^ 64 := by omega
  refine hw.writeHeld (S' := S') hwf hk (lo := o) (cnt := data.length) (by omega) hS' ?_
    rfl rfl rfl
    (fun y hy => storeBytes_load64_out _ _ _ _ hl hy)
    (fun x hx => storeBytes_mem_out _ _ _ _ hl hx) ?_
    (by rw [hrows]; exact fun r hr => nomatch hr)
    (by rw [hrows]; exact fun r hr => nomatch hr)
  · intro p hp
    rw [hS']
    exact hw.held.fits _ hmem p (hvals p hp).1
  · intro p hp
    have := hvals p hp
    exact .inl ⟨this.1, by omega⟩

/-- **And in a block a value is known to point into**, through a pointer
that may be written through, at bytes that hold no typed value: the context
is as it was. -/
theorem Havoc.shared {Γ : Ctx} {p a : BitVec 64} {τ : Ty} {Sh : Shape} {off o n : Nat}
    (hf : (p, τ) ∈ Γ.known) (hτ : τ.pointee Ψ.kinds = some (Sh, true, off))
    (ha : a + BitVec.ofNat 64 off = p + BitVec.ofNat 64 o) (hin : o + n ≤ Sh.size)
    (hfree : Sh.free o n = true) (hrows : Γ.rows = []) : Havoc fetch sys Ψ Γ a n Γ := by
  refine ⟨rfl, rfl, fun j Ψ' he hwf s hw data hlen _ => ?_⟩
  obtain ⟨base, l, hl, hsh, hlw, hp⟩ :=
    hasTy_pointee hwf (by rw [he.kinds]; exact hτ) (hw.known _ hf)
  subst hsh
  have hab : a = base + BitVec.ofNat 64 o := by bv_omega
  subst hab
  have hsz := hwf.size_lt base l hl
  have hl' : data.length < 2 ^ 64 := by simp only [Layout.size] at hsz; omega
  refine hw.writeShared hwf hl (hlw rfl) (lo := o) (cnt := data.length) (by omega) rfl rfl rfl
    (fun y hy => storeBytes_load64_out _ _ _ _ hl' hy)
    (fun x hx => storeBytes_mem_out _ _ _ _ hl' hx) (fun q hq => ?_)
    (by rw [hrows]; exact fun r hr => nomatch hr)
    (by rw [hrows]; exact fun r hr => nomatch hr)
  have := List.all_eq_true.mp hfree q hq
  simp only [ShapeOf.clearOf, Bool.or_eq_true, decide_eq_true_eq] at this
  exact .inl (by omega)

end TypedAsm.U
