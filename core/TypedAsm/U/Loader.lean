import TypedAsm.U.Entry

/-!
# All the memory there is, from how a state was built

A program's first state is built from one with no memory by giving
stretches of pages a permission, one after another. So every byte the
machine can touch in it is on a page of one of those stretches; and that
each stretch's pages lie within a region held or a block is then decided by
looking at the stretches. This is how a loaded program's first state is
seen to hold no memory but its blocks and its stack.
-/

namespace TypedAsm.U

open TypedAsm

/-- Every byte the machine can touch is on a page of one of some stretches,
each an address and a length. -/
def PermsWithin (s : State) (rs : List (BitVec 64 × BitVec 64)) : Prop :=
  ∀ a : BitVec 64, s.perm a ≠ .none → ∃ r ∈ rs,
    (State.pagesOf r.1.toNat r.2.toNat).1 ≤ a.toNat / 4096 ∧
      a.toNat / 4096 < (State.pagesOf r.1.toNat r.2.toNat).1 + (State.pagesOf r.1.toNat r.2.toNat).2

/-- The state with no memory. -/
theorem PermsWithin.init : PermsWithin State.init [] := by
  intro a ha
  exact absurd (Perms.get_none a) ha

/-- A stretch given a permission is one more stretch. -/
theorem PermsWithin.setPerm {s : State} {rs : List (BitVec 64 × BitVec 64)} (h : PermsWithin s rs)
    (base len : BitVec 64) (p : Perm) : PermsWithin (s.setPerm base len p) ((base, len) :: rs) := by
  intro a ha
  rw [State.perm_setPerm] at ha
  split at ha
  · next hin => exact ⟨(base, len), List.mem_cons_self, hin.2⟩
  · obtain ⟨r, hr, hlt⟩ := h a ha
    exact ⟨r, List.mem_cons_of_mem _ hr, hlt⟩

/-- A change that touches no permission keeps it so. -/
theorem PermsWithin.congr {s t : State} {rs : List (BitVec 64 × BitVec 64)} (h : PermsWithin s rs)
    (hp : t.perm = s.perm) : PermsWithin t rs := by
  intro a ha
  rw [hp] at ha
  exact h a ha

/-- Whether a stretch's pages lie wholly within one of some ranges of bytes,
each an address and a size; a stretch of no pages does. -/
def stretchIn (cs : List (BitVec 64 × Nat)) (r : BitVec 64 × BitVec 64) : Bool :=
  (State.pagesOf r.1.toNat r.2.toNat).2 == 0 || cs.any fun c =>
    decide (c.1.toNat ≤ 4096 * (State.pagesOf r.1.toNat r.2.toNat).1 ∧
      4096 * ((State.pagesOf r.1.toNat r.2.toNat).1 + (State.pagesOf r.1.toNat r.2.toNat).2)
        ≤ c.1.toNat + c.2)

/-- **Where each stretch's pages lie within one of the ranges, every byte
the machine can touch lies in one of the ranges.** -/
theorem PermsWithin.covered {s : State} {rs : List (BitVec 64 × BitVec 64)}
    (h : PermsWithin s rs) {cs : List (BitVec 64 × Nat)} (hc : rs.all (stretchIn cs) = true)
    {a : BitVec 64} (ha : s.perm a ≠ .none) : ∃ c ∈ cs, (a - c.1).toNat < c.2 := by
  obtain ⟨r, hr, h1, h2⟩ := h a ha
  have := List.all_eq_true.mp hc r hr
  simp only [stretchIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at this
  generalize (State.pagesOf r.1.toNat r.2.toNat).1 = p1 at *
  generalize (State.pagesOf r.1.toNat r.2.toNat).2 = p2 at *
  rcases this with h0 | ⟨c, hcm, h3, h4⟩
  · omega
  · exact ⟨c, hcm, by bv_omega⟩

/-- **All the memory there is, for the entry contract**: every byte the
machine can touch is in a region held or in a block. -/
theorem PermsWithin.complete {s : State} {rs : List (BitVec 64 × BitVec 64)}
    (h : PermsWithin s rs) {blocks : List (BitVec 64 × Layout)} {Γ : Ctx}
    (hc : rs.all (stretchIn (Γ.held.map (fun b => (b.1, b.2.size)) ++
      blocks.map (fun x => (x.1, x.2.size)))) = true) :
    ∀ a : BitVec 64, s.perm a ≠ .none →
      (∃ b ∈ Γ.held, (a - b.1).toNat < b.2.size) ∨
      (∃ x ∈ blocks, (a - x.1).toNat < x.2.size) := by
  intro a ha
  obtain ⟨c, hcm, hlt⟩ := h.covered hc ha
  rcases List.mem_append.mp hcm with hh | hb
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hh
    exact .inl ⟨b, hb, hlt⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact .inr ⟨x, hx, hlt⟩

end TypedAsm.U
