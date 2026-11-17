import Lean

/-!
# Two sets of rewriting rules

The rules that unfold the machine's step and an instruction's description,
on operands written out: for an instruction that goes on to the next, and
for one that passes control elsewhere. They are named sets, so that a proof
names the set and not its sixty members.
-/

/-- Unfolds the machine's step and a description's. -/
register_simp_attr desc_unfold

/-- The same, for an instruction that passes control elsewhere. -/
register_simp_attr goes_unfold
