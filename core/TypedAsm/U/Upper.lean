import TypedAsm.U.Learn

/-!
# How large a value may be

An amount a program computes with is often known only by its range: an
index it has compared against a bound, a count a call handed back. Here is
the most a value can be, as a number without sign, read off its term: a
number written out is itself; a value known to lie in a range that does
not wrap, or whose operator bounds it, is at most the range's top; a sum is
at most the sum; a value shifted left is at most so many times as much.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

/-- The top of a range that does not wrap. -/
def Range.top (r : Range) : Option Nat := if r.lo ≤ r.hi then some r.hi.toNat else none

theorem Range.top_has {r : Range} {m : Nat} (h : r.top = some m) {v : BitVec 64} (hv : r.has v) :
    v.toNat ≤ m := by
  unfold Range.top at h
  split at h
  · next hle =>
    cases h
    simp only [Range.has] at hv
    bv_omega
  · cases h

/-- The top of the first range a context knows a value to lie in that does
not wrap. -/
def CtxS.knownTop (Γ : CtxS) (v : Val) : Option Nat :=
  Γ.known.findSome? fun g =>
    if g.1.same v then
      match g.2 with
      | .range lo hi => Range.top ⟨lo, hi⟩
      | _ => none
    else none

theorem CtxS.knownTop_le {ρ : Env} {Γ : CtxS} {v : Val} {m : Nat} (h : Γ.knownTop v = some m)
    {Ψ' : MemTy} {n : Nat} (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    (v.den ρ).toNat ≤ m := by
  obtain ⟨g, hgm, hsome⟩ := List.exists_of_findSome?_eq_some h
  split at hsome
  · next hs =>
    have hT := hg (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩)
    cases hτ : g.2 with
    | range lo hi =>
      rw [hτ] at hsome hT
      rw [← Val.same_den ρ hs]
      exact Range.top_has hsome (hasTy_range.mp hT)
    | _ => rw [hτ] at hsome; cases hsome
  · cases hsome

/-- What a value is at most, by what is known of it or by its operator. -/
def CtxS.leafTop (Γ : CtxS) (v : Val) : Option Nat :=
  match Γ.knownTop v with
  | some m => some m
  | none => v.bound.top

theorem CtxS.leafTop_le {ρ : Env} {Γ : CtxS} {v : Val} {m : Nat} (h : Γ.leafTop v = some m)
    {Ψ' : MemTy} {n : Nat} (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    (v.den ρ).toNat ≤ m := by
  unfold CtxS.leafTop at h
  split at h
  · next m' hk => cases h; exact CtxS.knownTop_le hk hg
  · exact Range.top_has h (Val.bound_has ρ v)

/-- The lesser of two bounds, where there are two. -/
def lesser : Option Nat → Option Nat → Option Nat
  | some x, some y => some (min x y)
  | some x, none => some x
  | none, y => y

theorem lesser_le {x y : Option Nat} {m v : Nat} (h : lesser x y = some m)
    (hx : ∀ a, x = some a → v ≤ a) (hy : ∀ b, y = some b → v ≤ b) : v ≤ m := by
  cases x with
  | none => exact hy m h
  | some a =>
    cases y with
    | none => cases h; exact hx _ rfl
    | some b =>
      cases h
      exact Nat.le_min.mpr ⟨hx a rfl, hy b rfl⟩

/-- **The most a value can be**, as a number without sign: by what is known
of it or its operator; and, of a sum or a value shifted left, by its parts
too. -/
def CtxS.upper (Γ : CtxS) : Val → Option Nat
  | .lit v => some v.toNat
  | .bin .add a b =>
    lesser (Γ.leafTop (.bin .add a b))
      (match Γ.upper a, Γ.upper b with
       | some x, some y => some (x + y)
       | _, _ => none)
  | .un (.shl k) a =>
    lesser (Γ.leafTop (.un (.shl k) a))
      (match Γ.upper a with
       | some x => some (x <<< k)
       | none => none)
  | v => Γ.leafTop v

theorem CtxS.upper_le {ρ : Env} {Γ : CtxS} {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    (v : Val) → {m : Nat} → Γ.upper v = some m → (v.den ρ).toNat ≤ m
  | .lit v, m, h => by cases h; exact Nat.le_refl _
  | .bin .add a b, m, h => by
    simp only [CtxS.upper] at h
    refine lesser_le h (fun _ hl => CtxS.leafTop_le hl hg) (fun m' hm => ?_)
    split at hm
    · next x y hx hy =>
      cases hm
      have ha := CtxS.upper_le hg a hx
      have hb := CtxS.upper_le hg b hy
      show (a.den ρ + b.den ρ).toNat ≤ x + y
      rw [BitVec.toNat_add]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add ha hb)
    · cases hm
  | .un (.shl k) a, m, h => by
    simp only [CtxS.upper] at h
    refine lesser_le h (fun _ hl => CtxS.leafTop_le hl hg) (fun m' hm => ?_)
    split at hm
    · next x hx =>
      cases hm
      have ha := CtxS.upper_le hg a hx
      show (a.den ρ <<< k).toNat ≤ x <<< k
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.mul_le_mul_right _ ha)
    · cases hm
  | .var i, m, h => CtxS.leafTop_le h hg
  | .bvar d i, m, h => CtxS.leafTop_le h hg
  | .slot s, m, h => CtxS.leafTop_le h hg
  | .bin (.shift op w) a b, m, h => CtxS.leafTop_le h hg
  | .bin (.imul w) a b, m, h => CtxS.leafTop_le h hg
  | .tri o a b c, m, h => CtxS.leafTop_le h hg
  | .fop o fl a b, m, h => CtxS.leafTop_le h hg
  | .un (.neg w) a, m, h => CtxS.leafTop_le h hg
  | .un (.not w) a, m, h => CtxS.leafTop_le h hg
  | .un (.popcnt w) a, m, h => CtxS.leafTop_le h hg
  | .un (.bswap w) a, m, h => CtxS.leafTop_le h hg
  | .un (.signFill w) a, m, h => CtxS.leafTop_le h hg
  | .un (.trunc w) a, m, h => CtxS.leafTop_le h hg
  | .un (.zx w sw) a, m, h => CtxS.leafTop_le h hg
  | .un (.sx w sw) a, m, h => CtxS.leafTop_le h hg
  | .un .sxd a, m, h => CtxS.leafTop_le h hg
  | .un .low8 a, m, h => CtxS.leafTop_le h hg
  | .un .low16 a, m, h => CtxS.leafTop_le h hg

end TypedAsm.U
