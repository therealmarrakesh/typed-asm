import TypedAsm.Step

/-!
# Finding an instruction quickly

A program's instruction table is a list of its instructions, each with its
address, walked until the address asked for is met: `Lookup.first`. That is
the right definition and a poor way to compute: checking a typing looks up
every instruction, and each lookup walks past all the ones before.

`Lookup` is the same table as a search tree keyed by address. A tree is
written out for a program by the tactics, and `Lookup.sound` shows that it
answers as the list does, given two facts that are settled by computing
once for the program. After that a lookup costs a few comparisons of
numbers.
-/

namespace TypedAsm

/-- An instruction table as a search tree: one instruction at an address, or
two tables with every address below `mid` in the first and the rest in the
second. -/
inductive Lookup where
  | none
  | leaf (a : Nat) (i : Instr) (len : BitVec 64)
  | node (l : Lookup) (mid : Nat) (r : Lookup)

namespace Lookup

/-- The instruction at an address, and its length. -/
def find : Lookup → Nat → Option (Instr × BitVec 64)
  | .none, _ => Option.none
  | .leaf a i len, x => if x = a then some (i, len) else Option.none
  | .node l mid r, x => if x < mid then l.find x else r.find x

/-- The instructions in order, each with its address. -/
def toList : Lookup → List (Nat × Instr × BitVec 64)
  | .none => []
  | .leaf a i len => [(a, i, len)]
  | .node l _ r => l.toList ++ r.toList

/-- Whether the tree is a search tree for addresses from `lo` up to `hi`. -/
def ok : Lookup → Nat → Nat → Bool
  | .none, _, _ => true
  | .leaf a _ _, lo, hi => decide (lo ≤ a) && decide (a < hi)
  | .node l mid r, lo, hi => decide (lo ≤ mid) && decide (mid ≤ hi) && l.ok lo mid && r.ok mid hi

/-- The first instruction listed at an address. -/
def first : List (Nat × Instr × BitVec 64) → Nat → Option (Instr × BitVec 64)
  | [], _ => Option.none
  | (a, i, len) :: rest, x => if x = a then some (i, len) else first rest x

theorem first_append_left {xs ys : List (Nat × Instr × BitVec 64)} {x : Nat}
    (h : ∀ e ∈ ys, e.1 ≠ x) : first (xs ++ ys) x = first xs x := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons e rest ih =>
      obtain ⟨a, i, len⟩ := e
      have hne : x ≠ a := fun hx => h (a, i, len) List.mem_cons_self hx.symm
      simp only [List.nil_append, first, hne, ↓reduceIte] at ih ⊢
      exact ih fun e he => h e (List.mem_cons_of_mem _ he)
  | cons e rest ih =>
    obtain ⟨a, i, len⟩ := e
    simp only [List.cons_append, first]
    split
    · rfl
    · exact ih

theorem first_append_right {xs ys : List (Nat × Instr × BitVec 64)} {x : Nat}
    (h : ∀ e ∈ xs, e.1 ≠ x) : first (xs ++ ys) x = first ys x := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨a, i, len⟩ := e
    have hne : x ≠ a := fun hx => h (a, i, len) List.mem_cons_self hx.symm
    simp only [List.cons_append, first, hne, ↓reduceIte]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- Every address in a search tree lies within its bounds. -/
theorem mem_bounds {t : Lookup} {lo hi : Nat} (h : t.ok lo hi = true) :
    ∀ e ∈ t.toList, lo ≤ e.1 ∧ e.1 < hi := by
  induction t generalizing lo hi with
  | none => intro e he; cases he
  | leaf a i len =>
    intro e he
    simp only [toList, List.mem_singleton] at he
    subst he
    simpa [ok] using h
  | node l mid r ihl ihr =>
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hlo, hhi⟩, hl⟩, hr⟩ := h
    intro e he
    simp only [toList, List.mem_append] at he
    rcases he with he | he
    · have := ihl hl e he
      omega
    · have := ihr hr e he
      omega

/-- A search tree finds what a walk along its instructions finds. -/
theorem find_eq_first {t : Lookup} {lo hi : Nat} (h : t.ok lo hi = true) (x : Nat) :
    t.find x = first t.toList x := by
  induction t generalizing lo hi with
  | none => rfl
  | leaf a i len => rfl
  | node l mid r ihl ihr =>
    have h' := h
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨-, hl⟩, hr⟩ := h'
    simp only [find, toList]
    split
    · next hx =>
      rw [ihl hl, first_append_left]
      intro e he
      have := mem_bounds hr e he
      omega
    · next hx =>
      rw [ihr hr, first_append_right]
      intro e he
      have := mem_bounds hl e he
      omega

/-- What a walk finds at an address is listed there. -/
theorem first_mem {xs : List (Nat × Instr × BitVec 64)} {x : Nat} {v : Instr × BitVec 64}
    (h : first xs x = some v) : (x, v) ∈ xs := by
  induction xs with
  | nil => cases h
  | cons e rest ih =>
    obtain ⟨a, i, len⟩ := e
    simp only [first] at h
    split at h
    · next hx =>
      cases h
      subst hx
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- **A search tree written out for a list of instructions with their
addresses finds what a walk along the list finds**, if it is a search tree
and lists those instructions. Both are settled by computing. -/
theorem sound {xs : List (Nat × Instr × BitVec 64)} {t : Lookup}
    (hok : t.ok 0 (2 ^ 64) = true) (hlist : t.toList = xs) :
    (fun a : BitVec 64 => first xs a.toNat) = fun a => t.find a.toNat :=
  funext fun a => by rw [find_eq_first hok, hlist]

end Lookup

end TypedAsm
