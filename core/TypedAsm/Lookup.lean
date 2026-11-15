import TypedAsm.Step

/-!
# Finding an instruction quickly

A program's instruction table, `Fetch.layout`, is a list walked from the
program's base, adding up lengths until the address asked for is reached.
That is the right definition and a poor way to compute: checking a typing
looks up every instruction, and each lookup walks past all the ones before.

`Lookup` is the same table as a search tree keyed by address. A tree is
written out for a program by the tactics, and `Lookup.sound` shows that it
answers as the list does, given three facts that are settled by computing
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

/-- A program's instructions with the address of each, counted up from the
base as plain numbers. -/
def addrs : Nat → List (Instr × BitVec 64) → List (Nat × Instr × BitVec 64)
  | _, [] => []
  | b, (i, len) :: rest => (b, i, len) :: addrs (b + len.toNat) rest

/-- The length of a program in bytes. -/
def total : List (Instr × BitVec 64) → Nat
  | [] => 0
  | (_, len) :: rest => len.toNat + total rest

/-- For a program that ends before the address space does, the table finds
what a walk along the instructions with their addresses finds. -/
theorem layout_eq_first (items : List (Instr × BitVec 64)) (base a : BitVec 64)
    (h : base.toNat + total items < 2 ^ 64) :
    Fetch.layout base items a = first (addrs base.toNat items) a.toNat := by
  induction items generalizing base with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨i, len⟩ := p
    simp only [total] at h
    simp only [Fetch.layout, addrs, first]
    have hadd : (base + len).toNat = base.toNat + len.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    by_cases hab : a = base
    · subst hab
      simp
    · have hne : a.toNat ≠ base.toNat := fun h => hab (BitVec.eq_of_toNat_eq h)
      simp only [hab, hne, ↓reduceIte]
      rw [ih (base + len) (by rw [hadd]; omega), hadd]

/-- **A search tree written out for a program is the program's instruction
table**, if it is a search tree, lists the program's instructions at their
addresses, and the program ends before the address space does. All three are
settled by computing. -/
theorem sound {base : BitVec 64} {items : List (Instr × BitVec 64)} {t : Lookup}
    (hok : t.ok 0 (2 ^ 64) = true) (hlist : t.toList = addrs base.toNat items)
    (hfit : decide (base.toNat + total items < 2 ^ 64) = true) :
    Fetch.layout base items = fun a => t.find a.toNat :=
  funext fun a => by
    rw [layout_eq_first items base a (of_decide_eq_true hfit), find_eq_first hok, hlist]

end Lookup

end TypedAsm
