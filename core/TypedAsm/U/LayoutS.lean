import TypedAsm.U.Ground
import TypedAsm.U.Entry
import TypedAsm.U.FindFact

/-!
# Blocks and kinds as a program says them

A program says its first blocks and its kinds of block as data: shapes
written out, mentioning nothing. What they stand for is the memory typing
the program starts under.
-/

namespace TypedAsm.U

open TypedAsm

/-- The layout of a block, as data. -/
structure LayoutS where
  shape : ShapeS
  writable : Bool
  tag : Option Nat := none
  text : Nat := 0
  said : Option (List (BitVec 8)) := none

/-- The layout it stands for. -/
def LayoutS.den (l : LayoutS) : Layout := ⟨l.shape.den {}, l.writable, l.tag, l.text, l.said⟩

/-- How many bytes. -/
def LayoutS.size (l : LayoutS) : Nat := l.shape.size + l.text

/-- The blocks some said blocks stand for. -/
def denBlocks (bs : List (BitVec 64 × LayoutS)) : List (BitVec 64 × Layout) :=
  bs.map fun x => (x.1, x.2.den)

/-- The kinds a list of kinds stands for, for the memory typing. -/
def kindsDen (ks : List (Nat × ShapeS)) : Nat → Option Shape :=
  fun t => (ks.lookup t).map (·.den {})

/-- And for the checker. -/
def kindsOf (ks : List (Nat × ShapeS)) : Nat → Option ShapeS := fun t => ks.lookup t

/-- Whether the kinds mention nothing, and each block said to be of a kind
has that kind's shape. -/
def kindsCheck (ks : List (Nat × ShapeS)) (bs : List (BitVec 64 × LayoutS)) : Bool :=
  (ks.all fun k => k.2.ground) &&
    bs.all fun x =>
      match x.2.tag with
      | none => true
      | some t => ks.lookup t == some x.2.shape

theorem mem_of_lookup {ks : List (Nat × ShapeS)} {t : Nat} {Sh : ShapeS} :
    ks.lookup t = some Sh → (t, Sh) ∈ ks := by
  induction ks with
  | nil => intro h; cases h
  | cons k ks ih =>
    obtain ⟨a, b⟩ := k
    intro h
    rw [List.lookup_cons] at h
    split at h
    · next he =>
      cases h
      rw [beq_iff_eq.mp he]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- **The kinds the checker is given are the memory typing's.** -/
theorem kindsOk_of_check {ks : List (Nat × ShapeS)} {bs : List (BitVec 64 × LayoutS)}
    (h : kindsCheck ks bs = true) (B : List (BitVec 64 × Layout)) :
    KindsOk (MemTy.ofList B (kindsDen ks)) (kindsOf ks) := by
  intro ρ t Sh hl
  have hg : Sh.ground = true :=
    List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).1 (t, Sh) (mem_of_lookup hl)
  show (ks.lookup t).map (·.den {}) = some (Sh.den ρ)
  rw [show ks.lookup t = some Sh from hl, Option.map_some, ShapeS.den_ground {} ρ Sh hg]

/-- **Each block said to be of a kind has the kind's shape.** -/
theorem tags_of_check {ks : List (Nat × ShapeS)} {bs : List (BitVec 64 × LayoutS)}
    (h : kindsCheck ks bs = true) :
    ∀ x ∈ denBlocks bs, ∀ t, x.2.tag = some t → kindsDen ks t = some x.2.shape := by
  intro x hx t ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have := List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).2 y hy
  have ht' : y.2.tag = some t := ht
  rw [ht'] at this
  show (ks.lookup t).map (·.den {}) = some (y.2.shape.den {})
  rw [beq_iff_eq.mp this, Option.map_some]

end TypedAsm.U
