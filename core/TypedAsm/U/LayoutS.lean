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
  /-- Which of the kinds of its family the block is of. -/
  idx : Nat := 0
  text : Nat := 0
  said : Option (List (BitVec 8)) := none

/-- The layout it stands for. -/
def LayoutS.den (l : LayoutS) : Layout :=
  ⟨l.shape.den {}, l.writable, l.tag.map (· * 18446744073709551616 + l.idx), l.text, l.said⟩

/-- How many bytes. -/
def LayoutS.size (l : LayoutS) : Nat := l.shape.size + l.text

/-- The blocks some said blocks stand for. -/
def denBlocks (bs : List (BitVec 64 × LayoutS)) : List (BitVec 64 × Layout) :=
  bs.map fun x => (x.1, x.2.den)

/-- The member of a family of contexts that has one number for every
value. -/
def idxFam (k : Nat) : Fam := { vals := fun _ => BitVec.ofNat 64 k }

/-- The kinds a list of families of kinds stands for, for the memory
typing: each family's kinds are numbered from so many times two to the
sixty-fourth, and each has the family's shape with its own number. -/
def kindsDen (ks : List (Nat × ShapeS)) : Nat → Option Shape :=
  fun t => (ks.lookup (t / 18446744073709551616)).map
    (·.den { bound := [idxFam (t % 18446744073709551616)] })

/-- And for the checker. -/
def kindsOf (ks : List (Nat × ShapeS)) : Nat → Option ShapeS := fun t => ks.lookup t

/-- Whether the shapes of the families mention nothing but the number of
the kind, and each block said to be of a kind has that kind's shape. -/
def kindsCheck (ks : List (Nat × ShapeS)) (bs : List (BitVec 64 × LayoutS)) : Bool :=
  (ks.all fun k => k.2.famGround) &&
    bs.all fun x =>
      match x.2.tag with
      | none => true
      | some t =>
        decide (x.2.idx < 18446744073709551616) &&
          (ks.lookup t).map (·.atIdx (.lit (BitVec.ofNat 64 x.2.idx))) == some x.2.shape

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

/-- The family's member a term gives is the one of the number the term
stands for. -/
theorem famOf_idx (ρ : Env) (n : Val) : famOf ρ (idxOpen n) = idxFam (n.den ρ).toNat := by
  show (⟨fun _ => n.den ρ, _, _⟩ : Fam) = ⟨fun _ => BitVec.ofNat 64 (n.den ρ).toNat, _, _⟩
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- **What the shape of a family, at the number a term stands for, comes
to**: the same whatever else names stand for. -/
theorem ShapeS.atIdx_fam (ρ : Env) (S : ShapeS) {n : Val} (hn : n.closedAt 0 = true)
    (hS : S.famGround = true) :
    (S.atIdx n).den ρ = S.den { bound := [idxFam (n.den ρ).toNat] } := by
  have h1 := ShapeS.den_open ρ (idxOpen n) (idxOpen_closed hn) [] ρ.bound S
  rw [famOf_idx] at h1
  exact h1.trans (ShapeS.den_fam ρ {} _ S hS)

/-- **The kinds the checker is given are the memory typing's.** -/
theorem kindsOk_of_check {ks : List (Nat × ShapeS)} {bs : List (BitVec 64 × LayoutS)}
    (h : kindsCheck ks bs = true) (B : List (BitVec 64 × Layout)) :
    KindsOk (MemTy.ofList B (kindsDen ks)) (kindsOf ks) := by
  intro ρ t Sh n hn hl
  have hg : Sh.famGround = true :=
    List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).1 (t, Sh) (mem_of_lookup hl)
  have hlt := (n.den ρ).isLt
  show (ks.lookup ((t * 18446744073709551616 + (n.den ρ).toNat) / 18446744073709551616)).map _ = _
  rw [show (t * 18446744073709551616 + (n.den ρ).toNat) / 18446744073709551616 = t by omega,
    show (t * 18446744073709551616 + (n.den ρ).toNat) % 18446744073709551616 = (n.den ρ).toNat by
      omega,
    show ks.lookup t = some Sh from hl, Option.map_some, ShapeS.atIdx_fam ρ Sh hn hg]

/-- **Each block said to be of a kind has the kind's shape.** -/
theorem tags_of_check {ks : List (Nat × ShapeS)} {bs : List (BitVec 64 × LayoutS)}
    (h : kindsCheck ks bs = true) :
    ∀ x ∈ denBlocks bs, ∀ t, x.2.tag = some t → kindsDen ks t = some x.2.shape := by
  intro x hx t ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hall := Bool.and_eq_true _ _ |>.mp h
  have := List.all_eq_true.mp hall.2 y hy
  cases hyt : y.2.tag with
  | none =>
    have : (y.2.tag.map (· * 18446744073709551616 + y.2.idx)) = some t := ht
    rw [hyt] at this
    cases this
  | some t' =>
    have ht' : (y.2.tag.map (· * 18446744073709551616 + y.2.idx)) = some t := ht
    rw [hyt] at ht' this
    cases ht'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨hlt, hsh⟩ := this
    cases hk : ks.lookup t' with
    | none => rw [hk] at hsh; cases hsh
    | some T =>
      rw [hk] at hsh
      have hT : T.atIdx (.lit (BitVec.ofNat 64 y.2.idx)) = y.2.shape := Option.some.inj hsh
      have hg : T.famGround = true := List.all_eq_true.mp hall.1 (t', T) (mem_of_lookup hk)
      show (ks.lookup ((t' * 18446744073709551616 + y.2.idx) / 18446744073709551616)).map _
        = some (y.2.shape.den {})
      rw [show (t' * 18446744073709551616 + y.2.idx) / 18446744073709551616 = t' by omega,
        show (t' * 18446744073709551616 + y.2.idx) % 18446744073709551616 = y.2.idx by omega,
        hk, Option.map_some, ← hT, ShapeS.atIdx_fam {} T rfl hg]
      show some (T.den { bound := [idxFam y.2.idx] })
        = some (T.den { bound := [idxFam (BitVec.ofNat 64 y.2.idx).toNat] })
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

end TypedAsm.U
