import TypedAsm.U.Whole
import TypedAsm.U.ArgsEntry

/-!
# A whole program started with arguments, checked

The check of a program as written, for one that is started with arguments:
its labels' code is typed, and whatever arguments it is given, the state it
is loaded into starts as its entry asks.
-/

namespace TypedAsm.U
open TypedAsm

variable {L : Type} [DecidableEq L]

/-- The stretch of memory a program started with arguments is given for its
stack. -/
def argStretch : BitVec 64 × BitVec 64 :=
  (argBase - BitVec.ofNat 64 (8 * 0), BitVec.ofNat 64 (8 * 0 + 0x10000))

/-- **The state a program is started in with arguments**: its segments
placed as the kernel places them, the stack given with the arguments on it,
and the instruction pointer at the label it starts at; in any world. -/
def startArgs (code : List (Asm L)) (l : L) (args : List (List Byte)) (w : World) : State :=
  argsState (Asm.load State.init (Asm.base code) code l) (Asm.addr code (Asm.base code) l) args w

/-- **The program's bytes are in memory still once the arguments are
placed**, where they lie below the stack. -/
theorem args_holds {code : List (Asm L)} {l : L}
    (hholds : Loaded.holdsAllE (Asm.imageExt (Asm.base code) code)
      (Asm.partsExt (Asm.base code) code) = true)
    (hhead : Asm.headOkE (Asm.base code) code = true)
    (hbelow : (Asm.partsExt (Asm.base code) code).all
      (fun g => decide (g.1 + g.2.2 ≤ 0x7ffe0000)) = true)
    (args : List (List Byte)) (w : World) :
    ∀ g ∈ Asm.parts (Asm.base code) code, (startArgs code l args w).Holds g := by
  intro g hg k hk
  have hl := Asm.load_holds State.init (Asm.base code) code l hholds hhead g hg k hk
  have hb : g.1 + g.2.2.length ≤ 0x7ffe0000 := by
    rw [← Asm.parts_ext, List.all_map] at hbelow
    exact of_decide_eq_true (List.all_eq_true.mp hbelow g hg)
  have hx : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k).toNat < 0x7ffe0000 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hm : (startArgs code l args w).mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k)
      = (Asm.load State.init (Asm.base code) code l).mem
          (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) :=
    State.mem_withArgs_below _ 0 args (by
      have : argBase.toNat = 0x7fff0000 := rfl
      omega)
  have hp : (startArgs code l args w).perm (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k)
      = (Asm.load State.init (Asm.base code) code l).perm
          (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) :=
    State.perm_withArgs_below _ 0 args (by omega) hx
  rw [hm, hp]
  exact hl

section
variable {B : List (BitVec 64 × Layout)} (args : List (List Byte))

theorem argBlocks_mem {x : BitVec 64 × Layout} (hx : x ∈ argBlocks args) :
    x = (argBase + 8, argvLayout args) ∨
      x = (argBase + BitVec.ofNat 64 (argBytes args).length, restLayout args) := by
  simpa only [argBlocks, List.mem_cons, List.not_mem_nil, or_false] using hx

/-- Where the stack's two blocks are, and how long: after the count, and
within the stack's memory. -/
theorem argBlocks_at {x : BitVec 64 × Layout} (hx : x ∈ argBlocks args) :
    argBase.toNat + 8 ≤ x.1.toNat ∧ x.1.toNat + x.2.size ≤ argBase.toNat + 0x10000 ∧
      0 < x.2.size := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hL := argBytes_length_le args
  have hL' := argBytes_length args
  have hsz := argvLayout_size args
  have hA8 : (argBase + 8).toNat = 0x7fff0008 := rfl
  have hAL : (argBase + BitVec.ofNat 64 (argBytes args).length).toNat
      = 0x7fff0000 + (argBytes args).length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase]
    omega
  have hrest : (restLayout args).size = 0x10000 - (argBytes args).length := by
    simp only [restLayout, Layout.size]
    omega
  rcases argBlocks_mem args hx with rfl | rfl
  · show argBase.toNat + 8 ≤ (argBase + 8).toNat ∧
      (argBase + 8).toNat + (argvLayout args).size ≤ argBase.toNat + 0x10000 ∧
        0 < (argvLayout args).size
    omega
  · show argBase.toNat + 8 ≤ (argBase + BitVec.ofNat 64 (argBytes args).length).toNat ∧
      (argBase + BitVec.ofNat 64 (argBytes args).length).toNat + (restLayout args).size
        ≤ argBase.toNat + 0x10000 ∧ 0 < (restLayout args).size
    omega

/-- No two blocks are at one address: the program's, which lie below the
stack, and the stack's two. -/
theorem nd_args (hnd : B.Pairwise fun x y => x.1 ≠ y.1)
    (hbelow : ∀ x ∈ B, x.1.toNat + x.2.size ≤ argBase.toNat) (hpos : ∀ x ∈ B, 0 < x.2.size) :
    (B ++ argBlocks args).Pairwise fun x y => x.1 ≠ y.1 := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hL := argBytes_length_le args
  have hL' := argBytes_length args
  refine List.pairwise_append.mpr ⟨hnd, ?_, fun x hx y hy he => ?_⟩
  · refine List.pairwise_cons.mpr ⟨fun y hy he => ?_, List.pairwise_singleton _ _⟩
    cases List.mem_singleton.mp hy
    have h1 : (argBase + 8).toNat = 0x7fff0008 := rfl
    have h2 : (argBase + BitVec.ofNat 64 (argBytes args).length).toNat
        = 0x7fff0000 + (argBytes args).length := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase]
      omega
    have := congrArg BitVec.toNat he
    rw [h1, h2] at this
    omega
  · have h1 := hbelow x hx
    have h2 := hpos x hx
    have h3 := (argBlocks_at args hy).1
    rw [he] at h1
    omega

/-- **The program's blocks and the stack's two are well formed together**,
where the program's are, and lie below the stack. -/
theorem wf_args {kinds : Nat → Option Shape} (hwf : (MemTy.ofList B kinds).WF)
    (hnd : B.Pairwise fun x y => x.1 ≠ y.1)
    (hbelow : ∀ x ∈ B, x.1.toNat + x.2.size ≤ argBase.toNat) :
    (MemTy.ofList (B ++ argBlocks args) kinds).WF := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hB : ∀ {a l}, (a, l) ∈ B → MemTy.ofList B kinds a = some l :=
    fun h => MemTy.ofList_of_mem B hnd _ h
  have hsplit : ∀ {a l}, MemTy.ofList (B ++ argBlocks args) kinds a = some l →
      (a, l) ∈ B ∨ (a, l) ∈ argBlocks args :=
    fun h => List.mem_append.mp (MemTy.mem_of_ofList h)
  refine ⟨fun a l hl => ?_, fun a b la lb ha hb hab => ?_, fun a l hl => ?_,
    fun a l hl q hq => ?_, fun a l hl tag ht => ?_, fun a l bs hl hs => ?_⟩
  · rcases hsplit hl with h | h
    · exact hwf.size_lt a l (hB h)
    · have : argBase.toNat + 8 ≤ a.toNat ∧ a.toNat + l.size ≤ argBase.toNat + 0x10000 ∧
          0 < l.size := argBlocks_at args h
      show l.size < 2 ^ 64
      have h2 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
      omega
  · rcases hsplit ha with h1 | h1 <;> rcases hsplit hb with h2 | h2
    · exact hwf.disjoint a b la lb (hB h1) (hB h2) hab
    · have hx : a.toNat + la.size ≤ argBase.toNat := hbelow _ h1
      have hy : argBase.toNat + 8 ≤ b.toNat ∧ b.toNat + lb.size ≤ argBase.toNat + 0x10000 ∧
          0 < lb.size := argBlocks_at args h2
      exact disjoint_of_before (a := a) (n := la.size) (b := b) (m := lb.size) (by omega) (by omega)
    · have hx : b.toNat + lb.size ≤ argBase.toNat := hbelow _ h2
      have hy : argBase.toNat + 8 ≤ a.toNat ∧ a.toNat + la.size ≤ argBase.toNat + 0x10000 ∧
          0 < la.size := argBlocks_at args h1
      exact (disjoint_of_before (a := b) (n := lb.size) (b := a) (m := la.size) (by omega)
        (by omega)).symm
    · have hL := argBytes_length_le args
      have hL' := argBytes_length args
      have hsz := argvLayout_size args
      have hA8 : (argBase + 8).toNat = 0x7fff0008 := rfl
      have hAL : (argBase + BitVec.ofNat 64 (argBytes args).length).toNat
          = 0x7fff0000 + (argBytes args).length := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase]
        omega
      have hrest : (restLayout args).size = 0x10000 - (argBytes args).length := by
        simp only [restLayout, Layout.size]
        omega
      rcases argBlocks_mem args h1 with e1 | e1 <;> rcases argBlocks_mem args h2 with e2 | e2
      · exact absurd (congrArg Prod.fst e1 |>.trans (congrArg Prod.fst e2).symm) hab
      · cases e1; cases e2
        exact disjoint_of_before (a := argBase + 8) (n := (argvLayout args).size)
          (b := argBase + BitVec.ofNat 64 (argBytes args).length) (m := (restLayout args).size)
          (by omega) (by omega)
      · cases e1; cases e2
        exact (disjoint_of_before (a := argBase + 8) (n := (argvLayout args).size)
          (b := argBase + BitVec.ofNat 64 (argBytes args).length) (m := (restLayout args).size)
          (by omega) (by omega)).symm
      · exact absurd (congrArg Prod.fst e1 |>.trans (congrArg Prod.fst e2).symm) hab
  · rcases hsplit hl with h | h
    · exact hwf.nonempty a l (hB h)
    · exact (argBlocks_at args h).2.2
  · rcases hsplit hl with h | h
    · exact hwf.fits a l (hB h) q hq
    · rcases argBlocks_mem args h with e | e
      · cases e
        obtain ⟨i, hi, rfl⟩ := argvVals_spec 0 _ q hq
        show 0 + 8 * i + 8 ≤ 8 * (argsGiven args).length + 32
        omega
      · cases e
        cases hq
  · rcases hsplit hl with h | h
    · exact hwf.kinds a l (hB h) tag ht
    · rcases argBlocks_mem args h with e | e <;> cases e <;> cases ht
  · rcases hsplit hl with h | h
    · exact hwf.said a l bs (hB h) hs
    · rcases argBlocks_mem args h with e | e <;> cases e <;> cases hs

end

end TypedAsm.U
