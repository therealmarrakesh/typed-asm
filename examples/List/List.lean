import ListProgram
import TypedAsm.Tactic

/-!
# List: typing and safety

The program is in `ListProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace List3

/-! ## The typing -/

/-- What a node's link holds: zero, or the address of a node. Nodes are the
blocks of kind 1. -/
def link : Ty := .nullable (.ref 1 false 0)

/-- A node: a value and a link. -/
def nodeFields : List Ty := [.int, link]

def nodeLayout : Layout := ⟨nodeFields, false, some 1, 0⟩

/-- In the loop `rdi` holds a link. -/
def walking : Ctx := ⟨fun r => if r = .rdi then link else .int, [], 0, Flags.Any, []⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | loop : At .loop walking
  | done : At .done (entryCtx 0)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- Three memory blocks, one for each node. -/
def blocks : List (BitVec 64 × Layout) :=
  [(dataBase, nodeLayout), (dataBase + 16, nodeLayout), (dataBase + 32, nodeLayout)]

/-- The blocks, and the one kind of block there is: kind 1 is a node. -/
def Ψ : MemTy := .ofList blocks [(1, nodeFields)]

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + list]
    ty_step
    -- `rdi` holds exactly the first node's address, so it points to a node
    refine BlockOk.castRef (r := .rdi) (base := dataBase) (i := 0) (w := false) (tag := 1)
      (by decide) rfl rfl rfl rfl (fun h => absurd h (by decide)) ?_
    -- and a node has a value and a link
    ty_open .rdi
    ty_block
  | loop =>
    -- the link in `rdi` is zero or it is a node
    ty_null .rdi
    -- zero: the test sends control to `done`, and what follows is not reached
    · ty_block
    -- a node: it may be read, and its link goes round the loop
    · ty_open .rdi
      ty_block
  | done => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, and the list in readable memory. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase listBytes blocks 0 0

/-- A link that holds the address of a node is a link. -/
theorem link_node {n : Nat} {a : BitVec 64} (h : Ψ a = some nodeLayout) :
    HasTy fetch linux Ψ n link a :=
  hasTy_nullable.mpr (.inr (hasTy_ref.mpr ⟨a, nodeLayout, h, rfl, fun h => absurd h (by decide),
    by simp⟩))

/-- The data has the types the blocks claim: each node's link holds what the
data says, the address of the next node or zero. -/
theorem Entry.fieldsOk {s : State} (h : Entry s) (n : Nat) :
    ∀ x ∈ blocks, ∀ i τ, x.2.fields[i]? = some τ →
      HasTy fetch linux Ψ n τ (s.load64 (x.1 + BitVec.ofNat 64 (8 * i))) := by
  intro x hx i τ hi
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hlen : listBytes.length = 48 := by decide
  have hval : ∀ k, k + 8 ≤ 48 →
      s.load64 (dataBase + BitVec.ofNat 64 k) = word64 listBytes k :=
    fun k hk => h.data.load64 (by rw [hlen]; exact hk)
  rcases hx with rfl | rfl | rfl
  · match i, hi with
    | 0, hi => cases hi; exact HasTy.int _
    | 1, hi =>
      cases hi
      -- the first node's link is the second node
      show HasTy fetch linux Ψ n link (s.load64 (dataBase + BitVec.ofNat 64 (8 * 1)))
      rw [hval (8 * 1) (by omega),
        show word64 listBytes (8 * 1) = dataBase + 16 from by decide +kernel]
      exact link_node rfl
    | i + 2, hi => simp [nodeLayout, nodeFields] at hi
  · match i, hi with
    | 0, hi => cases hi; exact HasTy.int _
    | 1, hi =>
      cases hi
      -- the second node's link is the third
      show HasTy fetch linux Ψ n link (s.load64 (dataBase + 16 + BitVec.ofNat 64 (8 * 1)))
      rw [show dataBase + 16 + BitVec.ofNat 64 (8 * 1) = dataBase + BitVec.ofNat 64 24 from by decide,
        hval 24 (by omega),
        show word64 listBytes 24 = dataBase + 32 from by decide +kernel]
      exact link_node rfl
    | i + 2, hi => simp [nodeLayout, nodeFields] at hi
  · match i, hi with
    | 0, hi => cases hi; exact HasTy.int _
    | 1, hi =>
      cases hi
      -- the third node's link is zero
      show HasTy fetch linux Ψ n link (s.load64 (dataBase + 32 + BitVec.ofNat 64 (8 * 1)))
      rw [show dataBase + 32 + BitVec.ofNat 64 (8 * 1) = dataBase + BitVec.ofNat 64 40 from by decide,
        hval 40 (by omega),
        show word64 listBytes 40 = 0 from by decide +kernel]
      exact hasTy_nullable.mpr (.inl rfl)
    | i + 2, hi => simp [nodeLayout, nodeFields] at hi

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck
and never faults: in particular it never loads through the zero that ends
the list. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start h.fieldsOk

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

end List3
