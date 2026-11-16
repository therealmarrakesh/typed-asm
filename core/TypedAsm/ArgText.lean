import TypedAsm.Entry
import TypedAsm.Program

/-!
# Arguments as text

A program that reads what its arguments say needs more of its starting
state than their addresses: each address must be the start of text, bytes
it may read that end in a zero. Linux provides exactly that, above the
stack. Here it is stated as a contract, turned into a memory typing with a
block of text for each argument, and shown to hold of the model's own
starting states.

The texts are not part of the program, so they are not in the memory typing
the program is typed against. They are in the one its run starts in, which
is larger; a typed program is safe from any such start.
-/

namespace TypedAsm

variable {Φ : CodeTy} {fetch : Fetch} {sys : Syscall}

/-- **Soundness from a larger memory typing.** A program typed block by
block against `Ψ` is safe from a state that is well typed against any
well-formed memory typing that has `Ψ`'s blocks and perhaps more. -/
theorem soundness_blocks_ext {Ψ Ψ' : MemTy} {s : State} (hB : BlocksOk Φ fetch sys Ψ)
    (he : Ψ.Ext Ψ') (hΨ' : Ψ'.WF) (hs : StateOk Φ fetch sys Ψ' s) : Safe fetch sys s :=
  let ⟨Γ, hΓ, hw⟩ := hs
  safe_of_safeN (fun n =>
    safeUpTo hB.programOk n n (Nat.le_refl n) Ψ' he hΨ' s.rip Γ (hB _ _ hΓ) s rfl (hw n))

/-! ## The contract -/

/-- A block of text for each argument: where it is and how long, counting
the zero that ends it. -/
def argLayouts (texts : List (BitVec 64 × Nat)) : List (BitVec 64 × Layout) :=
  texts.map fun t => (t.1, ⟨.raw 0, false, none, t.2, none⟩)

/-- What a program that reads its arguments needs of its starting state: the
entry contract, with the number of arguments at `[rsp]`, the address of each
one's text in the slots after it, and each text readable, ended by a zero,
and apart from the stack, from the program's blocks and from the others. -/
def EntryTexts (entry : BitVec 64) (parts : List (Nat × Perm × List Byte))
    (blocks : List (BitVec 64 × Layout)) (room : Nat) (s : State) : Prop :=
  ∃ texts : List (BitVec 64 × Nat),
    Entry entry parts (blocks ++ argLayouts texts) room (texts.length + 5) s ∧
    s.load64 (s.getReg .rsp) = BitVec.ofNat 64 texts.length ∧
    (∀ i (hi : i < texts.length),
      s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * (i + 1))) = texts[i].1) ∧
    MemTy.check (blocks ++ argLayouts texts) = true ∧
    (∀ t ∈ texts, ∀ x ∈ blocks, x.1 ≠ t.1)

/-- The context of a program that reads its arguments, when it was given `c`
of them: `[rsp]` holds exactly `c`; after it comes an array of `c` addresses,
each of the start of a text; and after that 32 plain bytes. -/
def textsCtx (room : Nat) (c : BitVec 64) : Ctx :=
  entryCtx room [.slot (.eq c), (ShapeOf.slot (.str false)).rep c.toNat, .raw 32]

variable {kinds : List (Nat × Shape)}

/-- Listing more blocks after the ones there are grows the memory typing. -/
theorem MemTy.ofList_ext (bs extra : List (BitVec 64 × Layout)) :
    (MemTy.ofList bs kinds).Ext (MemTy.ofList (bs ++ extra) kinds) := by
  refine ⟨fun a l h => ?_, rfl⟩
  show ((bs ++ extra).find? (·.1 = a)).map (·.2) = some l
  have h' : (bs.find? (·.1 = a)).map (·.2) = some l := h
  rw [List.find?_append]
  cases hf : bs.find? (·.1 = a) with
  | none => rw [hf] at h'; cases h'
  | some x => rw [hf] at h'; exact h'

theorem MemTy.declared_argLayouts (texts : List (BitVec 64 × Nat)) :
    MemTy.declared kinds (argLayouts texts) = [] ∧ MemTy.actual (argLayouts texts) = [] := by
  induction texts with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih => exact ih

/-- The blocks of text say nothing of their bytes. -/
theorem argLayouts_said (texts : List (BitVec 64 × Nat)) :
    ∀ x ∈ argLayouts texts, x.2.said = none := by
  intro x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
  rfl

theorem argLayouts_saidOk (texts : List (BitVec 64 × Nat)) :
    MemTy.saidOk (argLayouts texts) = true :=
  List.all_eq_true.mpr fun x hx => by rw [argLayouts_said texts x hx]

/-- The address of a text is where the memory typing has a block of text. -/
theorem MemTy.ofList_text {blocks : List (BitVec 64 × Layout)} {texts : List (BitVec 64 × Nat)}
    {t : BitVec 64 × Nat} (ht : t ∈ texts) (hno : ∀ x ∈ blocks, x.1 ≠ t.1) :
    ∃ n, MemTy.ofList (blocks ++ argLayouts texts) kinds t.1 = some ⟨.raw 0, false, none, n, none⟩ := by
  show ∃ n, ((blocks ++ argLayouts texts).find? (·.1 = t.1)).map (·.2) = some _
  have hnone : blocks.find? (·.1 = t.1) = none := by
    rw [List.find?_eq_none]
    intro x hx
    simpa using hno x hx
  rw [List.find?_append, hnone, Option.none_or]
  have hsome : ((argLayouts texts).find? (·.1 = t.1)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨(t.1, ⟨.raw 0, false, none, t.2, none⟩), List.mem_map.mpr ⟨t, ht, rfl⟩, by simp⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hy)
  exact ⟨u.2, by rw [hy]; rfl⟩

variable {entry : BitVec 64} {parts : List (Nat × Perm × List Byte)}
  {blocks : List (BitVec 64 × Layout)} {room : Nat}

/-- The contract asks nothing of the outside world. -/
theorem EntryTexts.withWorld {s : State} (h : EntryTexts entry parts blocks room s)
    (w : World) : EntryTexts entry parts blocks room { s with world := w } :=
  let ⟨texts, hE, h1, h2, h3, h4⟩ := h
  ⟨texts, hE.withWorld w, h1, h2, h3, h4⟩

/-- **A state meeting the contract is well typed** against the program's
memory typing with a block of text added for each argument, in the context
for the number of arguments it holds. -/
theorem EntryTexts.wellTyped {s : State}
    (h : EntryTexts entry parts blocks room s)
    (hk : MemTy.declared kinds blocks = MemTy.actual blocks)
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    ∃ (c : BitVec 64) (Ψ' : MemTy), (MemTy.ofList blocks kinds).Ext Ψ' ∧ Ψ'.WF ∧
      s.rip = entry ∧ (∀ g ∈ parts, s.Holds g) ∧
      ∀ n, WellTyped fetch sys Ψ' n (textsCtx room c) s := by
  obtain ⟨texts, hE, hc, hslots, hcheck, hno⟩ := h
  have hlt := hE.room_lt
  have hn : (BitVec.ofNat 64 texts.length).toNat = texts.length := by
    simp only [BitVec.toNat_ofNat]
    omega
  have hWF : (MemTy.ofList (blocks ++ argLayouts texts) kinds).WF :=
    MemTy.wf_of_check hcheck (by
      simp only [MemTy.declared, MemTy.actual, List.filterMap_append] at hk ⊢
      have := MemTy.declared_argLayouts (kinds := kinds) texts
      simp only [MemTy.declared, MemTy.actual] at this
      rw [this.1, this.2, hk]) hE.saidOk
  refine ⟨BitVec.ofNat 64 texts.length, _, MemTy.ofList_ext blocks _, hWF, hE.rip, hE.loaded,
    fun n => ?_⟩
  refine hE.matchesStack HasTy.int (fun x hx p hp => ?_) (by
    simp only [stackLen, ShapeOf.slot_size, ShapeOf.raw_size, ShapeOf.rep_size, hn]
    omega) ?_ ?_
  · -- the program's own blocks are plain bytes; a block of text has no typed values
    rcases List.mem_append.mp hx with hx | hx
    · rw [hfields x hx] at hp
      cases hp
    · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
      cases hp
  · intro S hS p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl
    · simp only [ShapeOf.slot, List.mem_singleton] at hp
      subst hp
      exact Nat.le_refl _
    · exact ShapeOf.fits_mem (ShapeOf.fits_rep rfl _) p hp
    · cases hp
  · intro k S hk p hp
    match k, hk with
    | 0, hk =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [ShapeOf.slot, List.mem_singleton] at hp
      subst hp
      rw [show s.getReg .rsp + BitVec.ofNat 64 (stackOff _ 0 + 0) = s.getReg .rsp by
        simp [stackOff], hc]
      exact hasTy_eq.mpr rfl
    | 1, hk =>
      -- an argument's place in the array holds the address of its text
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      obtain ⟨j, hj, q, hq, rfl⟩ := ShapeOf.mem_repFrom hp
      rw [hn] at hj
      simp only [ShapeOf.slot, List.mem_singleton] at hq
      subst hq
      have e : s.getReg .rsp + BitVec.ofNat 64
          (stackOff [ShapeOf.slot (Ty.eq (BitVec.ofNat 64 texts.length)),
            (ShapeOf.slot (Ty.str false)).rep (BitVec.ofNat 64 texts.length).toNat,
            ShapeOf.raw 32] 1 + (0 + j * (ShapeOf.slot (Ty.str false)).size + 0))
          = s.getReg .rsp + BitVec.ofNat 64 (8 * (j + 1)) := by
        simp only [stackOff, ShapeOf.slot_size]
        congr 2
        omega
      rw [e, hslots j hj]
      obtain ⟨m, hm⟩ := MemTy.ofList_text (kinds := kinds) (List.getElem_mem hj)
        (hno _ (List.getElem_mem hj))
      have hpos := hWF.nonempty _ _ hm
      exact hasTy_str.mpr ⟨_, _, 0, hm, by
        simpa [Layout.size] using hpos, by simp⟩
    | 2, hk =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      cases hp
    | k + 3, hk => simp at hk

/-! ## How the model lays out the arguments -/

theorem textsAt_length : ∀ (ts : List (List Byte)) (a : Nat), (textsAt ts a).length = ts.length
  | [], _ => rfl
  | _ :: ts, a => by simp only [textsAt, List.length_cons, textsAt_length ts]

theorem textBytes_length_cons (t : List Byte) (ts : List (List Byte)) :
    (textBytes (t :: ts)).length = t.length + 1 + (textBytes ts).length := by
  simp only [textBytes, List.length_append, List.length_cons]
  omega

/-- Each text lies within the run of texts, and is not empty. -/
theorem textsAt_bounds : ∀ (ts : List (List Byte)) (a : Nat), ∀ t ∈ textsAt ts a,
    a ≤ t.1 ∧ t.1 + t.2 ≤ a + (textBytes ts).length ∧ 0 < t.2
  | [], _, t, h => by simp [textsAt] at h
  | u :: ts, a, t, h => by
    rw [textBytes_length_cons]
    simp only [textsAt, List.mem_cons] at h
    rcases h with rfl | h
    · dsimp only
      omega
    · have := textsAt_bounds ts _ t h
      omega

/-- The last byte of each text is the zero that ends it. -/
theorem textsAt_zero : ∀ (ts : List (List Byte)) (a : Nat), ∀ t ∈ textsAt ts a,
    (textBytes ts)[t.1 - a + t.2 - 1]? = some 0
  | [], _, t, h => by simp [textsAt] at h
  | u :: ts, a, t, h => by
    simp only [textsAt, List.mem_cons] at h
    rcases h with rfl | h
    · show (u ++ 0 :: textBytes ts)[a - a + (u.length + 1) - 1]? = some 0
      rw [show a - a + (u.length + 1) - 1 = u.length by omega,
        List.getElem?_append_right (Nat.le_refl _)]
      simp
    · have hb := textsAt_bounds ts _ t h
      have ih := textsAt_zero ts _ t h
      show (u ++ 0 :: textBytes ts)[t.1 - a + t.2 - 1]? = some 0
      rw [List.getElem?_append_right (by omega),
        show t.1 - a + t.2 - 1 - u.length = (t.1 - (a + (u.length + 1)) + t.2 - 1) + 1 by omega,
        List.getElem?_cons_succ]
      exact ih

/-- Two texts are the same one, or one ends before the other starts. -/
theorem textsAt_apart : ∀ (ts : List (List Byte)) (a : Nat), ∀ t ∈ textsAt ts a,
    ∀ u ∈ textsAt ts a, t = u ∨ t.1 + t.2 ≤ u.1 ∨ u.1 + u.2 ≤ t.1
  | [], _, t, h, _, _ => by simp [textsAt] at h
  | v :: ts, a, t, ht, u, hu => by
    simp only [textsAt, List.mem_cons] at ht hu
    rcases ht with rfl | ht <;> rcases hu with rfl | hu
    · exact .inl rfl
    · have := textsAt_bounds ts _ u hu
      dsimp only
      omega
    · have := textsAt_bounds ts _ t ht
      dsimp only
      omega
    · exact textsAt_apart ts _ t ht u hu

theorem flatMap_le64_length {α : Type} (l : List α) (f : α → BitVec 64) :
    (l.flatMap fun x => le64 (f x)).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, le64_length, ih, List.length_cons]
    omega

/-- Past eight bytes, a 64-bit value is read from what follows them. -/
theorem word64_shift (v : BitVec 64) (rest : List Byte) (k : Nat) :
    word64 (le64 v ++ rest) (8 + k) = word64 rest k := by
  have h : ∀ j, (le64 v ++ rest).getD (8 + k + j) 0 = rest.getD (k + j) 0 := by
    intro j
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [le64_length]; omega), le64_length,
      show 8 + k + j - 8 = k + j by omega]
  have h0 := h 0
  simp only [Nat.add_zero] at h0
  simp only [word64, h, h0]

theorem word64_flatMap {α : Type} (l : List α) (f : α → BitVec 64) (rest : List Byte) (i : Nat)
    (hi : i < l.length) :
    word64 (l.flatMap (fun x => le64 (f x)) ++ rest) (8 * i) = f l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, List.append_assoc, List.getElem_cons_zero]
      exact word64_le64 _ _
    | succ j =>
      simp only [List.flatMap_cons, List.append_assoc, List.getElem_cons_succ]
      rw [show 8 * (j + 1) = 8 + 8 * j by omega, word64_shift]
      exact ih j (by simpa using hi)

theorem argBlock_length (args : List (List Byte)) :
    (argBlock args).length = 8 * (args.length + 5) + (textBytes args).length := by
  simp only [argBlock, List.length_append, le64_length, flatMap_le64_length, textsAt_length]
  omega

/-- After the words come the texts. -/
theorem argBlock_text (args : List (List Byte)) (j : Nat) :
    (argBlock args)[8 * (args.length + 5) + j]? = (textBytes args)[j]? := by
  have e : argBlock args =
      (le64 (BitVec.ofNat 64 args.length) ++
        (textsAt args (textBase args)).flatMap (fun t => le64 (BitVec.ofNat 64 t.1)) ++
        le64 0 ++ le64 0 ++ le64 0 ++ le64 0) ++ textBytes args := by
    simp only [argBlock, List.append_assoc]
  have hl : (le64 (BitVec.ofNat 64 args.length) ++
      (textsAt args (textBase args)).flatMap (fun t => le64 (BitVec.ofNat 64 t.1)) ++
      le64 0 ++ le64 0 ++ le64 0 ++ le64 0).length = 8 * (args.length + 5) := by
    simp only [List.length_append, le64_length, flatMap_le64_length, textsAt_length]
    omega
  rw [e, List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]

/-- The word for an argument is the address of its text. -/
theorem argBlock_slot (args : List (List Byte)) (i : Nat) (hi : i < args.length) :
    word64 (argBlock args) (8 * (i + 1)) =
      BitVec.ofNat 64 ((textsAt args (textBase args))[i]'(by rw [textsAt_length]; exact hi)).1 := by
  have hT : i < (textsAt args (textBase args)).length := by rw [textsAt_length]; exact hi
  have h := word64_flatMap (textsAt args (textBase args)) (fun t => BitVec.ofNat 64 t.1)
    (le64 0 ++ (le64 0 ++ (le64 0 ++ (le64 0 ++ textBytes args)))) i hT
  have e : word64 (argBlock args) (8 * (i + 1)) =
      word64 ((textsAt args (textBase args)).flatMap (fun t => le64 (BitVec.ofNat 64 t.1)) ++
        (le64 0 ++ (le64 0 ++ (le64 0 ++ (le64 0 ++ textBytes args))))) (8 * i) := by
    rw [show 8 * (i + 1) = 8 + 8 * i by omega]
    exact word64_shift _ _ _
  rw [e, h]

/-- Blocks the starting state also has, with their permissions, apart from
the stack and with their text ended, may be added to the contract. -/
theorem Entry.addBlocks {above : Nat} {s : State} {extra : List (BitVec 64 × Layout)}
    (h : Entry entry parts blocks room above s)
    (hperm : ∀ x ∈ extra,
      s.canRead x.1 x.2.size = true ∧ (x.2.writable = true → s.canWrite x.1 x.2.size = true))
    (hapart : ∀ x ∈ extra,
      Disjoint (s.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) x.1 x.2.size)
    (htext : ∀ x ∈ extra, x.2.text ≠ 0 → s.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0)
    (hsaid : SaidHeld s extra) (hok : MemTy.saidOk extra = true) :
    Entry entry parts (blocks ++ extra) room above s :=
  ⟨h.rip, h.loaded,
    fun x hx => (List.mem_append.mp hx).elim (h.perms x) (hperm x), h.stack,
    fun x hx => (List.mem_append.mp hx).elim (h.apart x) (hapart x), h.room_lt,
    fun x hx => (List.mem_append.mp hx).elim (h.text x) (htext x),
    fun x hx => (List.mem_append.mp hx).elim (h.said x) (hsaid x),
    MemTy.saidOk_append h.saidOk hok⟩

/-! ## The model's starting states meet the contract -/

/-- **A state with the program loaded, given a stack with arguments, meets
the contract of a program that reads them**, whatever they are. -/
theorem EntryTexts.ofLoad {p : State} (args : List (List Byte)) (hroom : 8 * room ≤ 0x10000)
    (hloaded : ∀ g ∈ parts, p.Holds g)
    (hfar : ∀ g ∈ parts, g.1 + g.2.2.length ≤ 0x7ffe0000)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hfarBlocks : ∀ x ∈ blocks, x.1.toNat + x.2.size ≤ 0x7ffe0000)
    (hcheck : MemTy.check blocks = true)
    (htext : ∀ x ∈ blocks, x.2.text ≠ 0 → p.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0 := by
      decide)
    (hsaid : saidCheck p blocks = true := by decide) :
    EntryTexts entry parts blocks room { p.withArgs room args with rip := entry } := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  -- names for the pieces
  generalize hS : ({ p.withArgs room args with rip := entry } : State) = S
  generalize hg : argsGiven args = given
  have hn : given.length ≤ 1000 := by rw [← hg]; exact argsGiven_length_le args
  have hbl : (argBlock given).length ≤ 0x8000 := by
    rw [← hg]; exact argBytes_length_le args
  have hblen := argBlock_length given
  have hE : Entry entry parts blocks room (given.length + 5) S := by
    rw [← hS, ← hg]
    exact Entry.ofLoadSlots args hroom (by have := argsGiven_length_le args; omega) hloaded
      hfar hblocks hfarBlocks htext hsaid
  have hsp : S.getReg .rsp = argBase := by
    rw [← hS]; exact State.getReg_withArgs p room args
  -- what was put on the stack is there
  have hD : S.HasData argBase (argBlock given) := by
    rw [← hS, ← hg]
    exact (State.hasData_withArgs p room args).congr rfl
  -- and may be read
  have hperm : ∀ x : BitVec 64, 0x7fff0000 ≤ x.toNat → x.toNat < 0x7fff8000 →
      S.perm x = .rw := by
    intro x h1 h2
    rw [← hS]
    show (p.withArgs room args).perm x = .rw
    exact State.perm_withArgs_in p room args hroom (by omega) (by omega)
  -- the texts
  let T := textsAt given (textBase given)
  have hTlen : T.length = given.length := textsAt_length _ _
  have hT : ∀ t ∈ T, 0x7fff0000 + 8 * (given.length + 5) ≤ t.1 ∧ t.1 + t.2 ≤ 0x7fff8000 ∧
      0 < t.2 := by
    intro t ht
    have := textsAt_bounds given (textBase given) t ht
    simp only [textBase, hbase] at this
    omega
  let texts : List (BitVec 64 × Nat) := T.map fun t => (BitVec.ofNat 64 t.1, t.2)
  have htl : texts.length = given.length := by
    show (T.map _).length = _
    rw [List.length_map, hTlen]
  have hmem : ∀ x ∈ argLayouts texts,
      ∃ t ∈ T, x = (BitVec.ofNat 64 t.1, ⟨.raw 0, false, none, t.2, none⟩) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
    exact ⟨t, ht, rfl⟩
  refine ⟨texts, ?_, ?_, ?_, ?_, ?_⟩
  · -- the contract, with the texts as blocks
    rw [htl]
    refine hE.addBlocks ?_ ?_ ?_
      (fun x hx b hb => by rw [argLayouts_said texts x hx] at hb; cases hb)
      (argLayouts_saidOk texts)
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := hmem x hx
      obtain ⟨h1, h2, h3⟩ := hT t ht
      refine ⟨?_, fun hw => Bool.noConfusion hw⟩
      rw [State.canRead_iff]
      intro i hi
      have hi' : i < t.2 := by simpa [Layout.size] using hi
      rw [hperm _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]
      rfl
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := hmem x hx
      obtain ⟨h1, h2, h3⟩ := hT t ht
      rw [hsp]
      show Disjoint _ _ _ (8 * 0 + t.2)
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
    · intro x hx _
      obtain ⟨t, ht, rfl⟩ := hmem x hx
      obtain ⟨h1, h2, h3⟩ := hT t ht
      show S.mem (BitVec.ofNat 64 t.1 + BitVec.ofNat 64 (8 * 0 + t.2 - 1)) = 0
      -- the last byte of the text, as a position in what was put on the stack
      have hb := textsAt_bounds given (textBase given) t ht
      have hz := textsAt_zero given (textBase given) t ht
      rw [← argBlock_text] at hz
      obtain ⟨hk, hval⟩ := List.getElem?_eq_some_iff.mp hz
      have hd := hD _ hk
      rw [hval] at hd
      rw [← hd]
      congr 1
      simp only [textBase, hbase] at hb ⊢
      bv_omega
  · -- the count
    have hl := hD.load64 (i := 0) (by omega)
    rw [hsp, show argBase = argBase + BitVec.ofNat 64 0 by simp, hl, htl]
    exact word64_le64 _ _
  · -- each slot holds the address of its text
    intro i hi
    have hi' : i < given.length := by rw [← htl]; exact hi
    have hl := hD.load64 (i := 8 * (i + 1)) (by omega)
    rw [hsp, hl, argBlock_slot given i hi']
    show _ = ((T.map fun t => (BitVec.ofNat 64 t.1, t.2))[i]'hi).1
    rw [List.getElem_map]
  · -- the blocks and the texts together pass the check
    simp only [MemTy.check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      Bool.or_eq_true] at hcheck ⊢
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact hcheck.1 x hx
      · obtain ⟨t, ht, rfl⟩ := hmem x hx
        obtain ⟨h1, h2, h3⟩ := hT t ht
        refine ⟨?_, rfl⟩
        simp only [Layout.size, ShapeOf.raw_size]
        omega
    · rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
      · exact hcheck.2 x hx y hy
      · obtain ⟨t, ht, rfl⟩ := hmem y hy
        obtain ⟨h1, h2, h3⟩ := hT t ht
        have hf := hfarBlocks x hx
        right
        show Disjoint _ _ _ (8 * 0 + t.2)
        refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
      · obtain ⟨t, ht, rfl⟩ := hmem x hx
        obtain ⟨h1, h2, h3⟩ := hT t ht
        have hf := hfarBlocks y hy
        right
        show Disjoint _ (8 * 0 + t.2) _ _
        refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
      · obtain ⟨t, ht, rfl⟩ := hmem x hx
        obtain ⟨u, hu, rfl⟩ := hmem y hy
        obtain ⟨h1, h2, h3⟩ := hT t ht
        obtain ⟨g1, g2, g3⟩ := hT u hu
        rcases textsAt_apart given (textBase given) t ht u hu with rfl | hlt | hlt
        · exact .inl rfl
        · right
          show Disjoint _ (8 * 0 + t.2) _ (8 * 0 + u.2)
          refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
        · right
          show Disjoint _ (8 * 0 + t.2) _ (8 * 0 + u.2)
          refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
  · -- no block starts where a text does
    intro t ht x hx he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    obtain ⟨h1, h2, h3⟩ := hT u hu
    have hf := hfarBlocks x hx
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    omega

end TypedAsm
