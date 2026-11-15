import TypedAsm.Machine
import TypedAsm.Asm

/-!
# A program's bytes, and loading them

The bytes of a labelled program are the encodings of its instructions, one
after another. A state that holds those bytes in executable memory has the
program loaded, in the sense the machine with code in memory needs.
-/

namespace TypedAsm

/-- The encodings of a list of instructions, one after another. -/
def encodeAll : List (Instr × BitVec 64) → List Byte
  | [] => []
  | (i, _) :: rest => i.encode ++ encodeAll rest

/-- The bytes of a labelled program loaded at `base`. -/
def Asm.image {L : Type} [DecidableEq L] (base : BitVec 64) (prog : List (Asm L)) : List Byte :=
  encodeAll (Asm.resolve (Asm.addr prog base) base prog)

/-- Memory from `a` holds exactly these bytes, and they are executable. -/
def State.HasCode (s : State) (a : BitVec 64) (bytes : List Byte) : Prop :=
  ∀ k (hk : k < bytes.length),
    s.mem (a + BitVec.ofNat 64 k) = bytes[k] ∧ s.perm (a + BitVec.ofNat 64 k) = .rx

/-- Holding code depends only on memory and permissions. -/
theorem State.HasCode.congr {s t : State} {a : BitVec 64} {bytes : List Byte}
    (h : t.HasCode a bytes) (hm : s.mem = t.mem) (hp : s.perm = t.perm) : s.HasCode a bytes := by
  intro k hk
  rw [hm, hp]
  exact h k hk

/-- Every instruction in the list is paired with its true length. -/
def LengthsOk (items : List (Instr × BitVec 64)) : Prop :=
  ∀ p ∈ items, p.2 = BitVec.ofNat 64 p.1.length

/-- Instructions laid out from `base` are loaded if their encodings are in
executable memory from `base`. -/
theorem loaded_layout {items : List (Instr × BitVec 64)} {base : BitVec 64} {s : State}
    (hlen : LengthsOk items) (hc : s.HasCode base (encodeAll items)) :
    Loaded (Fetch.layout base items) s := by
  induction items generalizing base with
  | nil => intro a i len h; simp [Fetch.layout] at h
  | cons p rest ih =>
    obtain ⟨i₀, len₀⟩ := p
    have hl₀ : len₀ = BitVec.ofNat 64 i₀.length := hlen (i₀, len₀) (List.mem_cons_self ..)
    intro a i len h
    simp only [Fetch.layout] at h
    split at h
    · next ha =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst ha
      refine ⟨hl₀, fun k hk => ?_⟩
      have hk' : k < (encodeAll ((i₀, len₀) :: rest)).length := by
        simp only [encodeAll, List.length_append]
        exact Nat.lt_of_lt_of_le hk (Nat.le_add_right ..)
      obtain ⟨hm, hp⟩ := hc k hk'
      refine ⟨?_, hp⟩
      rw [hm]
      simp only [encodeAll]
      exact List.getElem_append_left hk
    · refine ih (fun p hp => hlen p (List.mem_cons_of_mem _ hp)) (fun k hk => ?_) a i len h
      have hk' : i₀.length + k < (encodeAll ((i₀, len₀) :: rest)).length := by
        simp only [encodeAll, List.length_append]
        exact Nat.add_lt_add_left hk _
      obtain ⟨hm, hp⟩ := hc (i₀.length + k) hk'
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← hl₀] at hm hp
      refine ⟨?_, hp⟩
      rw [hm]
      simp [encodeAll, Instr.length]

/-- The labels module pairs every instruction with its true length. -/
theorem Asm.resolve_lengthsOk {L : Type} [DecidableEq L] (target : L → BitVec 64) (a : BitVec 64)
    (prog : List (Asm L)) : LengthsOk (Asm.resolve target a prog) := by
  induction prog generalizing a with
  | nil => intro p hp; simp [Asm.resolve] at hp
  | cons x rest ih =>
    intro p hp
    cases x with
    | label l => exact ih _ p (by simpa [Asm.resolve] using hp)
    | ins i =>
      simp only [Asm.resolve, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · exact ih _ p hp
    | jmp l =>
      simp only [Asm.resolve, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · exact ih _ p hp
    | jcc c l =>
      simp only [Asm.resolve, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · exact ih _ p hp
    | call l =>
      simp only [Asm.resolve, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rfl
      · exact ih _ p hp
    | ref i l past =>
      simp only [Asm.resolve, List.mem_cons] at hp
      rcases hp with rfl | hp
      · show BitVec.ofNat 64 i.length = BitVec.ofNat 64 (i.aim _).length
        rw [Instr.length_aim]
      · exact ih _ p hp
    | segment w => simp [Asm.resolve] at hp
    | bytes bs => simp [Asm.resolve] at hp
    | quad l => simp [Asm.resolve] at hp
    | space n => simp [Asm.resolve] at hp

/-- **A labelled program whose bytes are in executable memory is loaded.** -/
theorem Asm.loaded {L : Type} [DecidableEq L] {base : BitVec 64} {prog : List (Asm L)} {s : State}
    (hc : s.HasCode base (Asm.image base prog)) : Loaded (Asm.fetch base prog) s :=
  loaded_layout (Asm.resolve_lengthsOk _ _ _) hc

/-- The state with these bytes placed in executable memory from `a`. -/
def State.loadCode (s : State) (a : BitVec 64) (bytes : List Byte) : State :=
  let n := bytes.length
  { s with
    memory := s.memory.setBytes a bytes
    perms := s.perms.override (fun x => decide ((x - a).toNat < n)) .rx
      (if a.toNat + n ≤ 2 ^ 64 then a.toNat + n else 2 ^ 64)
      (fun x hx => by
        have hx' : (x - a).toNat < n := of_decide_eq_true hx
        split
        · rw [BitVec.toNat_sub] at hx'
          have := x.isLt
          have := a.isLt
          omega
        · exact x.isLt) }

/-- Loading bytes changes the addresses they cover and no other. -/
theorem State.mem_loadCode (s : State) (a x : BitVec 64) (bytes : List Byte)
    (hlen : bytes.length ≤ 2 ^ 64) :
    (s.loadCode a bytes).mem x = (bytes[(x - a).toNat]?).getD (s.mem x) :=
  Memory.get_setBytes _ _ _ _ hlen

/-- Loading bytes puts them in memory, executable. -/
theorem State.hasCode_loadCode (s : State) (a : BitVec 64) (bytes : List Byte)
    (hlen : bytes.length ≤ 2 ^ 64) : (s.loadCode a bytes).HasCode a bytes := by
  intro k hk
  have e : (a + BitVec.ofNat 64 k - a).toNat = k := by bv_omega
  refine ⟨?_, ?_⟩
  · rw [State.mem_loadCode s a _ bytes hlen, e, List.getElem?_eq_getElem hk]
    rfl
  · simp only [State.loadCode, State.perm, Perms.get_override, e, hk, decide_true, ite_true]

/-- Loading code does not change permissions outside the code. -/
theorem State.perm_loadCode_outside {s : State} {a x : BitVec 64} {bytes : List Byte}
    (h : bytes.length ≤ (x - a).toNat) : (s.loadCode a bytes).perm x = s.perm x := by
  simp only [State.loadCode, State.perm, Perms.get_override, Nat.not_lt.mpr h, decide_false,
    Bool.false_eq_true, ↓reduceIte]

/-- Loading code does not change what is readable outside the code. -/
theorem State.canRead_loadCode {s : State} {a b : BitVec 64} {bytes : List Byte} {n : Nat}
    (h : ∀ k, k < n → bytes.length ≤ (b + BitVec.ofNat 64 k - a).toNat) :
    (s.loadCode a bytes).canRead b n = s.canRead b n := by
  rw [Bool.eq_iff_iff]
  simp only [State.canRead, List.all_eq_true, List.mem_range]
  constructor
  · intro hh k hk
    have := hh k hk
    rwa [State.perm_loadCode_outside (h k hk)] at this
  · intro hh k hk
    rw [State.perm_loadCode_outside (h k hk)]
    exact hh k hk

/-- Loading code does not change what is writable outside the code. -/
theorem State.canWrite_loadCode {s : State} {a b : BitVec 64} {bytes : List Byte} {n : Nat}
    (h : ∀ k, k < n → bytes.length ≤ (b + BitVec.ofNat 64 k - a).toNat) :
    (s.loadCode a bytes).canWrite b n = s.canWrite b n := by
  rw [Bool.eq_iff_iff]
  simp only [State.canWrite, List.all_eq_true, List.mem_range]
  constructor
  · intro hh k hk
    have := hh k hk
    rwa [State.perm_loadCode_outside (h k hk)] at this
  · intro hh k hk
    rw [State.perm_loadCode_outside (h k hk)]
    exact hh k hk

end TypedAsm
