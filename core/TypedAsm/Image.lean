import TypedAsm.Machine
import TypedAsm.Asm

/-!
# A program in memory

A labelled program says, line by line, which bytes go where and with what
permission: `Asm.parts`. A state that holds every line's bytes, executable
where the line is in an executable segment, has the program loaded, in the
sense the machine with code in memory needs.
-/

namespace TypedAsm

attribute [local instance] IsLabel.dec

/-- Memory holds these bytes from an address on, and if the permission asked
for is to execute, they are executable. -/
def State.Holds (s : State) (g : Nat × Perm × List Byte) : Prop :=
  ∀ k (hk : k < g.2.2.length),
    s.mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) = g.2.2[k] ∧
      (g.2.1 = .rx → s.perm (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) = .rx)

/-- Holding bytes depends only on memory and permissions. -/
theorem State.Holds.congr {s t : State} {g : Nat × Perm × List Byte}
    (h : t.Holds g) (hm : s.mem = t.mem) (hp : s.perm = t.perm) : s.Holds g := by
  intro k hk
  rw [hm, hp]
  exact h k hk

/-- Whether memory holds each of these runs of bytes, executable where that
is asked, as found by looking at each byte. -/
def State.holdsCheck (s : State) (parts : List (Nat × Perm × List Byte)) : Bool :=
  parts.all fun g =>
    (List.range g.2.2.length).all fun k =>
      s.mem (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) == g.2.2.getD k 0 &&
        (g.2.1 != .rx || s.perm (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k) == .rx)

/-- A check of each byte shows that memory holds what it should. This serves
for a starting state however it was made. -/
theorem State.holds_of_check {s : State} {parts : List (Nat × Perm × List Byte)}
    (h : s.holdsCheck parts = true) : ∀ g ∈ parts, s.Holds g := by
  intro g hg k hk
  have := List.all_eq_true.mp (List.all_eq_true.mp h g hg) k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  obtain ⟨hm, hp⟩ := this
  refine ⟨?_, fun hx => ?_⟩
  · rw [hm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  · rcases hp with hp | hp
    · simp [hx] at hp
    · exact hp

namespace Asm

variable {L : Type} [IsLabel L]

omit [IsLabel L] in
/-- A line that is an instruction comes to that instruction's bytes. -/
theorem lineBytes_of_instr {target : L → BitVec 64} {a : Nat} {x : Asm L} {i : Instr}
    (h : instr target (BitVec.ofNat 64 (next a x)) x = some i) :
    lineBytes target a x = i.encode := by
  cases x <;> simp_all [lineBytes, instr]

omit [IsLabel L] in
/-- Every instruction in the table has its true length, and its bytes are
among what the program puts in memory, at its address, to be executed. -/
theorem tableFrom_mem (target : L → BitVec 64) (a : Nat) (p : Perm) (prog : List (Asm L)) :
    ∀ e ∈ tableFrom target a p prog,
      e.2.2 = BitVec.ofNat 64 e.2.1.length ∧
        (e.1, Perm.rx, e.2.1.encode) ∈ partsFrom target a p prog := by
  induction prog generalizing a p with
  | nil => intro e he; cases he
  | cons x rest ih =>
    intro e he
    simp only [tableFrom] at he
    simp only [partsFrom, List.mem_cons]
    split at he
    · next i hi =>
      split at he
      · next hp =>
        rcases List.mem_cons.mp he with rfl | he
        · subst hp
          exact ⟨by rw [← Instr.size_eq], .inl (by rw [lineBytes_of_instr hi])⟩
        · exact ⟨(ih _ _ e he).1, .inr (ih _ _ e he).2⟩
      · exact ⟨(ih _ _ e he).1, .inr (ih _ _ e he).2⟩
    · exact ⟨(ih _ _ e he).1, .inr (ih _ _ e he).2⟩

/-- **A labelled program whose lines are all in memory is loaded.** -/
theorem loaded {base : BitVec 64} {prog : List (Asm L)} {s : State}
    (h : ∀ g ∈ parts base prog, s.Holds g) : Loaded (fetch base prog) s := by
  intro a i len hf
  obtain ⟨hlen, hmem⟩ := tableFrom_mem _ _ _ _ _ (Lookup.first_mem hf)
  refine ⟨hlen, fun k hk => ?_⟩
  obtain ⟨hm, hp⟩ := h _ hmem k hk
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hm hp
  exact ⟨hm, hp trivial⟩

end Asm

end TypedAsm
