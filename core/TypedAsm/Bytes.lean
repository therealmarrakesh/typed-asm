import TypedAsm.Memory
import TypedAsm.Encode

/-!
# A value and its eight bytes

A 64-bit value in memory is eight bytes, the least significant at the lowest
address. The bytes at an address are the bytes of the value loaded from
there, and a byte stored among them leaves the value with that byte
replaced: which is what lets the type of a field that holds an exactly known
value follow a store of one byte into it.
-/

namespace TypedAsm

/-- Eight bytes put together as a value, taken apart again, are the bytes. -/
theorem le64_of_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    le64 (((b7 ++ b6) ++ (b5 ++ b4)) ++ ((b3 ++ b2) ++ (b1 ++ b0)))
      = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [le64, le32, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i hi
     have key : ∀ (b : BitVec 8) (j : Nat), j = i → b.getLsbD j = b[i] := by
       rintro b _ rfl; exact BitVec.getLsbD_eq_getElem _
     simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
     repeat' split
     all_goals first
       | exact key _ _ (by omega)
       | (rw [decide_eq_true (by omega), Bool.true_and]; exact key _ _ (by omega))
       | (exfalso; omega))

/-- The eight bytes in memory at an address are the bytes of the value loaded
from there. -/
theorem State.loadBytes_eight (s : State) (a : BitVec 64) : s.loadBytes a 8 = le64 (s.load64 a) := by
  have e : s.loadBytes a 8 = [s.mem a, s.mem (a + 1), s.mem (a + 2), s.mem (a + 3), s.mem (a + 4),
      s.mem (a + 5), s.mem (a + 6), s.mem (a + 7)] := by
    simp [State.loadBytes, List.range, List.range.loop]
  rw [e]
  have h : s.load64 a = ((s.mem (a + 7) ++ s.mem (a + 6)) ++ (s.mem (a + 5) ++ s.mem (a + 4))) ++
      ((s.mem (a + 3) ++ s.mem (a + 2)) ++ (s.mem (a + 1) ++ s.mem a)) := by
    simp only [State.load64, State.load32, State.load16, State.load8, BitVec.add_assoc]
    rfl
  rw [h, le64_of_bytes]

/-- Eight bytes put together as a value, the first the least significant. -/
def ofBytes (l : List (BitVec 8)) : BitVec 64 :=
  ((l.getD 7 0 ++ l.getD 6 0) ++ (l.getD 5 0 ++ l.getD 4 0)) ++
    ((l.getD 3 0 ++ l.getD 2 0) ++ (l.getD 1 0 ++ l.getD 0 0))

/-- A value with one of its eight bytes replaced: byte 0 is the least
significant, which is the one at the lowest address. -/
def setByte (v : BitVec 64) (i : Nat) (b : BitVec 8) : BitVec 64 :=
  ofBytes ((le64 v).set i b)

/-- The value loaded from an address is its eight bytes put together. -/
theorem State.load64_ofBytes (s : State) (a : BitVec 64) :
    s.load64 a = ofBytes (s.loadBytes a 8) := by
  have e : s.loadBytes a 8 = [s.mem a, s.mem (a + 1), s.mem (a + 2), s.mem (a + 3), s.mem (a + 4),
      s.mem (a + 5), s.mem (a + 6), s.mem (a + 7)] := by
    simp [State.loadBytes, List.range, List.range.loop]
  rw [e]
  simp only [State.load64, State.load32, State.load16, State.load8, BitVec.add_assoc, ofBytes]
  rfl

/-- A byte stored among the eight at an address replaces that one of them. -/
theorem State.loadBytes_store8 (s : State) (a : BitVec 64) {i : Nat} (hi : i < 8) (b : BitVec 8) :
    (s.store8 (a + BitVec.ofNat 64 i) b).loadBytes a 8 = (s.loadBytes a 8).set i b := by
  apply List.ext_getElem
  · simp [State.loadBytes]
  · intro j h₁ h₂
    simp only [State.loadBytes, List.length_map, List.length_range] at h₁
    simp only [State.loadBytes, List.getElem_map, List.getElem_range, List.getElem_set,
      State.mem_store8]
    by_cases e : i = j
    · subst e; simp
    · have : a + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i := by
        intro h
        have h' : BitVec.ofNat 64 j = BitVec.ofNat 64 i := by
          have := congrArg (· - a) h
          simpa using this
        have := congrArg BitVec.toNat h'
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp [this, e]

/-- **A byte stored into an 8-byte field** leaves the field holding the
value it held with that byte replaced. -/
theorem State.load64_store8 (s : State) (a : BitVec 64) {i : Nat} (hi : i < 8) (b : BitVec 8) :
    (s.store8 (a + BitVec.ofNat 64 i) b).load64 a = setByte (s.load64 a) i b := by
  rw [State.load64_ofBytes, State.loadBytes_store8 s a hi, State.loadBytes_eight, setByte]

end TypedAsm
