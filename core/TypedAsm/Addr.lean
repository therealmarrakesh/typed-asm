import TypedAsm.Program
import TypedAsm.Blocks

/-!
# Arithmetic of addresses

Facts about the byte a displacement and a scaled index reach, and about a
number of bytes as a 64-bit value: used wherever an operand is placed.
-/

namespace TypedAsm

namespace Addr

theorem sext_toNat {disp : BitVec 32} (hd : disp.toNat < 2 ^ 31) :
    disp.signExtend 64 = BitVec.ofNat 64 disp.toNat := by
  have h := sext_small hd
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

/-- The byte a scaled index and a displacement reach. It holds for any
index, since addresses wrap. -/
theorem index_bytes (c : BitVec 64) (sc : Scale) (disp : BitVec 32) (hd : disp.toNat < 2 ^ 31) :
    (c <<< sc.shift) + disp.signExtend 64
      = BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift + disp.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize c.toNat * 2 ^ sc.shift = m
  omega

theorem toNat_ofNat_lt {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_ofNat_add_le {j n m : Nat} (h : j + n ≤ m) : (BitVec.ofNat 64 j).toNat + n ≤ m := by
  rw [BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) h

theorem block_idx (c : BitVec 64) (sc : Scale) (disp : BitVec 32) (base : BitVec 64) (d : Nat)
    (h : disp.signExtend 64 = base + BitVec.ofNat 64 d) :
    (c <<< sc.shift) + disp.signExtend 64
      = base + BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift + d) := by
  have hc : c <<< sc.shift = BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [h, hc, BitVec.ofNat_add]
  ac_rfl

end Addr

export Addr (sext_toNat index_bytes)

end TypedAsm
