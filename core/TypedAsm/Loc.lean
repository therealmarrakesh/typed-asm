import TypedAsm.Addr

/-!
# Where an operand's bytes are

The typing rules for an instruction with an operand in memory come in one
form for each way the operand can be placed: through a pointer, with or
without an index; in a block the context owns; in a piece of the stack; in
one of the program's blocks, reached from the next instruction or at an
address that is exactly known. `Loc` says of an operand which block or piece
it is in and which byte of it, whichever way that is, and from it every one
of those rules follows. A checker that finds the place has then only to say
what the instruction needs of it: that so many bytes are inside the block,
what typed value is there.
-/

namespace TypedAsm

/-- The kind of place an operand is in. -/
inductive Kind
  /-- A block others may point into, reached through a pointer. -/
  | ptr (writable : Bool)
  /-- The block the context owns at place `k`, which is at `a`. -/
  | owned (k : Nat) (a : BitVec 64)
  /-- Piece `k` of the stack. -/
  | piece (k : Nat)
  /-- One of the program's blocks. -/
  | block (writable : Bool)

/-- `Loc Ψ next Γ m κ S o`: the memory operand `m` names byte `o` of a block
or piece of shape `S`, of the kind `κ`. -/
inductive Loc (Ψ : MemTy) (next : BitVec 64) (Γ : Ctx) : Mem → Kind → Shape → Nat → Prop
  | field {b : Reg} {S : Shape} {w : Bool} {off d : Nat} {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .ptr S w off → byteDisp d disp →
    Loc Ψ next Γ (.sib (some b) none disp) (.ptr w) S (off + d)
  | indexed {b : Reg} {x : IndexReg} {sc : Scale} {S : Shape} {w : Bool} {off d : Nat}
      {disp : BitVec 32} {c : BitVec 64} :
    b ≠ .rsp → Γ.regs b = .ptr S w off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d →
    Loc Ψ next Γ (.sib (some b) (some (x, sc)) disp) (.ptr w) S (off + d)
  | owned {m : Mem} {k j : Nat} {a p : BitVec 64} {S : Shape} :
    EaIs Γ m p → Γ.owned[k]? = some (a, S) → p = a + BitVec.ofNat 64 j → j < 2 ^ 64 →
    Loc Ψ next Γ m (.owned k a) S j
  | slot {d k i : Nat} {S : Shape} {disp : BitVec 32} :
    byteDisp d disp → StackAt Γ.stack k S d i →
    Loc Ψ next Γ (.sib (some .rsp) none disp) (.piece k) S i
  | slotIndexed {x : IndexReg} {sc : Scale} {d k i : Nat} {S : Shape} {disp : BitVec 32}
      {c : BitVec 64} :
    Γ.regs x.toReg = .eq c → (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d →
    StackAt Γ.stack k S d i →
    Loc Ψ next Γ (.sib (some .rsp) (some (x, sc)) disp) (.piece k) S i
  | global {base : BitVec 64} {l : Layout} {d : Nat} {disp : BitVec 32} :
    Ψ base = some l → next + disp.signExtend 64 = base + BitVec.ofNat 64 d →
    Loc Ψ next Γ (.rip disp) (.block l.writable) l.shape d
  | placed {m : Mem} {p base : BitVec 64} {l : Layout} {d : Nat} :
    EaIs Γ m p → Ψ base = some l → p = base + BitVec.ofNat 64 d →
    Loc Ψ next Γ m (.block l.writable) l.shape d

namespace Loc

variable {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {m : Mem} {κ : Kind} {S : Shape} {o n : Nat}

open Addr (toNat_ofNat_lt)

/-- Bytes inside the block may be read. -/
theorem read (h : Loc Ψ next Γ m κ S o) (hin : o + n ≤ S.size) : ReadOk Ψ next Γ n (.mem m) := by
  cases h with
  | field hb hΓ hd => exact .field hb hΓ hd hin
  | indexed hb hΓ hx he => exact .indexed hb hΓ hx he hin
  | owned he ho hp hj => exact .owned he ⟨ho, hp⟩ (by rw [toNat_ofNat_lt hj]; exact hin)
  | slot hd hat => exact .slot hd hat hin
  | slotIndexed hx he hat => exact .slotIndexed hx he hat hin
  | global hl ha => exact .global hl ha hin
  | placed he hl hp => exact .placed he hl hp hin

/-- A 64-bit load of the typed value there keeps its type. -/
theorem load {d : Reg} {τ : Ty} (h : Loc Ψ next Γ m κ S o) (hd : d ≠ .rsp)
    (hv : S.valAt o = some τ) : Straight Ψ next Γ (.mov .w64 (.r_m d m)) (Γ.setReg d τ) := by
  cases h with
  | field hb hΓ hk => exact .loadField hd hb hΓ hk hv
  | indexed hb hΓ hx he => exact .loadIndexed hd hb hΓ hx he hv
  | owned he ho hp hj => exact .loadOwned hd he ⟨ho, hp⟩ (by rw [toNat_ofNat_lt hj]; exact hv)
  | slot hk hat => exact .loadStack hd hk hat hv
  | slotIndexed hx he hat => exact .loadStackIndexed hd hx he hat hv
  | global hl ha => exact .loadGlobal hd hl ha hv
  | placed he hl hp => exact .loadHeld hd (.placed he hl hp hv)

/-- Plain bytes of a block that may be written stay as they are. -/
theorem writeShared {w : Bool} (h : Loc Ψ next Γ m κ S o) (hκ : κ = .ptr w ∨ κ = .block w)
    (hw : w = true) (hin : o + n ≤ S.size) (hfree : S.free o n = true) :
    WriteIntOk Ψ next Γ n (.mem m) Γ := by
  subst hw
  cases h with
  | field hb hΓ hd => rcases hκ with e | e <;> cases e; exact .field hb hΓ hd hin hfree
  | indexed hb hΓ hx he => rcases hκ with e | e <;> cases e; exact .indexed hb hΓ hx he hin hfree
  | owned => rcases hκ with e | e <;> cases e
  | slot => rcases hκ with e | e <;> cases e
  | slotIndexed => rcases hκ with e | e <;> cases e
  | @global base l d disp hl ha =>
    have hwr : l.writable = true := by
      rcases hκ with e | e
      · cases e
      · injection e
    exact .global hl hwr ha hin hfree
  | @placed m p base l d he hl hp =>
    have hwr : l.writable = true := by
      rcases hκ with e | e
      · cases e
      · injection e
    exact .placed he hl hwr hp hin hfree

/-- Bytes of a block the context owns may be written: what typed values
reached into them are forgotten. -/
theorem writeOwned {k : Nat} {a : BitVec 64} (h : Loc Ψ next Γ m (.owned k a) S o)
    (hin : o + n ≤ S.size) :
    WriteIntOk Ψ next Γ n (.mem m) { Γ with owned := Γ.owned.set k (a, S.clear o n) } := by
  cases h with
  | owned he ho hp hj =>
    have e := toNat_ofNat_lt hj
    have := WriteIntOk.ownedClear (Ψ := Ψ) (next := next) (n := n) he ⟨ho, hp⟩
      (by rw [e]; exact hin)
    rw [e] at this
    exact this

/-- Bytes of a piece of the stack may be written, likewise. -/
theorem writePiece {k : Nat} (h : Loc Ψ next Γ m (.piece k) S o) (hin : o + n ≤ S.size) :
    WriteIntOk Ψ next Γ n (.mem m) { Γ with stack := Γ.stack.set k (S.clear o n) } := by
  cases h with
  | slot hd hat => exact .slot hd hat hin
  | slotIndexed hx he hat => exact .slotIndexed hx he hat hin

/-- A 64-bit store into a block the context owns: the bytes take the type
of what is stored. -/
theorem storeOwned {k : Nat} {a : BitVec 64} {s : Reg} (h : Loc Ψ next Γ m (.owned k a) S o)
    (hs : s ≠ .rsp) (hin : o + 8 ≤ S.size) :
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem m) s))
      { Γ with owned := Γ.owned.set k (a, S.set o (Γ.regs s)) } := by
  cases h with
  | owned he ho hp hj =>
    have e := toNat_ofNat_lt hj
    have := Straight.storeOwned (Ψ := Ψ) (next := next) hs he ⟨ho, hp⟩ (by rw [e]; exact hin)
    rw [e] at this
    exact this

/-- One byte stored into an 8-byte field of a block the context owns that
holds an exactly known value, from a register that holds one: the field
holds the value with that byte replaced. -/
theorem store8Owned {k : Nat} {a v x : BitVec 64} {s : Reg} {f : Nat}
    (h : Loc Ψ next Γ m (.owned k a) S o) (hs : s ≠ .rsp) (hlo : f ≤ o) (hhi : o < f + 8)
    (hv : S.valAt f = some (.eq v)) (hx : Γ.regs s = .eq x) :
    Straight Ψ next Γ (.store8 m s)
      { Γ with
        owned := Γ.owned.set k (a, S.set f (.eq (setByte v (o - f) (x.setWidth 8)))) } := by
  cases h with
  | owned he ho hp hj =>
    have e := toNat_ofNat_lt hj
    have := Straight.store8Owned (Ψ := Ψ) (next := next) hs he ⟨ho, hp⟩ (by rw [e]; exact hlo)
      (by rw [e]; exact hhi) hv hx
    rw [e] at this
    exact this

/-- The same for a field of a piece of the stack, reached from the stack
pointer by a displacement. -/
theorem store8Piece {k : Nat} {v x : BitVec 64} {s : Reg} {f : Nat} {disp : BitVec 32}
    (h : Loc Ψ next Γ (.sib (some .rsp) none disp) (.piece k) S o) (hs : s ≠ .rsp)
    (hlo : f ≤ o) (hhi : o < f + 8) (hv : S.valAt f = some (.eq v)) (hx : Γ.regs s = .eq x) :
    Straight Ψ next Γ (.store8 (.sib (some .rsp) none disp) s)
      { Γ with stack := Γ.stack.set k (S.set f (.eq (setByte v (o - f) (x.setWidth 8)))) } := by
  cases h with
  | slot hd hat => exact .store8Slot hs hd hat hlo hhi hv hx

/-- A 64-bit store over a typed value reached through a writable pointer: a
value of the type that is there. -/
theorem storePtr {s : Reg} {τ : Ty} (h : Loc Ψ next Γ m (.ptr true) S o) (hs : s ≠ .rsp)
    (hv : S.valAt o = some τ) (hso : S.sole o = true) (hsub : Sub (Γ.regs s) τ) :
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem m) s)) Γ := by
  cases h with
  | field hb hΓ hd => exact .storeField hb hs hΓ hd hv hso hsub
  | indexed hb hΓ hx he => exact .storeIndexed hb hs hΓ hx he hv hso hsub

/-- A 64-bit store over a typed value of a block the context owns, of a
value of the type that is there: the context stays as it is. -/
theorem storeOwnedKeep {k : Nat} {a : BitVec 64} {s : Reg} {τ : Ty}
    (h : Loc Ψ next Γ m (.owned k a) S o) (hs : s ≠ .rsp) (hv : S.valAt o = some τ)
    (hso : S.sole o = true) (hsub : Sub (Γ.regs s) τ) :
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem m) s)) Γ := by
  cases h with
  | owned he ho hp hj =>
    have e := toNat_ofNat_lt hj
    exact .storeOwnedKeep hs he ⟨ho, hp⟩ (by rw [e]; exact hv) (by rw [e]; exact hso) hsub

/-- A 64-bit store over a typed value of one of the program's writable
blocks: a value of the type that is there. -/
theorem storeBlock {s : Reg} {τ : Ty} (h : Loc Ψ next Γ m κ S o) (hκ : κ = .block true)
    (hs : s ≠ .rsp) (hv : S.valAt o = some τ) (hso : S.sole o = true)
    (hsub : Sub (Γ.regs s) τ) : Straight Ψ next Γ (.mov .w64 (.rm_r (.mem m) s)) Γ := by
  cases h with
  | field => cases hκ
  | indexed => cases hκ
  | owned => cases hκ
  | slot => cases hκ
  | slotIndexed => cases hκ
  | @global base l d disp hl ha =>
    have hwr : l.writable = true := by injection hκ
    exact .storeGlobal hs hl hwr ha hv hso hsub
  | @placed m p base l d he hl hp =>
    have hwr : l.writable = true := by injection hκ
    exact .storePlaced hs he hl hwr hp hv hso hsub

/-- A typed value at a place is held there, in the sense the rules for an
operand that holds a value speak of. The rules have no such form for a block
the context owns or for the stack reached through an index. -/
theorem holds {τ : Ty} (h : Loc Ψ next Γ m κ S o) (hκ : ∀ k a, κ ≠ .owned k a)
    (hm : ∀ x d, m ≠ .sib (some .rsp) (some x) d) (hv : S.valAt o = some τ) :
    Holds Ψ next Γ (.mem m) τ := by
  cases h with
  | field hb hΓ hd => exact .field hb hΓ hd hv
  | indexed hb hΓ hx he => exact .indexed hb hΓ hx he hv
  | owned => exact absurd rfl (hκ _ _)
  | slot hd hat => exact .slot hd hat hv
  | slotIndexed => exact absurd rfl (hm _ _)
  | global hl ha => exact .global hl ha hv
  | placed he hl hp => exact .placed he hl hp hv

end Loc

end TypedAsm
