import TypedAsm.Ranges
import TypedAsm.Image

/-!
# Data in memory, and a program's arguments

Bytes known to be in memory, how a program's data is put there, and what
the kernel puts on a new program's stack: the count of its arguments, the
address of each one's text, and the texts. No type system is needed to say
any of it.
-/

namespace TypedAsm

/-- The bytes are in memory at `a`. -/
def State.HasData (s : State) (a : BitVec 64) (bytes : List Byte) : Prop :=
  ∀ k, (h : k < bytes.length) → s.mem (a + BitVec.ofNat 64 k) = bytes[k]

theorem State.HasData.congr {s t : State} {a : BitVec 64} {bytes : List Byte}
    (h : s.HasData a bytes) (hm : t.mem = s.mem) : t.HasData a bytes :=
  fun k hk => by rw [hm]; exact h k hk

/-- The state with these bytes placed at `a`, with permission `p`. -/
def State.loadData (s : State) (a : BitVec 64) (bytes : List Byte) (p : Perm) : State :=
  (s.setPerm a (BitVec.ofNat 64 bytes.length) p).storeBytes a bytes

theorem State.hasData_loadData (s : State) (a : BitVec 64) (bytes : List Byte) (p : Perm)
    (hlen : bytes.length ≤ 2 ^ 64) : (s.loadData a bytes p).HasData a bytes := by
  intro k hk
  have e : (a + BitVec.ofNat 64 k - a).toNat = k := by bv_omega
  rw [State.loadData, State.mem_storeBytes _ a _ bytes hlen, e, List.getElem?_eq_getElem hk]
  rfl

/-- The 64-bit value whose eight bytes, lowest first, start at position `i`
of a list of bytes. -/
def word64 (l : List Byte) (i : Nat) : BitVec 64 :=
  ((l.getD (i + 7) 0 ++ l.getD (i + 6) 0) ++ (l.getD (i + 5) 0 ++ l.getD (i + 4) 0)) ++
    ((l.getD (i + 3) 0 ++ l.getD (i + 2) 0) ++ (l.getD (i + 1) 0 ++ l.getD i 0))

/-- A 64-bit load from data that is known is the value the bytes spell. -/
theorem State.HasData.load64 {s : State} {a : BitVec 64} {bytes : List Byte}
    (h : s.HasData a bytes) {i : Nat} (hi : i + 8 ≤ bytes.length) :
    s.load64 (a + BitVec.ofNat 64 i) = word64 bytes i := by
  have hb : ∀ j, (hj : j < 8) → ∀ x, x = a + BitVec.ofNat 64 (i + j) →
      s.mem x = bytes.getD (i + j) 0 := by
    intro j hj x hx
    rw [hx, h (i + j) (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  generalize hb' : a + BitVec.ofNat 64 i = b at *
  have h0 := hb 0 (by omega) b (by simp [← hb'])
  have h1 := hb 1 (by omega) (b + 1) (by rw [← hb']; bv_omega)
  have h2 := hb 2 (by omega) (b + 2) (by rw [← hb']; bv_omega)
  have h3 := hb 3 (by omega) (b + 2 + 1) (by rw [← hb']; bv_omega)
  have h4 := hb 4 (by omega) (b + 4) (by rw [← hb']; bv_omega)
  have h5 := hb 5 (by omega) (b + 4 + 1) (by rw [← hb']; bv_omega)
  have h6 := hb 6 (by omega) (b + 4 + 2) (by rw [← hb']; bv_omega)
  have h7 := hb 7 (by omega) (b + 4 + 2 + 1) (by rw [← hb']; bv_omega)
  simp only [State.load64, State.load32, State.load16, State.load8, word64, h0, h1, h2, h3, h4,
    h5, h6, h7, Nat.add_zero]

/-- A run of bytes that is in memory, a line of the program at a time, is in
memory. -/
theorem State.Holds.hasData {s : State} {g : Nat × Perm × List Byte} (h : s.Holds g) :
    s.HasData (BitVec.ofNat 64 g.1) g.2.2 :=
  fun k hk => (h k hk).1

/-- The byte a program puts at an address, if it puts one there. -/
def partsByte (parts : List (Nat × Perm × List Byte)) (x : Nat) : Option Byte :=
  parts.findSome? fun g => if g.1 ≤ x then g.2.2[x - g.1]? else none

/-- Whether a program puts these bytes at an address, as found by looking
each one up. -/
def partsHave (parts : List (Nat × Perm × List Byte)) (a : BitVec 64) (bytes : List Byte) : Bool :=
  (List.range bytes.length).all fun k =>
    partsByte parts (a + BitVec.ofNat 64 k).toNat == some (bytes.getD k 0)

theorem State.mem_of_partsByte {s : State} {parts : List (Nat × Perm × List Byte)}
    (h : ∀ g ∈ parts, s.Holds g) {x : BitVec 64} {b : Byte}
    (hb : partsByte parts x.toNat = some b) : s.mem x = b := by
  obtain ⟨g, hg, hx⟩ := List.exists_of_findSome?_eq_some hb
  split at hx
  · next hle =>
    obtain ⟨hk, hv⟩ := List.getElem?_eq_some_iff.mp hx
    have := (h g hg _ hk).1
    rw [hv] at this
    rw [← this]
    congr 1
    bv_omega
  · cases hx

/-- The eight bytes a program puts at an address, as a number; a byte it
does not put there counts as zero. -/
def partsWord (parts : List (Nat × Perm × List Byte)) (a : BitVec 64) : BitVec 64 :=
  word64 ((List.range 8).map fun k =>
    (partsByte parts (a + BitVec.ofNat 64 k).toNat).getD 0) 0

/-- Whether a program puts all eight bytes at an address. -/
def partsCover (parts : List (Nat × Perm × List Byte)) (a : BitVec 64) : Bool :=
  (List.range 8).all fun k => (partsByte parts (a + BitVec.ofNat 64 k).toNat).isSome

/-! ## A starting state with arguments

What the kernel puts on a new program's stack, built for the model: the
number of arguments, the address of each one's text, a zero, a zero for the
empty environment, two more zero words, and then the texts themselves, each
ended by a zero byte. -/

/-- Where the model puts the stack pointer of a program started with
arguments. -/
def argBase : BitVec 64 := 0x7fff0000

/-- Where each argument's text goes when the texts are laid end to end from
address `a`: its address, and its length counting the zero that ends it. -/
def textsAt : List (List Byte) → Nat → List (Nat × Nat)
  | [], _ => []
  | t :: ts, a => (a, t.length + 1) :: textsAt ts (a + (t.length + 1))

/-- The texts laid end to end, each ended by a zero. -/
def textBytes : List (List Byte) → List Byte
  | [] => []
  | t :: ts => t ++ 0 :: textBytes ts

/-- Where the first argument's text goes: after the count, an address for
each argument, and four more words. -/
def textBase (args : List (List Byte)) : Nat :=
  argBase.toNat + 8 * (args.length + 5)

/-- The words and texts for the given arguments, as they lie from `argBase`. -/
def argBlock (args : List (List Byte)) : List Byte :=
  le64 (BitVec.ofNat 64 args.length) ++
    ((textsAt args (textBase args)).flatMap (fun t => le64 (BitVec.ofNat 64 t.1)) ++
    (le64 0 ++ (le64 0 ++ (le64 0 ++ (le64 0 ++ textBytes args)))))

/-- The arguments a program is started with: the ones asked for, unless
there are too many or they would not fit in the space the model sets aside,
in which case none. -/
def argsGiven (args : List (List Byte)) : List (List Byte) :=
  if args.length ≤ 1000 ∧ (argBlock args).length ≤ 0x8000 then args else []

theorem argsGiven_length_le (args : List (List Byte)) : (argsGiven args).length ≤ 1000 := by
  unfold argsGiven
  split
  · next h => exact h.1
  · decide

/-- What the model puts on the stack for these arguments. -/
def argBytes (args : List (List Byte)) : List Byte :=
  argBlock (argsGiven args)

theorem argBytes_length_le (args : List (List Byte)) : (argBytes args).length ≤ 0x8000 := by
  unfold argBytes argsGiven
  split
  · next h => exact h.2
  · decide

/-- The number of arguments, as the program finds it at `[rsp]`. -/
def argCount (args : List (List Byte)) : BitVec 64 :=
  BitVec.ofNat 64 (argsGiven args).length

theorem argCount_toNat (args : List (List Byte)) : (argCount args).toNat ≤ 1000 := by
  have := argsGiven_length_le args
  simp only [argCount, BitVec.toNat_ofNat]
  omega

/-- The eight bytes of a value, put back together, are the value. -/
private theorem bytes_le64 (v : BitVec 64) :
    BitVec.extractLsb' 24 8 (BitVec.extractLsb' 32 32 v) ++
            BitVec.extractLsb' 16 8 (BitVec.extractLsb' 32 32 v) ++
          (BitVec.extractLsb' 8 8 (BitVec.extractLsb' 32 32 v) ++
            BitVec.extractLsb' 0 8 (BitVec.extractLsb' 32 32 v)) ++
        (BitVec.extractLsb' 24 8 (BitVec.extractLsb' 0 32 v) ++
            BitVec.extractLsb' 16 8 (BitVec.extractLsb' 0 32 v) ++
          (BitVec.extractLsb' 8 8 (BitVec.extractLsb' 0 32 v) ++
            BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 v))) = v := by
  ext i hi
  have key : ∀ j, j = i → v.getLsbD j = v[i] := by
    rintro _ rfl; exact BitVec.getLsbD_eq_getElem _
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first
    | exact key _ (by omega)
    | (rw [key _ (by omega)]; generalize v[i] = b; cases b <;> simp <;> omega)

/-- Eight bytes spelling a value, read back, are the value. -/
theorem word64_le64 (v : BitVec 64) (rest : List Byte) : word64 (le64 v ++ rest) 0 = v := by
  simp only [word64, le64, le32, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero, Nat.zero_add, Nat.reduceAdd]
  exact bytes_le64 v

/-- The state with a stack for a program given these arguments: `room`
writable slots below the stack pointer, and from the stack pointer up, 64
KiB of writable memory starting with the arguments. -/
def State.withArgs (s : State) (room : Nat) (args : List (List Byte)) : State :=
  ((s.setPerm (argBase - BitVec.ofNat 64 (8 * room)) (BitVec.ofNat 64 (8 * room + 0x10000)) .rw
    ).storeBytes argBase (argBytes args)).setReg .rsp argBase

namespace State

variable (s : State) (room : Nat) (args : List (List Byte))

theorem getReg_withArgs : (s.withArgs room args).getReg .rsp = argBase :=
  State.getReg_setReg_same _ _ _

/-- Only giving the stack its permission changes any. -/
theorem perm_withArgs (x : BitVec 64) :
    (s.withArgs room args).perm x =
      (s.setPerm (argBase - BitVec.ofNat 64 (8 * room)) (BitVec.ofNat 64 (8 * room + 0x10000))
        .rw).perm x :=
  rfl

/-- The stack is writable: the room below the stack pointer and the 64 KiB
from it up. -/
theorem perm_withArgs_in (hroom : 8 * room ≤ 0x10000) {x : BitVec 64}
    (h1 : argBase.toNat - 8 * room ≤ x.toNat) (h2 : x.toNat < argBase.toNat + 0x10000) :
    (s.withArgs room args).perm x = .rw := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hx : x.toNat < addrTop := by
    show x.toNat < 0x7ffffffff000
    rw [hbase] at h2
    exact Nat.lt_trans h2 (by decide)
  rw [perm_withArgs]
  exact State.perm_setPerm_in s (base := argBase - BitVec.ofNat 64 (8 * room))
    (len := BitVec.ofNat 64 (8 * room + 0x10000)) .rw hx ⟨by bv_omega, by bv_omega⟩

/-- Below the stack's pages, permissions are what they were. -/
theorem perm_withArgs_below (hroom : 8 * room ≤ 0x10000) {x : BitVec 64}
    (hx : x.toNat < 0x7ffe0000) : (s.withArgs room args).perm x = s.perm x := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hout : x.toNat / 4096 < (argBase - BitVec.ofNat 64 (8 * room)).toNat / 4096 := by
    bv_omega
  rw [perm_withArgs]
  exact State.perm_setPerm_out s (len := BitVec.ofNat 64 (8 * room + 0x10000)) .rw (.inl hout)

theorem mem_withArgs_below {x : BitVec 64} (hx : x.toNat < argBase.toNat) :
    (s.withArgs room args).mem x = s.mem x := by
  show ((s.setPerm _ _ _).storeBytes argBase (argBytes args)).mem x = s.mem x
  have hlen := argBytes_length_le args
  rw [State.mem_storeBytes _ _ _ _ (by omega), List.getElem?_eq_none (by
    have : argBase.toNat = 0x7fff0000 := rfl
    rw [BitVec.toNat_sub]
    omega)]
  rfl

/-- The stack holds what was put there. -/
theorem hasData_withArgs : (s.withArgs room args).HasData argBase (argBytes args) := by
  intro k hk
  have hlen := argBytes_length_le args
  have e : (argBase + BitVec.ofNat 64 k - argBase).toNat = k := by bv_omega
  show ((s.setPerm _ _ _).storeBytes argBase (argBytes args)).mem _ = _
  rw [State.mem_storeBytes _ _ _ _ (by omega), e, List.getElem?_eq_getElem hk]
  rfl

end State

/-- Memory below the stack keeps its data. -/
theorem State.HasData.withArgs {s : State} {a : BitVec 64} {bytes : List Byte}
    (h : s.HasData a bytes) (room : Nat) (args : List (List Byte))
    (hlt : a.toNat + bytes.length ≤ 0x7ffe0000) : (s.withArgs room args).HasData a bytes := by
  intro k hk
  rw [State.mem_withArgs_below s room args (by
    have : argBase.toNat = 0x7fff0000 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega)]
  exact h k hk

/-! ## A program that goes through its arguments

Such a program needs to know how many slots there are, and that depends on
how many arguments it was given. So its contract says that `[rsp]` holds a
number `c` and that `c + 5` slots are there, and its entry context has `c`
in it: one context for each `c`. -/

end TypedAsm

