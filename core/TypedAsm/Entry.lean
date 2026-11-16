import TypedAsm.Blocks
import TypedAsm.Soundness
import TypedAsm.Image

/-!
# The entry contract

What a program needs of the state it starts in, stated once for every
program of the usual shape: the program itself, some memory blocks, and a
stack. It is the
contract with whatever loads the program; for an ELF file, with the kernel.

Nothing is assumed about the registers other than `rsp`, and nothing about
what the memory blocks contain beyond the program's own data.
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

/-- What a program needs of its starting state `s`: execution starts at
`entry`, every line of the program is in memory, executable where it is to
be executed, each memory block has its permissions, and the stack is there: `room` writable slots below `rsp` and `above` at and above
it, overlapping no block.

The room below `rsp` is asked for as writable memory. Linux does not have
all of a stack in memory to begin with: it keeps the addresses below the
stack clear, up to the limit on the stack's size, and puts memory there when
the program first touches it. A program cannot tell the difference, so room
within that limit meets this contract. The kernel keeps those addresses
clear of the memory it chooses for `mmap`, which is why `mmap` is modelled
only where the kernel chooses.

The slots at and above `rsp` are where the program's arguments are. Linux
starts a program with the number of arguments at `[rsp]`, the address of
each argument's text in the slots after it, then a zero, then the
environment's addresses and a zero, then at least two more words: so there
are always at least five slots, whatever the program was given. -/
structure Entry (entry : BitVec 64) (parts : List (Nat × Perm × List Byte))
    (blocks : List (BitVec 64 × Layout)) (room above : Nat) (s : State) : Prop where
  rip : s.rip = entry
  /-- What the program puts in memory is there: `Asm.parts` of the program. -/
  loaded : ∀ g ∈ parts, s.Holds g
  perms : ∀ x ∈ blocks,
    s.canRead x.1 x.2.size = true ∧ (x.2.writable = true → s.canWrite x.1 x.2.size = true)
  stack : s.canWrite (s.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) = true
  apart : ∀ x ∈ blocks,
    Disjoint (s.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) x.1 x.2.size
  room_lt : 8 * (room + above) < 2 ^ 64
  /-- The text of each block that has some ends in a zero byte. -/
  text : ∀ x ∈ blocks, x.2.text ≠ 0 → s.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0

/-- **The stack of a starting state is where a program can have memory.** No
state meets an entry contract with its stack at an address the processor
would refuse, or one the kernel keeps for itself. -/
theorem Entry.stack_top {entry : BitVec 64} {parts : List (Nat × Perm × List Byte)}
    {blocks : List (BitVec 64 × Layout)} {room above : Nat} {s : State}
    (h : Entry entry parts blocks room above s) (hpos : 0 < room + above) :
    (s.getReg .rsp - BitVec.ofNat 64 (8 * room)).toNat + 8 * (room + above) ≤ addrTop :=
  State.canWrite_top h.stack (by omega)

/-- The context a program is entered in: nothing known about any register,
room below `rsp` for `room` eight-byte words, and the given pieces at and
above `rsp`; none, unless the program looks at its arguments. The room is
counted in words here, as the entry contract counts it; in the context it is
that many bytes. -/
def entryCtx (room : Nat) (stack : List Shape := []) : Ctx :=
  ⟨fun _ => .int, stack, 8 * room, Flags.Any, [], 0⟩

/-- The context a program that looks at its arguments is entered in: `above`
eight-byte words at and above `rsp`, as plain bytes. The first is the number
of arguments; the ones after it are addresses of their text. -/
def entryCtxArgs (room above : Nat) : Ctx :=
  entryCtx room [.raw (8 * above)]

variable {entry : BitVec 64} {parts : List (Nat × Perm × List Byte)}
  {blocks : List (BitVec 64 × Layout)} {room above : Nat}

/-- Bytes the program puts at an address are in memory there: any stretch of
its data, wherever it begins. That it does put them there is settled by
computing. -/
theorem Entry.hasData {s : State} {a : BitVec 64} {bytes : List Byte}
    (h : Entry entry parts blocks room above s) (hc : partsHave parts a bytes = true) :
    s.HasData a bytes := by
  intro k hk
  have := List.all_eq_true.mp hc k (List.mem_range.mpr hk)
  simp only [beq_iff_eq] at this
  rw [State.mem_of_partsByte h.loaded this, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]
  rfl

/-- A state meeting the entry contract matches the entry context with any
pieces at and above `rsp` that come to the bytes that are there and whose
typed values are of their types, provided each typed value of each block is
of its type to begin with. -/
theorem Entry.matchesStack {H : Ty → BitVec 64 → Prop} {s : State} {σ : List Shape}
    (h : Entry entry parts blocks room above s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      H p.2 (s.load64 (x.1 + BitVec.ofNat 64 p.1)))
    (hσ : stackLen σ = 8 * above)
    (hfits : ∀ S ∈ σ, ∀ p ∈ S.vals, p.1 + 8 ≤ S.size)
    (hslots : ∀ k S, σ[k]? = some S → ∀ p ∈ S.vals,
      H p.2 (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff σ k + p.1)))) :
    Matches H (MemTy.ofList blocks kinds) (entryCtx room σ) s where
  regs := fun _ _ => hint _
  flags := trivial
  stackPerm := by
    have := h.stack
    rw [Nat.mul_add] at this
    simpa only [stackBase, stackSize, entryCtx, hσ] using this
  stackBound := by
    have := h.room_lt
    rw [Nat.mul_add] at this
    simpa only [stackSize, entryCtx, hσ, Nat.add_zero] using this
  stackFits := hfits
  stack := hslots
  heapPerm := fun a l hl => h.perms (a, l) (MemTy.mem_of_ofList hl)
  heap := fun a l hl p hp => hfields (a, l) (MemTy.mem_of_ofList hl) p hp
  stackHeap := fun a l hl => by
    have := h.apart (a, l) (MemTy.mem_of_ofList hl)
    rw [Nat.mul_add] at this
    simpa only [stackBase, stackSize, entryCtx, hσ] using this
  sp := hint _
  text := fun a l hl => h.text (a, l) (MemTy.mem_of_ofList hl)
  owned := OwnedOk.nil rfl

/-- A state meeting the entry contract matches the entry context, provided
each typed value of each block is of its type to begin with: a fact about the
program's data. -/
theorem Entry.matches {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry parts blocks room 0 s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      H p.2 (s.load64 (x.1 + BitVec.ofNat 64 p.1))) :
    Matches H (MemTy.ofList blocks kinds) (entryCtx room) s :=
  h.matchesStack hint hfields rfl (fun S hS => by cases hS) (fun k S hk => by simp at hk)

/-- The same when the blocks are all plain bytes, which needs nothing of the
data. -/
theorem Entry.matchesInt {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry parts blocks room 0 s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    Matches H (MemTy.ofList blocks kinds) (entryCtx room) s :=
  h.matches hint (fun x hx p hp => by
    rw [hfields x hx] at hp
    cases hp)

/-- For a program that looks at its arguments: the state matches the context
with `above` slots holding numbers, when the blocks are all plain bytes. -/
theorem Entry.matchesArgs {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry parts blocks room above s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    Matches H (MemTy.ofList blocks kinds) (entryCtxArgs room above) s :=
  h.matchesStack hint (fun x hx p hp => by
      rw [hfields x hx] at hp
      cases hp)
    (by simp [stackLen])
    (fun S hS p hp => by
      simp only [List.mem_singleton] at hS
      subst hS
      cases hp)
    (fun k S hk p hp => by
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        cases hp
      | succ k => simp at hk)

/-- The entry contract says nothing about the outside world: it holds
whatever there is to read. -/
theorem Entry.withWorld {s : State}
    (h : Entry entry parts blocks room above s) (w : World) :
    Entry entry parts blocks room above { s with world := w } :=
  ⟨h.rip, h.loaded, h.perms, h.stack, h.apart, h.room_lt, h.text⟩

/-- A state with the program loaded, its blocks and its stack, and `rip` set
to the entry, meets the entry contract. -/
theorem Entry.ofLoad {p : State} (hroom : 8 * (room + above) < 2 ^ 64)
    (hloaded : ∀ g ∈ parts, p.Holds g)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hstack : p.canWrite (p.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) = true)
    (hapart : ∀ x ∈ blocks,
      Disjoint (p.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) x.1 x.2.size)
    (htext : ∀ x ∈ blocks, x.2.text ≠ 0 → p.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0 := by
      decide) :
    Entry entry parts blocks room above { p with rip := entry } :=
  ⟨rfl, fun g hg => (hloaded g hg).congr rfl rfl, hblocks, hstack, hapart, hroom, htext⟩

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

/-- A state with the program loaded, given a stack with arguments, meets the
entry contract with any number of slots at and above the stack pointer that
the model's stack has room for, whatever the arguments are, if the program
and its blocks lie below the stack. -/
theorem Entry.ofLoadSlots {p : State} (args : List (List Byte)) (hroom : 8 * room ≤ 0x10000)
    (habove : 8 * above ≤ 0x10000)
    (hloaded : ∀ g ∈ parts, p.Holds g)
    (hfar : ∀ g ∈ parts, g.1 + g.2.2.length ≤ 0x7ffe0000)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hfarBlocks : ∀ x ∈ blocks, x.1.toNat + x.2.size ≤ 0x7ffe0000)
    (htext : ∀ x ∈ blocks, x.2.text ≠ 0 → p.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0 := by
      decide) :
    Entry entry parts blocks room above { p.withArgs room args with rip := entry } := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hsp : ({ p.withArgs room args with rip := entry } : State).getReg .rsp = argBase :=
    State.getReg_withArgs p room args
  -- below the stack, permissions are what they were
  have hperm : ∀ x : BitVec 64, x.toNat < 0x7ffe0000 →
      ({ p.withArgs room args with rip := entry } : State).perm x = p.perm x := by
    intro x hx
    exact State.perm_withArgs_below p room args hroom hx
  have hmem : ∀ x : BitVec 64, x.toNat < 0x7ffe0000 →
      ({ p.withArgs room args with rip := entry } : State).mem x = p.mem x :=
    fun x hx => State.mem_withArgs_below p room args (by omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · intro g hg k hk
    have hf := hfar g hg
    have hx : (BitVec.ofNat 64 g.1 + BitVec.ofNat 64 k).toNat < 0x7ffe0000 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    rw [hmem _ hx, hperm _ hx]
    exact hloaded g hg k hk
  · intro x hx
    obtain ⟨hr, hw⟩ := hblocks x hx
    have hf := hfarBlocks x hx
    have hin : ∀ i, i < x.2.size → (x.1 + BitVec.ofNat 64 i).toNat < 0x7ffe0000 := by
      intro i hi
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine ⟨?_, fun hwr => ?_⟩
    · rw [State.canRead_iff] at hr ⊢
      intro i hi
      rw [hperm _ (hin i hi)]
      exact hr i hi
    · have hw' := hw hwr
      rw [State.canWrite_iff] at hw' ⊢
      intro i hi
      rw [hperm _ (hin i hi)]
      exact hw' i hi
  · rw [hsp, State.canWrite_iff]
    intro i hi
    show ((p.withArgs room args).perm _).writable = true
    rw [State.perm_withArgs_in p room args hroom (by bv_omega) (by bv_omega)]
    rfl
  · intro x hx
    have hf := hfarBlocks x hx
    rw [hsp]
    refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega
  · intro x hx ht
    have hf := hfarBlocks x hx
    have hpos : 0 < x.2.size := by simp only [Layout.size]; omega
    rw [hmem _ (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega)]
    exact htext x hx ht

/-- The same for a program that looks at a fixed few of its arguments: up to
five slots, which are there whatever the program was given. -/
theorem Entry.ofLoadArgs {p : State} (args : List (List Byte)) (hroom : 8 * room ≤ 0x10000)
    (habove : above ≤ 5)
    (hloaded : ∀ g ∈ parts, p.Holds g)
    (hfar : ∀ g ∈ parts, g.1 + g.2.2.length ≤ 0x7ffe0000)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hfarBlocks : ∀ x ∈ blocks, x.1.toNat + x.2.size ≤ 0x7ffe0000)
    (htext : ∀ x ∈ blocks, x.2.text ≠ 0 → p.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0 := by
      decide) :
    Entry entry parts blocks room above { p.withArgs room args with rip := entry } :=
  Entry.ofLoadSlots args hroom (by omega) hloaded hfar hblocks hfarBlocks htext

/-! ## A program that goes through its arguments

Such a program needs to know how many slots there are, and that depends on
how many arguments it was given. So its contract says that `[rsp]` holds a
number `c` and that `c + 5` slots are there, and its entry context has `c`
in it: one context for each `c`. -/

/-- The context of a program that goes through its arguments, when it was
given `c` of them: `[rsp]` holds exactly `c`, and after it come `c + 4`
eight-byte words, as plain bytes. The first `c` of those are the addresses
of the arguments' texts. -/
def argsCtx (room : Nat) (c : BitVec 64) : Ctx :=
  entryCtx room [.slot (.eq c), .raw (8 * (c.toNat + 4))]

/-- What a program that goes through its arguments needs of its starting
state: the entry contract with as many slots as Linux provides for the
number of arguments found at `[rsp]`. -/
def EntryArgs (entry : BitVec 64) (parts : List (Nat × Perm × List Byte))
    (blocks : List (BitVec 64 × Layout)) (room : Nat) (s : State) : Prop :=
  ∃ c : BitVec 64, Entry entry parts blocks room (c.toNat + 5) s ∧
    s.load64 (s.getReg .rsp) = c

/-- A state meeting the contract matches the context for the number of
arguments it holds, when the blocks are all plain bytes. -/
theorem Entry.matchesCount {H : Ty → BitVec 64 → Prop} {s : State} {c : BitVec 64}
    (h : Entry entry parts blocks room (c.toNat + 5) s)
    (hc : s.load64 (s.getReg .rsp) = c) (hint : ∀ v, H .int v) (heq : ∀ v, H (.eq v) v)
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    Matches H (MemTy.ofList blocks kinds) (argsCtx room c) s :=
  h.matchesStack hint (fun x hx p hp => by
      rw [hfields x hx] at hp
      cases hp)
    (by simp only [stackLen, ShapeOf.slot_size, ShapeOf.raw_size]; omega)
    (fun S hS p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl
      · simp only [ShapeOf.slot, List.mem_singleton] at hp
        subst hp
        exact Nat.le_refl _
      · cases hp)
    (fun k S hk p hp => by
      match k, hk with
      | 0, hk =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [ShapeOf.slot, List.mem_singleton] at hp
        subst hp
        rw [show s.getReg .rsp + BitVec.ofNat 64 (stackOff _ 0 + 0) = s.getReg .rsp by
          simp [stackOff], hc]
        exact heq c
      | 1, hk =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        cases hp
      | k + 2, hk => simp at hk)

theorem EntryArgs.withWorld {s : State} (h : EntryArgs entry parts blocks room s)
    (w : World) : EntryArgs entry parts blocks room { s with world := w } :=
  let ⟨c, hE, hc⟩ := h
  ⟨c, hE.withWorld w, hc⟩

/-- A state with the program loaded, given a stack with arguments, meets the
contract of a program that goes through them, whatever they are. -/
theorem EntryArgs.ofLoad {p : State} (args : List (List Byte)) (hroom : 8 * room ≤ 0x10000)
    (hloaded : ∀ g ∈ parts, p.Holds g)
    (hfar : ∀ g ∈ parts, g.1 + g.2.2.length ≤ 0x7ffe0000)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hfarBlocks : ∀ x ∈ blocks, x.1.toNat + x.2.size ≤ 0x7ffe0000)
    (htext : ∀ x ∈ blocks, x.2.text ≠ 0 → p.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0 := by
      decide) :
    EntryArgs entry parts blocks room { p.withArgs room args with rip := entry } := by
  have hcnt := argCount_toNat args
  refine ⟨argCount args,
    Entry.ofLoadSlots args hroom (by omega) hloaded hfar hblocks hfarBlocks htext, ?_⟩
  -- the count is the first word of what was put on the stack
  have hd : ({ p.withArgs room args with rip := entry } : State).HasData argBase (argBytes args) :=
    (State.hasData_withArgs p room args).congr rfl
  have hl := hd.load64 (i := 0) (by
    show 0 + 8 ≤ (argBlock (argsGiven args)).length
    simp only [argBlock, List.length_append, le64_length]
    omega)
  have hsp : ({ p.withArgs room args with rip := entry } : State).getReg .rsp = argBase :=
    State.getReg_withArgs p room args
  rw [hsp, show argBase = argBase + BitVec.ofNat 64 0 by simp, hl]
  exact word64_le64 _ _

end TypedAsm
