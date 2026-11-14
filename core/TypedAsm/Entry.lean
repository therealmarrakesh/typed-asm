import TypedAsm.Blocks
import TypedAsm.Soundness
import TypedAsm.Image
import Std.Tactic.BVDecide

/-!
# The entry contract

What a program needs of the state it starts in, stated once for every
program of the usual shape: code, some memory blocks, and a stack. It is the
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

/-- What a program needs of its starting state `s`: execution starts at
`entry`, the program's bytes are in executable memory at `base`, its data
is in memory at `dataBase`, each memory block has its permissions, and there
are `room` writable stack slots below `rsp` that overlap no block. -/
structure Entry (entry base : BitVec 64) (image : List Byte) (dataBase : BitVec 64)
    (data : List Byte) (blocks : List (BitVec 64 × Layout)) (room : Nat) (s : State) : Prop where
  rip : s.rip = entry
  code : s.HasCode base image
  data : s.HasData dataBase data
  perms : ∀ x ∈ blocks,
    s.canRead x.1 x.2.size = true ∧ (x.2.writable = true → s.canWrite x.1 x.2.size = true)
  stack : s.canWrite (s.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * room) = true
  apart : ∀ x ∈ blocks,
    Disjoint (s.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * room) x.1 x.2.size
  room_lt : 8 * room < 2 ^ 64

/-- The context a program is entered in: nothing known about any register,
an empty stack, and `room` free slots. -/
def entryCtx (room : Nat) : Ctx :=
  ⟨fun _ => .int, [], room, Flags.Any⟩

variable {entry base dataBase : BitVec 64} {image data : List Byte}
  {blocks : List (BitVec 64 × Layout)} {room : Nat}

/-- A state meeting the entry contract matches the entry context, provided
each field of each block holds a value of its type to begin with. For a
field that is not an integer, that is a fact about the program's data. -/
theorem Entry.matches {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry base image dataBase data blocks room s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ i τ, x.2.fields[i]? = some τ →
      H τ (s.load64 (x.1 + BitVec.ofNat 64 (8 * i)))) :
    Matches H (MemTy.ofList blocks) (entryCtx room) s where
  regs := fun _ _ => hint _
  flags := trivial
  stackPerm := h.stack
  stackSize_lt := h.room_lt
  stack := fun i τ hi => by simp [entryCtx] at hi
  heapPerm := fun a l hl => h.perms (a, l) (MemTy.mem_of_ofList hl)
  heap := fun a l hl i τ hi => hfields (a, l) (MemTy.mem_of_ofList hl) i τ hi
  stackHeap := fun a l hl => h.apart (a, l) (MemTy.mem_of_ofList hl)

/-- The same when every field of every block is an integer, which needs
nothing of the data. -/
theorem Entry.matchesInt {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry base image dataBase data blocks room s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    Matches H (MemTy.ofList blocks) (entryCtx room) s :=
  h.matches hint (fun x hx i τ hi => by
    rw [hfields x hx τ (List.mem_of_getElem? hi)]
    exact hint _)

/-- The entry contract says nothing about the outside world: it holds
whatever there is to read. -/
theorem Entry.withWorld {s : State} (h : Entry entry base image dataBase data blocks room s)
    (w : World) : Entry entry base image dataBase data blocks room { s with world := w } :=
  ⟨h.rip, h.code, h.data, h.perms, h.stack, h.apart, h.room_lt⟩

/-- A state built by loading the program into a prepared state meets the
entry contract, if the prepared state has the data, the blocks and the stack,
and all lie above the code. -/
theorem Entry.ofLoad {p : State} (hlen : image.length ≤ 2 ^ 64) (hroom : 8 * room < 2 ^ 64)
    (hdata : p.HasData dataBase data)
    (hfarData : base.toNat + image.length ≤ dataBase.toNat ∧
      dataBase.toNat + data.length ≤ 2 ^ 64)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hstack : p.canWrite (p.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * room) = true)
    (hapart : ∀ x ∈ blocks,
      Disjoint (p.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * room) x.1 x.2.size)
    (hfarBlocks : ∀ x ∈ blocks,
      base.toNat + image.length ≤ x.1.toNat ∧ x.1.toNat + x.2.size ≤ 2 ^ 64)
    (hfarStack : base.toNat + image.length + 8 * room ≤ (p.getReg .rsp).toNat) :
    Entry entry base image dataBase data blocks room
      { p.loadCode base image with rip := entry } := by
  have hp : ({ p.loadCode base image with rip := entry } : State).perm
      = (p.loadCode base image).perm := rfl
  have hsp : ({ p.loadCode base image with rip := entry } : State).getReg .rsp = p.getReg .rsp :=
    rfl
  refine ⟨rfl, (State.hasCode_loadCode p base image hlen).congr rfl rfl, ?_, ?_, ?_, ?_, hroom⟩
  · intro k hk
    show (p.loadCode base image).mem _ = _
    rw [State.mem_loadCode p base _ image hlen, List.getElem?_eq_none (by bv_omega)]
    exact hdata k hk
  · intro x hx
    obtain ⟨hr, hw⟩ := hblocks x hx
    obtain ⟨hf₁, hf₂⟩ := hfarBlocks x hx
    have hfar : ∀ k, k < x.2.size → image.length ≤ (x.1 + BitVec.ofNat 64 k - base).toNat := by
      intro k hk; bv_omega
    rw [State.canRead_congr hp, State.canRead_loadCode hfar, State.canWrite_congr hp,
      State.canWrite_loadCode hfar]
    exact ⟨hr, hw⟩
  · have hfar : ∀ k, k < 8 * room → image.length
        ≤ (p.getReg .rsp - BitVec.ofNat 64 (8 * room) + BitVec.ofNat 64 k - base).toNat := by
      intro k hk; bv_omega
    rw [hsp, State.canWrite_congr hp, State.canWrite_loadCode hfar]
    exact hstack
  · intro x hx
    rw [hsp]
    exact hapart x hx

end TypedAsm
