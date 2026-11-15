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
is in memory at `dataBase`, each memory block has its permissions, and the
stack is there: `room` writable slots below `rsp` and `above` at and above
it, overlapping no block.

The slots at and above `rsp` are where the program's arguments are. Linux
starts a program with the number of arguments at `[rsp]`, the address of
each argument's text in the slots after it, then a zero, then the
environment's addresses and a zero, then at least two more words: so there
are always at least five slots, whatever the program was given. -/
structure Entry (entry base : BitVec 64) (image : List Byte) (dataBase : BitVec 64)
    (data : List Byte) (blocks : List (BitVec 64 × Layout)) (room above : Nat) (s : State) :
    Prop where
  rip : s.rip = entry
  code : s.HasCode base image
  data : s.HasData dataBase data
  perms : ∀ x ∈ blocks,
    s.canRead x.1 x.2.size = true ∧ (x.2.writable = true → s.canWrite x.1 x.2.size = true)
  stack : s.canWrite (s.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) = true
  apart : ∀ x ∈ blocks,
    Disjoint (s.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) x.1 x.2.size
  room_lt : 8 * (room + above) < 2 ^ 64

/-- The context a program is entered in: nothing known about any register,
`room` free slots, and the given types for the slots at and above `rsp`;
none, unless the program looks at its arguments. -/
def entryCtx (room : Nat) (stack : List Ty := []) : Ctx :=
  ⟨fun _ => .int, stack, room, Flags.Any⟩

/-- The context a program that looks at its arguments is entered in: `above`
slots at and above `rsp`, each holding some number. The first is the number
of arguments; the ones after it are addresses of their text. -/
def entryCtxArgs (room above : Nat) : Ctx :=
  entryCtx room (List.replicate above .int)

variable {entry base dataBase : BitVec 64} {image data : List Byte}
  {blocks : List (BitVec 64 × Layout)} {room above : Nat}

/-- A state meeting the entry contract matches the entry context with any
types for the slots at and above `rsp` that those slots have, provided each
field of each block holds a value of its type to begin with. -/
theorem Entry.matchesStack {H : Ty → BitVec 64 → Prop} {s : State} {σ : List Ty}
    (h : Entry entry base image dataBase data blocks room above s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ i τ, x.2.fields[i]? = some τ →
      H τ (s.load64 (x.1 + BitVec.ofNat 64 (8 * i))))
    (hσ : σ.length = above)
    (hslots : ∀ i τ, σ[i]? = some τ → H τ (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)))) :
    Matches H (MemTy.ofList blocks kinds) (entryCtx room σ) s where
  regs := fun _ _ => hint _
  flags := trivial
  stackPerm := by
    have := h.stack
    simpa only [stackBase, stackSize, entryCtx, hσ] using this
  stackSize_lt := by
    have := h.room_lt
    simpa only [stackSize, entryCtx, hσ] using this
  stack := hslots
  heapPerm := fun a l hl => h.perms (a, l) (MemTy.mem_of_ofList hl)
  heap := fun a l hl i τ hi => hfields (a, l) (MemTy.mem_of_ofList hl) i τ hi
  stackHeap := fun a l hl => by
    have := h.apart (a, l) (MemTy.mem_of_ofList hl)
    simpa only [stackBase, stackSize, entryCtx, hσ] using this
  sp := hint _

/-- A state meeting the entry contract matches the entry context, provided
each field of each block holds a value of its type to begin with. For a
field that is not an integer, that is a fact about the program's data. -/
theorem Entry.matches {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry base image dataBase data blocks room 0 s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ i τ, x.2.fields[i]? = some τ →
      H τ (s.load64 (x.1 + BitVec.ofNat 64 (8 * i)))) :
    Matches H (MemTy.ofList blocks kinds) (entryCtx room) s :=
  h.matchesStack hint hfields rfl (fun i τ hi => by simp at hi)

/-- The same when every field of every block is an integer, which needs
nothing of the data. -/
theorem Entry.matchesInt {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry base image dataBase data blocks room 0 s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    Matches H (MemTy.ofList blocks kinds) (entryCtx room) s :=
  h.matches hint (fun x hx i τ hi => by
    rw [hfields x hx τ (List.mem_of_getElem? hi)]
    exact hint _)

/-- For a program that looks at its arguments: the state matches the context
with `above` slots holding numbers, when every field of every block is an
integer. -/
theorem Entry.matchesArgs {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry base image dataBase data blocks room above s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    Matches H (MemTy.ofList blocks kinds) (entryCtxArgs room above) s :=
  h.matchesStack hint (fun x hx i τ hi => by
      rw [hfields x hx τ (List.mem_of_getElem? hi)]
      exact hint _)
    List.length_replicate (fun i τ hi => by
      have hτ : τ = .int := by
        rw [List.getElem?_replicate] at hi
        split at hi
        · exact (Option.some.inj hi).symm
        · cases hi
      rw [hτ]
      exact hint _)

/-- The entry contract says nothing about the outside world: it holds
whatever there is to read. -/
theorem Entry.withWorld {s : State}
    (h : Entry entry base image dataBase data blocks room above s) (w : World) :
    Entry entry base image dataBase data blocks room above { s with world := w } :=
  ⟨h.rip, h.code, h.data, h.perms, h.stack, h.apart, h.room_lt⟩

/-- A state built by loading the program into a prepared state meets the
entry contract, if the prepared state has the data, the blocks and the stack,
and all lie above the code. -/
theorem Entry.ofLoad {p : State} (hlen : image.length ≤ 2 ^ 64)
    (hroom : 8 * (room + above) < 2 ^ 64)
    (hdata : p.HasData dataBase data)
    (hfarData : base.toNat + image.length ≤ dataBase.toNat ∧
      dataBase.toNat + data.length ≤ 2 ^ 64)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hstack : p.canWrite (p.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) = true)
    (hapart : ∀ x ∈ blocks,
      Disjoint (p.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * (room + above)) x.1 x.2.size)
    (hfarBlocks : ∀ x ∈ blocks,
      base.toNat + image.length ≤ x.1.toNat ∧ x.1.toNat + x.2.size ≤ 2 ^ 64)
    (hfarStack : base.toNat + image.length + 8 * room ≤ (p.getReg .rsp).toNat ∧
      (p.getReg .rsp).toNat + 8 * above ≤ 2 ^ 64) :
    Entry entry base image dataBase data blocks room above
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
  · have hfar : ∀ k, k < 8 * (room + above) → image.length
        ≤ (p.getReg .rsp - BitVec.ofNat 64 (8 * room) + BitVec.ofNat 64 k - base).toNat := by
      intro k hk; bv_omega
    rw [hsp, State.canWrite_congr hp, State.canWrite_loadCode hfar]
    exact hstack
  · intro x hx
    rw [hsp]
    exact hapart x hx

/-! ## A starting state with arguments

What the kernel puts on a new program's stack, built for the model: the
number of arguments, the address of each one's text, a zero, a zero for the
empty environment, two more zero words, and then the texts themselves, each
ended by a zero byte. -/

/-- Where the model puts the stack pointer of a program started with
arguments. -/
def argBase : BitVec 64 := 0x7fff0000

/-- The words and texts for the given arguments, as they lie from `argBase`. -/
def argBlock (args : List (List Byte)) : List Byte :=
  let texts := args.map (· ++ [0])
  let first := argBase.toNat + 8 * (args.length + 5)
  let addrs := (texts.foldl (fun (acc : List Nat × Nat) t => (acc.1 ++ [acc.2], acc.2 + t.length))
    ([], first)).1
  le64 (BitVec.ofNat 64 args.length) ++ addrs.flatMap (fun a => le64 (BitVec.ofNat 64 a)) ++
    le64 0 ++ le64 0 ++ le64 0 ++ le64 0 ++ texts.flatten

/-- The same, unless it would not fit in the space the model sets aside, in
which case the program is started with no arguments. -/
def argBytes (args : List (List Byte)) : List Byte :=
  if (argBlock args).length ≤ 0x8000 then argBlock args else argBlock []

theorem argBytes_length_le (args : List (List Byte)) : (argBytes args).length ≤ 0x8000 := by
  unfold argBytes
  split
  · assumption
  · decide

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

theorem perm_withArgs (x : BitVec 64) :
    (s.withArgs room args).perm x =
      if x - (argBase - BitVec.ofNat 64 (8 * room)) < BitVec.ofNat 64 (8 * room + 0x10000)
      then .rw else s.perm x :=
  State.perm_setPerm _ _ _ _ _

theorem mem_withArgs_below {x : BitVec 64} (hx : x.toNat < argBase.toNat) :
    (s.withArgs room args).mem x = s.mem x := by
  show ((s.setPerm _ _ _).storeBytes argBase (argBytes args)).mem x = s.mem x
  have hlen := argBytes_length_le args
  rw [State.mem_storeBytes _ _ _ _ (by omega), List.getElem?_eq_none (by
    have : argBase.toNat = 0x7fff0000 := rfl
    rw [BitVec.toNat_sub]
    omega)]
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

/-- A program loaded into a state given a stack with arguments meets the
entry contract with up to five slots at and above the stack pointer,
whatever the arguments are, if its code, data and blocks lie below the
stack. -/
theorem Entry.ofLoadArgs {p : State} (args : List (List Byte)) (hroom : 8 * room ≤ 0x10000)
    (habove : above ≤ 5) (hlen : image.length ≤ 2 ^ 64)
    (hdata : p.HasData dataBase data)
    (hfarData : base.toNat + image.length ≤ dataBase.toNat ∧
      dataBase.toNat + data.length ≤ 0x7ffe0000)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hfarBlocks : ∀ x ∈ blocks,
      base.toNat + image.length ≤ x.1.toNat ∧ x.1.toNat + x.2.size ≤ 0x7ffe0000)
    (hcode : base.toNat + image.length ≤ 0x7ffe0000) :
    Entry entry base image dataBase data blocks room above
      { (p.withArgs room args).loadCode base image with rip := entry } := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hsp := State.getReg_withArgs p room args
  -- below the stack, permissions are what they were
  have hperm : ∀ x : BitVec 64, x.toNat < 0x7ffe0000 → (p.withArgs room args).perm x = p.perm x := by
    intro x hx
    rw [State.perm_withArgs]
    split
    · next hin => exact absurd hin (by bv_omega)
    · rfl
  refine Entry.ofLoad hlen (by omega) (hdata.withArgs room args hfarData.2) ⟨hfarData.1, by omega⟩
    ?_ ?_ ?_ (fun x hx => ⟨(hfarBlocks x hx).1, by have := (hfarBlocks x hx).2; omega⟩)
    ⟨by rw [hsp, hbase]; omega, by rw [hsp, hbase]; omega⟩
  · intro x hx
    obtain ⟨hr, hw⟩ := hblocks x hx
    have hf := (hfarBlocks x hx).2
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
    rw [State.perm_withArgs]
    split
    · rfl
    · next hout => exact absurd (show _ < _ by bv_omega) hout
  · intro x hx
    have hf := (hfarBlocks x hx).2
    rw [hsp]
    refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> bv_omega

end TypedAsm
