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
what the memory blocks contain, so the blocks must have integer fields.
-/

namespace TypedAsm

/-- What a program needs of its starting state `s`: execution starts at
`entry`, the program's bytes are in executable memory at `base`, each memory
block has its permissions, and there are `room` writable stack slots below
`rsp` that overlap no block. -/
structure Entry (entry base : BitVec 64) (image : List Byte) (blocks : List (BitVec 64 × Layout))
    (room : Nat) (s : State) : Prop where
  rip : s.rip = entry
  code : s.HasCode base image
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

variable {entry base : BitVec 64} {image : List Byte} {blocks : List (BitVec 64 × Layout)}
  {room : Nat}

/-- A state meeting the entry contract matches the entry context. -/
theorem Entry.matches {H : Ty → BitVec 64 → Prop} {s : State}
    (h : Entry entry base image blocks room s) (hint : ∀ v, H .int v)
    (hfields : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    Matches H (MemTy.ofList blocks) (entryCtx room) s where
  regs := fun _ _ => hint _
  flags := trivial
  stackPerm := h.stack
  stackSize_lt := h.room_lt
  stack := fun i τ hi => by simp [entryCtx] at hi
  heapPerm := fun a l hl => h.perms (a, l) (MemTy.mem_of_ofList hl)
  heap := fun a l hl i τ hi => by
    rw [hfields (a, l) (MemTy.mem_of_ofList hl) τ (List.mem_of_getElem? hi)]
    exact hint _
  stackHeap := fun a l hl => h.apart (a, l) (MemTy.mem_of_ofList hl)

/-- The entry contract says nothing about the outside world: it holds
whatever there is to read. -/
theorem Entry.withWorld {s : State} (h : Entry entry base image blocks room s) (w : World) :
    Entry entry base image blocks room { s with world := w } :=
  ⟨h.rip, h.code, h.perms, h.stack, h.apart, h.room_lt⟩

/-- A state built by loading the program into a prepared state meets the
entry contract, if the prepared state has the blocks and the stack, and both
lie above the code. -/
theorem Entry.ofLoad {p : State} (hlen : image.length ≤ 2 ^ 64) (hroom : 8 * room < 2 ^ 64)
    (hblocks : ∀ x ∈ blocks,
      p.canRead x.1 x.2.size = true ∧ (x.2.writable = true → p.canWrite x.1 x.2.size = true))
    (hstack : p.canWrite (p.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * room) = true)
    (hapart : ∀ x ∈ blocks,
      Disjoint (p.getReg .rsp - BitVec.ofNat 64 (8 * room)) (8 * room) x.1 x.2.size)
    (hfarBlocks : ∀ x ∈ blocks,
      base.toNat + image.length ≤ x.1.toNat ∧ x.1.toNat + x.2.size ≤ 2 ^ 64)
    (hfarStack : base.toNat + image.length + 8 * room ≤ (p.getReg .rsp).toNat) :
    Entry entry base image blocks room { p.loadCode base image with rip := entry } := by
  have hp : ({ p.loadCode base image with rip := entry } : State).perm
      = (p.loadCode base image).perm := rfl
  have hsp : ({ p.loadCode base image with rip := entry } : State).getReg .rsp = p.getReg .rsp :=
    rfl
  refine ⟨rfl, (State.hasCode_loadCode p base image hlen).congr rfl rfl, ?_, ?_, ?_, hroom⟩
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
