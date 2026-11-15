import TypedAsm.Types
import TypedAsm.Safety

/-!
# Typing rules

Which instructions are allowed in which contexts, and what the context is
afterwards. An instruction form with no rule here is rejected.

The rules come in two layers. `Straight` covers instructions that always
continue to the next one, and says how they change the context. `HasType`
adds the instructions that transfer control, and checks every possible
successor address against the code typing.

A memory operand is `[register + constant]`, a field of a typed pointer or a
stack slot; `[register + index * scale + constant]`, a field chosen by an
exactly known index; or `[rip + constant]`, a field of a block at a fixed
address. A
whole 8-byte field or slot keeps its type when loaded or stored at 64 bits;
any other access, narrower or inside a field, reads and writes integers.

Every instruction of the machine has a rule. What the rules do not track:
an operation on values that are not exactly known gives a plain integer.
A divide is typed only when it is shown not to raise a divide error, which
needs its operands in registers holding exactly known values.
-/

namespace TypedAsm

/-! ## Subtyping -/

theorem Sub.rfl {τ : Ty} : Sub τ τ := .refl τ

theorem Sub.trans {τ υ φ : Ty} (h₁ : Sub τ υ) (h₂ : Sub υ φ) : Sub τ φ := by
  induction h₂ generalizing τ with
  | refl => exact h₁
  | int => exact .int _
  | readOnly shape w index =>
    cases h₁ with
    | refl => exact .readOnly shape w index
    | readOnly => exact .readOnly shape w index
  | refReadOnly tag w index =>
    cases h₁ with
    | refl => exact .refReadOnly tag w index
    | refReadOnly => exact .refReadOnly tag w index
  | nullable _ ih => exact .nullable (ih h₁)
  | null τ' =>
    cases h₁ with
    | refl => exact .null τ'
  | nullableMono h ih =>
    cases h₁ with
    | refl => exact .nullableMono h
    | nullable h' => exact .nullable (ih h')
    | null => exact .null _
    | nullableMono h' => exact .nullableMono (ih h')
  | strLess more =>
    cases h₁ with
    | refl => exact .strLess more
    | strLess => exact .strLess more
  | codeAll pre x =>
    cases h₁ with
    | refl => exact .codeAll pre x
    | codeAllMap pre' g => exact .codeAll pre' (g x)
  | codeAllMap pre f =>
    cases h₁ with
    | refl => exact .codeAllMap pre f
    | codeAllMap pre' g => exact .codeAllMap pre' (fun s => g (f s))
  | orErr _ ih => exact .orErr (ih h₁)
  | orErrMono h ih =>
    cases h₁ with
    | refl => exact .orErrMono h
    | orErr h' => exact .orErr (ih h')
    | orErrMono h' => exact .orErrMono (ih h')

/-- A caller ready for each chosen value is ready for each sequence, read as
the value it stands for. -/
theorem FnSigEx.CallerOk.toRaw {ι : Type} [Chosen ι] {sig : FnSigEx ι} {saved : Reg → Ty}
    {ret : ι → Ctx} {rest : List Shape} {room : Nat} {frame : List (BitVec 64 × Shape)}
    {above : Nat}
    (h : sig.CallerOk saved ret rest room frame above) :
    sig.raw.CallerOk saved (fun s => ret (Chosen.dec s)) rest room frame above :=
  ⟨fun s => h.each (Chosen.dec s), fun s => h.frame (Chosen.dec s),
    fun s => h.detached (Chosen.dec s)⟩

/-- A caller ready for each sequence is ready for each chosen value, written
as a sequence. -/
theorem FnSigEx.CallerOk.ofRaw {ι : Type} [Chosen ι] {sig : FnSigEx ι} {saved : Reg → Ty}
    {ret : (Nat → BitVec 64) → Ctx} {rest : List Shape} {room : Nat}
    {frame : List (BitVec 64 × Shape)} {above : Nat}
    (h : sig.raw.CallerOk saved ret rest room frame above) :
    sig.CallerOk saved (fun x => ret (Chosen.enc x)) rest room frame above := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => h.detached (Chosen.enc x)⟩
  · have := h.each (Chosen.enc x)
    simpa only [FnSigEx.raw, FnSigEx.pick, Chosen.dec_enc] using this
  · have := h.frame (Chosen.enc x)
    simpa only [FnSigEx.raw, Chosen.dec_enc] using this

theorem SubShape.refl (S : Shape) : SubShape S S :=
  ⟨rfl, fun q hq => ⟨q, hq, rfl, .refl _⟩⟩

/-- A typed value on the stack may be used at a weaker type. -/
theorem SubShape.slot {τ υ : Ty} (h : Sub τ υ) : SubShape (.slot τ) (.slot υ) :=
  ⟨rfl, fun q hq => by
    simp only [ShapeOf.slot, List.mem_singleton] at hq
    subst hq
    exact ⟨(0, τ), by simp [ShapeOf.slot], rfl, h⟩⟩

/-- What a piece of the stack holds may be forgotten: it is then plain bytes. -/
theorem SubShape.raw (S : Shape) : SubShape S (.raw S.size) :=
  ⟨rfl, fun q hq => by cases hq⟩

theorem SubList.refl : ∀ σ : List Shape, SubList σ σ
  | [] => .nil
  | S :: σ => .cons (.refl S) (SubList.refl σ)

theorem CtxSub.refl (Γ : Ctx) : CtxSub Γ Γ :=
  ⟨fun _ _ => .refl _, .refl _, rfl, fun _ h => h, .refl _, rfl, rfl⟩

/-- The code at `a` may be entered from a state matching `Γ`: one of the
contexts allowed there is `Γ` or weaker. -/
def Accepts (Φ : CodeTy) (a : BitVec 64) (Γ : Ctx) : Prop :=
  ∃ Δ, Φ a Δ ∧ CtxSub Γ Δ

/-! ## Changing a context -/

def CtxOf.setReg (Γ : Ctx) (r : Reg) (τ : Ty) : Ctx :=
  { Γ with regs := fun r' => if r' = r then τ else Γ.regs r' }

/-- The context after the stack pointer has moved by `d`: what was known of
its value is carried along. -/
def CtxOf.moveSp (Γ : Ctx) (d : BitVec 64) : Ctx :=
  { Γ with regs := fun r => if r = .rsp then (Γ.regs .rsp).shift d else Γ.regs r }

theorem CtxOf.moveSp_regs {Γ : Ctx} {d : BitVec 64} {r : Reg} (hr : r ≠ .rsp) :
    (Γ.moveSp d).regs r = Γ.regs r := by
  simp only [CtxOf.moveSp, hr, ↓reduceIte]

theorem CtxOf.moveSp_sp (Γ : Ctx) (d : BitVec 64) :
    (Γ.moveSp d).regs .rsp = (Γ.regs .rsp).shift d := by
  simp only [CtxOf.moveSp, ↓reduceIte]

/-- Moving by amounts that are equal gives the same type. -/
theorem Sub.shift_congr {τ : Ty} {a b : BitVec 64} (h : a = b) : Sub (τ.shift a) (τ.shift b) :=
  h ▸ .refl _

/-- Comparing a context whose stack pointer has just moved with another. -/
theorem CtxSub.ofMoved {Γ Δ : Ctx} {d : BitVec 64} {stack : List Shape} {room : Nat}
    (hregs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (Δ.regs r)) (hstack : SubList stack Δ.stack)
    (hroom : room = Δ.room) (hflags : ∀ f, Γ.flags f → Δ.flags f)
    (hsp : Sub ((Γ.regs .rsp).shift d) (Δ.regs .rsp)) (howned : Γ.owned = Δ.owned)
    (habove : Γ.above = Δ.above := by rfl) :
    CtxSub { Γ.moveSp d with stack := stack, room := room } Δ :=
  ⟨fun r hr => by
      show Sub ((Γ.moveSp d).regs r) _
      rw [CtxOf.moveSp_regs hr]
      exact hregs r hr,
    hstack, hroom, hflags, by
      show Sub ((Γ.moveSp d).regs .rsp) _
      rw [CtxOf.moveSp_sp]
      exact hsp, howned, habove⟩

/-- Whether the operation reads the carry flag. -/
def AluOp.readsCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

/-- The result and flags of an operation that does not read the carry flag.
(For the two that do, this is the result with the carry clear.) -/
def AluOp.apply {n : Nat} (op : AluOp) (a b : BitVec n) : BitVec n × Flags :=
  match op with
  | .add | .adc => addCarry a b false
  | .sub | .sbb | .cmp => subBorrow a b false
  | .and => (a &&& b, .ofResult (a &&& b) false false)
  | .or => (a ||| b, .ofResult (a ||| b) false false)
  | .xor => (a ^^^ b, .ofResult (a ^^^ b) false false)

/-- The context after a two-operand operation on register `d`: the flags
become known, and `d` holds an integer if the operation writes it. -/
def CtxOf.afterAlu (Γ : Ctx) (op : AluOp) (d : Reg) : Ctx :=
  { (bif op.writesDst then Γ.setReg d .int else Γ) with flags := Flags.Known }

/-- The context after a system call: the operating system may have changed
`rax`, `rcx`, `r11` and the flags. -/
def CtxOf.afterSyscall (Γ : Ctx) : Ctx :=
  { ((Γ.setReg .rax .int).setReg .rcx .int).setReg .r11 .int with flags := Flags.Any }

/-- The displacement `disp` reaches byte `d` from where a pointer points. -/
structure byteDisp (d : Nat) (disp : BitVec 32) : Prop where
  eq : disp = BitVec.ofNat 32 d
  lt : d < 2 ^ 31

/-- The number of bytes in a narrow value. -/
def NarrowW.bytes : NarrowW → Nat
  | .w8 => 1
  | .w16 => 2

/-! ## Operands

Three judgments about an operand, each covering a register, a field of a
block reached through a pointer, and a stack slot. They let one rule serve
every instruction that takes such an operand. `n` is the access size in bytes. -/

/-- Address `p` is `off` bytes into the owned block listed at place `k`,
which is at `a` and has shape `S`. (A structure, so that finding the block
and checking the address are settled together.) -/
structure OwnedAt (owned : List (BitVec 64 × Shape)) (k : Nat) (a : BitVec 64) (S : Shape)
    (p off : BitVec 64) : Prop where
  entry : owned[k]? = some (a, S)
  addr : p = a + off

/-- `EaIs Γ m p`: the address the memory operand `m` names is exactly `p`,
because the registers it is computed from hold exactly known values. -/
inductive EaIs (Γ : Ctx) : Mem → BitVec 64 → Prop
  | base {b : Reg} {v : BitVec 64} {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .eq v → EaIs Γ (.sib (some b) none disp) (v + disp.signExtend 64)
  | indexed {b : Reg} {x : IndexReg} {sc : Scale} {v c : BitVec 64} {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .eq v → Γ.regs x.toReg = .eq c →
    EaIs Γ (.sib (some b) (some (x, sc)) disp) (v + (c <<< sc.shift) + disp.signExtend 64)

/-- As `OwnedAt.mk`, for a search among several blocks: the offset is also
shown to fall inside the block, so that a block the address is not in is
passed over. -/
theorem OwnedAt.of_inside {owned : List (BitVec 64 × Shape)} {k : Nat} {a : BitVec 64}
    {S : Shape} {p off : BitVec 64} (entry : owned[k]? = some (a, S)) (addr : p = a + off)
    (_inside : off.toNat < S.size) : OwnedAt owned k a S p off :=
  ⟨entry, addr⟩

/-- An address written from one place, seen from a block that starts at another. -/
theorem OwnedAt.addr_sub (v c d : BitVec 64) : v + c = v + d + (c - d) := by bv_omega

theorem OwnedAt.addr_sub' (v e c d : BitVec 64) : v + e + c = v + d + (e + c - d) := by bv_omega

/-- `StackAt σ k S d i`: byte `d` above the stack pointer is byte `i` of
piece `k` of the stack `σ`, and that piece is `S`. -/
structure StackAt (σ : List Shape) (k : Nat) (S : Shape) (d i : Nat) : Prop where
  entry : σ[k]? = some S
  off : d = stackOff σ k + i

/-- As `StackAt.mk`, for a search among the pieces: the byte is also shown to
fall inside the piece, so that a piece it is not in is passed over. -/
theorem StackAt.of_inside {σ : List Shape} {k : Nat} {S : Shape} {d i : Nat}
    (entry : σ[k]? = some S) (off : d = stackOff σ k + i) (_inside : i < S.size) :
    StackAt σ k S d i :=
  ⟨entry, off⟩

/-- `ReadOk Ψ next Γ n rm`: reading `n` bytes from `rm` is safe. For memory, the
bytes must lie inside one block or one piece of the stack. -/
inductive ReadOk (Ψ : MemTy) (next : BitVec 64) (Γ : Ctx) (n : Nat) : RM → Prop
  | reg (r : Reg) : ReadOk Ψ next Γ n (.reg r)
  | field {b : Reg} {S : Shape} {writable : Bool} {off d : Nat} {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .ptr S writable off → byteDisp d disp →
    off + d + n ≤ S.size → ReadOk Ψ next Γ n (.mem (.sib (some b) none disp))
  | slot {d k i : Nat} {S : Shape} {disp : BitVec 32} :
    byteDisp d disp → StackAt Γ.stack k S d i → i + n ≤ S.size →
    ReadOk Ψ next Γ n (.mem (.sib (some .rsp) none disp))
  /-- Bytes of the stack reached through an index holding an exactly known
  value. -/
  | slotIndexed {x : IndexReg} {sc : Scale} {d k i : Nat} {S : Shape} {disp : BitVec 32}
      {c : BitVec 64} :
    Γ.regs x.toReg = .eq c → (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d →
    StackAt Γ.stack k S d i → i + n ≤ S.size →
    ReadOk Ψ next Γ n (.mem (.sib (some .rsp) (some (x, sc)) disp))
  /-- An indexed access: the index register holds an exactly known value,
  and scaled and added to the displacement it lands inside the block. -/
  | indexed {b : Reg} {x : IndexReg} {sc : Scale} {S : Shape} {writable : Bool}
      {off d : Nat} {disp : BitVec 32} {c : BitVec 64} :
    b ≠ .rsp → Γ.regs b = .ptr S writable off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d →
    off + d + n ≤ S.size →
    ReadOk Ψ next Γ n (.mem (.sib (some b) (some (x, sc)) disp))
  /-- A global: bytes of a block, at a fixed distance from the next
  instruction. -/
  | global {base : BitVec 64} {l : Layout} {d : Nat} {disp : BitVec 32} :
    Ψ base = some l → next + disp.signExtend 64 = base + BitVec.ofNat 64 d →
    d + n ≤ l.shape.size → ReadOk Ψ next Γ n (.mem (.rip disp))
  /-- The byte of text a register points at. -/
  | text {b : Reg} {more : Bool} : b ≠ .rsp → Γ.regs b = .str more → n = 1 →
    ReadOk Ψ next Γ n (.mem (.sib (some b) none 0))
  /-- Bytes of an owned block: the base register holds an exactly known
  value that, with the displacement, lands `off` bytes into the block. -/
  | owned {m : Mem} {k : Nat} {a p off : BitVec 64} {S : Shape} :
    EaIs Γ m p → OwnedAt Γ.owned k a S p off → off.toNat + n ≤ S.size →
    ReadOk Ψ next Γ n (.mem m)

/-- `WriteIntOk Ψ next Γ n rm Γ'`: overwriting `n` bytes of `rm` with an arbitrary
value is safe and leaves a state matching `Γ'`. A register or stack slot
becomes an integer. A field must already be an integer field of a writable
block, since a field's type cannot change. -/
inductive WriteIntOk (Ψ : MemTy) (next : BitVec 64) (Γ : Ctx) (n : Nat) : RM → Ctx → Prop
  | reg {d : Reg} : d ≠ .rsp → WriteIntOk Ψ next Γ n (.reg d) (Γ.setReg d .int)
  | field {b : Reg} {S : Shape} {off d : Nat} {disp : BitVec 32} :
    b ≠ .rsp → Γ.regs b = .ptr S true off → byteDisp d disp →
    off + d + n ≤ S.size → S.free (off + d) n = true →
    WriteIntOk Ψ next Γ n (.mem (.sib (some b) none disp)) Γ
  /-- Any bytes of a piece of the stack. Whatever typed value reached into
  them is forgotten: the stack is the program's own. -/
  | slot {d k i : Nat} {S : Shape} {disp : BitVec 32} :
    byteDisp d disp → StackAt Γ.stack k S d i → i + n ≤ S.size →
    WriteIntOk Ψ next Γ n (.mem (.sib (some .rsp) none disp))
      { Γ with stack := Γ.stack.set k (S.clear i n) }
  | slotIndexed {x : IndexReg} {sc : Scale} {d k i : Nat} {S : Shape} {disp : BitVec 32}
      {c : BitVec 64} :
    Γ.regs x.toReg = .eq c → (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d →
    StackAt Γ.stack k S d i → i + n ≤ S.size →
    WriteIntOk Ψ next Γ n (.mem (.sib (some .rsp) (some (x, sc)) disp))
      { Γ with stack := Γ.stack.set k (S.clear i n) }
  | indexed {b : Reg} {x : IndexReg} {sc : Scale} {S : Shape} {off d : Nat}
      {disp : BitVec 32} {c : BitVec 64} :
    b ≠ .rsp → Γ.regs b = .ptr S true off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d →
    off + d + n ≤ S.size → S.free (off + d) n = true →
    WriteIntOk Ψ next Γ n (.mem (.sib (some b) (some (x, sc)) disp)) Γ
  | global {base : BitVec 64} {l : Layout} {d : Nat} {disp : BitVec 32} :
    Ψ base = some l → l.writable = true →
    next + disp.signExtend 64 = base + BitVec.ofNat 64 d →
    d + n ≤ l.shape.size → l.shape.free d n = true →
    WriteIntOk Ψ next Γ n (.mem (.rip disp)) Γ
  /-- Plain bytes of an owned block: no typed value reaches into them. -/
  | owned {m : Mem} {k : Nat} {a p off : BitVec 64} {S : Shape} :
    EaIs Γ m p → OwnedAt Γ.owned k a S p off → off.toNat + n ≤ S.size →
    S.free off.toNat n = true → WriteIntOk Ψ next Γ n (.mem m) Γ
  /-- Any bytes of an owned block. Whatever typed value reached into them is
  forgotten: nothing else looks at an owned block, so its bytes may be given
  up as plain ones. -/
  | ownedClear {m : Mem} {k : Nat} {a p off : BitVec 64} {S : Shape} :
    EaIs Γ m p → OwnedAt Γ.owned k a S p off → off.toNat + n ≤ S.size →
    WriteIntOk Ψ next Γ n (.mem m)
      { Γ with owned := Γ.owned.set k (a, S.clear off.toNat n) }

/-- `Holds Ψ next Γ rm τ`: `rm` is a register, a typed value of a block or a
typed value on the stack, holding a value of type `τ`. -/
inductive Holds (Ψ : MemTy) (next : BitVec 64) (Γ : Ctx) : RM → Ty → Prop
  | indexed {b : Reg} {x : IndexReg} {sc : Scale} {S : Shape} {writable : Bool}
      {off d : Nat} {disp : BitVec 32} {c : BitVec 64} {τ : Ty} :
    b ≠ .rsp → Γ.regs b = .ptr S writable off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d →
    S.valAt (off + d) = some τ →
    Holds Ψ next Γ (.mem (.sib (some b) (some (x, sc)) disp)) τ
  | global {base : BitVec 64} {l : Layout} {d : Nat} {disp : BitVec 32} {τ : Ty} :
    Ψ base = some l → next + disp.signExtend 64 = base + BitVec.ofNat 64 d →
    l.shape.valAt d = some τ → Holds Ψ next Γ (.mem (.rip disp)) τ
  | reg {r : Reg} {τ : Ty} : r ≠ .rsp → Γ.regs r = τ → Holds Ψ next Γ (.reg r) τ
  | field {b : Reg} {S : Shape} {writable : Bool} {off d : Nat} {disp : BitVec 32}
      {τ : Ty} :
    b ≠ .rsp → Γ.regs b = .ptr S writable off → byteDisp d disp →
    S.valAt (off + d) = some τ → Holds Ψ next Γ (.mem (.sib (some b) none disp)) τ
  | slot {d k i : Nat} {S : Shape} {disp : BitVec 32} {τ : Ty} :
    byteDisp d disp → StackAt Γ.stack k S d i → S.valAt i = some τ →
    Holds Ψ next Γ (.mem (.sib (some .rsp) none disp)) τ

/-- At least the named flags are defined. -/
def Flags.Defined (cf zf sf of : Bool) : Flags → Prop :=
  fun f => (cf = true → f.cf.isSome = true) ∧ (zf = true → f.zf.isSome = true) ∧
    (sf = true → f.sf.isSome = true) ∧ (of = true → f.of.isSome = true)

/-- Whether a condition reads only flags among the named ones. -/
def Cond.within (c : Cond) (cf zf sf of : Bool) : Bool :=
  match c with
  | .o | .no => of
  | .b | .ae => cf
  | .e | .ne => zf
  | .be | .a => cf && zf
  | .s | .ns => sf
  | .l | .ge => sf && of
  | .le | .g => zf && sf && of

/-- What is known about the flags after a shift or rotate by `c`, where `c`
has been reduced modulo the operand width. A count of zero leaves them as
they were. Otherwise a shift defines carry, zero and sign, a rotate only
carry, and either defines overflow only for a count of one. -/
def ShiftOp.flagsAfter (op : ShiftOp) (c : Nat) (old : Flags → Prop) : Flags → Prop :=
  if c = 0 then old else
  match op with
  | .shl | .shr | .sar => Flags.Defined true true true (c == 1)
  | .rol | .ror => Flags.Defined true false false (c == 1)

/-- The value a shift or rotate by `c` produces, where `c` has been reduced
modulo the operand width. -/
def ShiftOp.apply {n : Nat} (op : ShiftOp) (a : BitVec n) (c : Nat) : BitVec n :=
  match op with
  | .shl => a <<< c
  | .shr => a >>> c
  | .sar => a.sshiftRight c
  | .rol => a.rotateLeft c
  | .ror => a.rotateRight c

/-- After a multiply, only carry and overflow are defined. -/
abbrev Flags.AfterMul : Flags → Prop := Flags.Defined true false false true

/-- The context after a multiply or divide: `rax` and `rdx` hold the result,
and the flags satisfy `P`. -/
def CtxOf.afterMulDiv (Γ : Ctx) (P : Flags → Prop) : Ctx :=
  { (Γ.setReg .rax .int).setReg .rdx .int with flags := P }

/-! ## Instructions that continue to the next one -/

/-- `Straight Ψ next Γ i Γ'`: in a state matching `Γ`, instruction `i` executes
safely and leaves a state matching `Γ'`. `next` is the address of the
following instruction. The stack pointer is never an explicit destination,
except to allocate or release a frame. -/
inductive Straight (Ψ : MemTy) (next : BitVec 64) : Ctx → Instr → Ctx → Prop
  | nop {Γ : Ctx} : Straight Ψ next Γ .nop Γ
  /-- A 64-bit register copy carries the type along. -/
  | movRR64 {Γ : Ctx} {d s : Reg} : d ≠ .rsp → s ≠ .rsp →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.reg d) s)) (Γ.setReg d (Γ.regs s))
  /-- A 32-bit register copy keeps only the low half, so the result is an integer. -/
  | movRR32 {Γ : Ctx} {d s : Reg} : d ≠ .rsp →
    Straight Ψ next Γ (.mov .w32 (.rm_r (.reg d) s)) (Γ.setReg d .int)
  /-- Loading a constant gives exactly that value. -/
  | movRI {Γ : Ctx} {w : Width} {d : Reg} {imm : BitVec 32} : d ≠ .rsp →
    Straight Ψ next Γ (.mov w (.rm_i (.reg d) imm))
      (Γ.setReg d (.eq ((imm.signExtend w.bits).setWidth 64)))
  | movAbs {Γ : Ctx} {d : Reg} {imm : BitVec 64} : d ≠ .rsp →
    Straight Ψ next Γ (.movAbs d imm) (Γ.setReg d (.eq imm))
  /-- A `rip`-relative `lea` computes a known address: the address of the
  next instruction plus the displacement. -/
  | leaRip {Γ : Ctx} {d : Reg} {disp : BitVec 32} : d ≠ .rsp →
    Straight Ψ next Γ (.lea .w64 d (.rip disp)) (Γ.setReg d (.eq (next + disp.signExtend 64)))
  /-- The address of something on the stack, when the stack pointer's value
  is known. -/
  | leaSp {Γ : Ctx} {d : Reg} {disp : BitVec 32} {v : BitVec 64} :
    d ≠ .rsp → Γ.regs .rsp = .eq v →
    Straight Ψ next Γ (.lea .w64 d (.sib (some .rsp) none disp))
      (Γ.setReg d (.eq (v + disp.signExtend 64)))
  /-- `lea` only computes an address; the result is an integer. -/
  | lea {Γ : Ctx} {w : Width} {d : Reg} {m : Mem} : d ≠ .rsp →
    Straight Ψ next Γ (.lea w d m) (Γ.setReg d .int)
  /-- Load the typed value `k` bytes past where a register points. -/
  | loadField {Γ : Ctx} {d b : Reg} {S : Shape} {writable : Bool} {off k : Nat}
      {disp : BitVec 32} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr S writable off → byteDisp k disp →
    S.valAt (off + k) = some τ →
    Straight Ψ next Γ (.mov .w64 (.r_m d (.sib (some b) none disp))) (Γ.setReg d τ)
  /-- Store over the typed value `k` bytes past where a writable pointer
  points. The stored value must have that value's type. -/
  | storeField {Γ : Ctx} {b s : Reg} {S : Shape} {off k : Nat} {disp : BitVec 32}
      {τ : Ty} :
    b ≠ .rsp → s ≠ .rsp → Γ.regs b = .ptr S true off → byteDisp k disp →
    S.valAt (off + k) = some τ → S.sole (off + k) = true → Sub (Γ.regs s) τ →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.sib (some b) none disp)) s)) Γ
  /-- Load a whole field of an owned block, keeping its type. -/
  | loadOwned {Γ : Ctx} {d : Reg} {m : Mem} {k : Nat} {a p off : BitVec 64} {S : Shape}
      {τ : Ty} :
    d ≠ .rsp → EaIs Γ m p → OwnedAt Γ.owned k a S p off → S.valAt off.toNat = some τ →
    Straight Ψ next Γ (.mov .w64 (.r_m d m)) (Γ.setReg d τ)
  /-- Store eight bytes into an owned block. They take the type of what is
  stored, whatever was there before: nothing else looks at them. -/
  | storeOwned {Γ : Ctx} {s : Reg} {m : Mem} {k : Nat} {a p off : BitVec 64} {S : Shape} :
    s ≠ .rsp → EaIs Γ m p → OwnedAt Γ.owned k a S p off → off.toNat + 8 ≤ S.size →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem m) s))
      { Γ with owned := Γ.owned.set k (a, S.set off.toNat (Γ.regs s)) }
  /-- Store over a typed value of an owned block a value of the type it has
  already: the context stays as it is. This is the store to use where the
  place is not known exactly, as in a loop over an array of addresses. -/
  | storeOwnedKeep {Γ : Ctx} {s : Reg} {m : Mem} {k : Nat} {a p off : BitVec 64} {S : Shape}
      {τ : Ty} :
    s ≠ .rsp → EaIs Γ m p → OwnedAt Γ.owned k a S p off → S.valAt off.toNat = some τ →
    S.sole off.toNat = true → Sub (Γ.regs s) τ →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem m) s)) Γ
  /-- Load a typed value through an index, keeping its type. -/
  | loadIndexed {Γ : Ctx} {d b : Reg} {x : IndexReg} {sc : Scale} {S : Shape}
      {writable : Bool} {off k : Nat} {disp : BitVec 32} {c : BitVec 64} {τ : Ty} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .ptr S writable off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 k →
    S.valAt (off + k) = some τ →
    Straight Ψ next Γ (.mov .w64 (.r_m d (.sib (some b) (some (x, sc)) disp))) (Γ.setReg d τ)
  /-- Store over a typed value through an index. The stored value must have
  that value's type. -/
  | storeIndexed {Γ : Ctx} {b s : Reg} {x : IndexReg} {sc : Scale} {S : Shape}
      {off k : Nat} {disp : BitVec 32} {c : BitVec 64} {τ : Ty} :
    b ≠ .rsp → s ≠ .rsp → Γ.regs b = .ptr S true off → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 k →
    S.valAt (off + k) = some τ → S.sole (off + k) = true → Sub (Γ.regs s) τ →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.sib (some b) (some (x, sc)) disp)) s)) Γ
  /-- Load a typed value of a block at a fixed address, keeping its type. -/
  | loadGlobal {Γ : Ctx} {d : Reg} {base : BitVec 64} {l : Layout} {k : Nat} {disp : BitVec 32}
      {τ : Ty} :
    d ≠ .rsp → Ψ base = some l → next + disp.signExtend 64 = base + BitVec.ofNat 64 k →
    l.shape.valAt k = some τ → Straight Ψ next Γ (.mov .w64 (.r_m d (.rip disp))) (Γ.setReg d τ)
  /-- Store over a typed value of a writable block at a fixed address. The
  stored value must have that value's type. -/
  | storeGlobal {Γ : Ctx} {s : Reg} {base : BitVec 64} {l : Layout} {k : Nat} {disp : BitVec 32}
      {τ : Ty} :
    s ≠ .rsp → Ψ base = some l → l.writable = true →
    next + disp.signExtend 64 = base + BitVec.ofNat 64 k → l.shape.valAt k = some τ →
    l.shape.sole k = true → Sub (Γ.regs s) τ → Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.rip disp)) s)) Γ
  /-- Load a typed value from the stack. -/
  | loadStack {Γ : Ctx} {r : Reg} {d k i : Nat} {S : Shape} {disp : BitVec 32} {τ : Ty} :
    r ≠ .rsp → byteDisp d disp → StackAt Γ.stack k S d i → S.valAt i = some τ →
    Straight Ψ next Γ (.mov .w64 (.r_m r (.sib (some .rsp) none disp))) (Γ.setReg r τ)
  /-- Load the typed value on the stack that an index picks out. The index
  register holds an exactly known value. This is how a program gets at an
  argument whose number it has computed. -/
  | loadStackIndexed {Γ : Ctx} {r : Reg} {x : IndexReg} {sc : Scale} {d k i : Nat} {S : Shape}
      {disp : BitVec 32} {c : BitVec 64} {τ : Ty} :
    r ≠ .rsp → Γ.regs x.toReg = .eq c →
    (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d →
    StackAt Γ.stack k S d i → S.valAt i = some τ →
    Straight Ψ next Γ (.mov .w64 (.r_m r (.sib (some .rsp) (some (x, sc)) disp))) (Γ.setReg r τ)
  /-- Store eight bytes into the stack. They take the type of what is stored,
  whatever was there before. -/
  | storeStack {Γ : Ctx} {s : Reg} {d k i : Nat} {S : Shape} {disp : BitVec 32} :
    s ≠ .rsp → byteDisp d disp → StackAt Γ.stack k S d i → i + 8 ≤ S.size →
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none disp)) s))
      { Γ with stack := Γ.stack.set k (S.set i (Γ.regs s)) }
  | push {Γ : Ctx} {r : Reg} {n : Nat} : r ≠ .rsp → Γ.room = n + 8 →
    Straight Ψ next Γ (.push r)
      { Γ.moveSp (-8) with stack := .slot (Γ.regs r) :: Γ.stack, room := n }
  | pop {Γ : Ctx} {r : Reg} {τ : Ty} {σ : List Shape} : r ≠ .rsp → Γ.stack = .slot τ :: σ →
    Straight Ψ next Γ (.pop r)
      (CtxOf.setReg { Γ.moveSp 8 with stack := σ, room := Γ.room + 8 } r τ)
  /-- Pop eight bytes that are not known to be one typed value: a number. -/
  | popPlain {Γ : Ctx} {r : Reg} {S : Shape} {σ : List Shape} :
    r ≠ .rsp → Γ.stack = S :: σ → S.size = 8 →
    Straight Ψ next Γ (.pop r)
      (CtxOf.setReg { Γ.moveSp 8 with stack := σ, room := Γ.room + 8 } r .int)
  /-- Arithmetic between registers. The result is an integer whatever the operands were. -/
  | aluRR {Γ : Ctx} {op : AluOp} {w : Width} {d s : Reg} :
    d ≠ .rsp → (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.rm_r (.reg d) s)) (Γ.afterAlu op d)
  | aluRI {Γ : Ctx} {op : AluOp} {w : Width} {d : Reg} {imm : BitVec 32} :
    d ≠ .rsp → (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.rm_i (.reg d) imm)) (Γ.afterAlu op d)
  /-- Arithmetic on an exactly known value with a constant: the result and
  the flags are exactly known too. -/
  | aluExact {Γ : Ctx} {op : AluOp} {d : Reg} {imm : BitVec 32} {a : BitVec 64} :
    d ≠ .rsp → Γ.regs d = .eq a → op.readsCarry = false →
    Straight Ψ next Γ (.alu op .w64 (.rm_i (.reg d) imm))
      { (bif op.writesDst then Γ.setReg d (.eq (op.apply a (imm.signExtend 64)).1) else Γ) with
        flags := (· = (op.apply a (imm.signExtend 64)).2) }
  /-- Arithmetic between two exactly known values. -/
  | aluExactRR {Γ : Ctx} {op : AluOp} {d s : Reg} {a b : BitVec 64} :
    d ≠ .rsp → s ≠ .rsp → Γ.regs d = .eq a → Γ.regs s = .eq b → op.readsCarry = false →
    Straight Ψ next Γ (.alu op .w64 (.rm_r (.reg d) s))
      { (bif op.writesDst then Γ.setReg d (.eq (op.apply a b).1) else Γ) with
        flags := (· = (op.apply a b).2) }
  /-- Reserve `k` bytes of stack: one piece of plain bytes. -/
  | allocFrame {Γ : Ctx} {k m : Nat} {imm : BitVec 32} :
    byteDisp k imm → Γ.room = m + k →
    Straight Ψ next Γ (.alu .sub .w64 (.rm_i (.reg .rsp) imm))
      { Γ.moveSp (-BitVec.ofNat 64 k) with
        stack := .raw k :: Γ.stack, room := m, flags := Flags.Known }
  /-- Release the pieces at the top of the stack that come to `k` bytes. -/
  | freeFrame {Γ : Ctx} {k : Nat} {imm : BitVec 32} {top rest : List Shape} :
    byteDisp k imm → Γ.stack = top ++ rest → stackLen top = k →
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm))
      { Γ.moveSp (BitVec.ofNat 64 k) with
        stack := rest, room := Γ.room + k, flags := Flags.Known }
  /-- Advancing a pointer keeps it a pointer into the same block, that many
  bytes on. -/
  | addPtr {Γ : Ctx} {d : Reg} {S : Shape} {writable : Bool} {off k : Nat}
      {imm : BitVec 32} :
    d ≠ .rsp → Γ.regs d = .ptr S writable off → byteDisp k imm →
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg d) imm))
      { Γ.setReg d (.ptr S writable (off + k)) with flags := Flags.Known }
  /-- Step to the next byte of a text, from one known not to be its last. -/
  | strNext {Γ : Ctx} {d : Reg} :
    d ≠ .rsp → Γ.regs d = .str true →
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg d) 1))
      { Γ.setReg d (.str false) with flags := Flags.Known }
  -- The rules below are stated over operands, so each covers registers,
  -- fields and stack slots at once. Where an operand is written, its new
  -- contents are an integer.
  /-- Arithmetic that writes its destination, with a register source. -/
  | aluStoreR {Γ Γ' : Ctx} {op : AluOp} {w : Width} {dst : RM} {s : Reg} :
    op.writesDst = true → ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.rm_r dst s)) { Γ' with flags := Flags.Known }
  /-- Arithmetic that writes its destination, with a constant source. -/
  | aluStoreI {Γ Γ' : Ctx} {op : AluOp} {w : Width} {dst : RM} {imm : BitVec 32} :
    op.writesDst = true → ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.rm_i dst imm)) { Γ' with flags := Flags.Known }
  /-- A comparison with a register. -/
  | cmpR {Γ : Ctx} {op : AluOp} {w : Width} {dst : RM} {s : Reg} :
    op.writesDst = false → ReadOk Ψ next Γ w.bytes.toNat dst →
    Straight Ψ next Γ (.alu op w (.rm_r dst s)) { Γ with flags := Flags.Known }
  /-- A comparison with a constant. -/
  | cmpI {Γ : Ctx} {op : AluOp} {w : Width} {dst : RM} {imm : BitVec 32} :
    op.writesDst = false → ReadOk Ψ next Γ w.bytes.toNat dst →
    Straight Ψ next Γ (.alu op w (.rm_i dst imm)) { Γ with flags := Flags.Known }
  /-- Arithmetic into a register from memory. -/
  | aluLoad {Γ : Ctx} {op : AluOp} {w : Width} {d : Reg} {m : Mem} :
    d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat (.mem m) →
    (op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true) →
    Straight Ψ next Γ (.alu op w (.r_m d m)) (Γ.afterAlu op d)
  | testRM {Γ : Ctx} {w : Width} {dst : RM} {src : RI} : ReadOk Ψ next Γ w.bytes.toNat dst →
    Straight Ψ next Γ (.test w dst src) { Γ with flags := Flags.Known }
  | negRM {Γ Γ' : Ctx} {w : Width} {dst : RM} :
    ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    Straight Ψ next Γ (.unary .neg w dst) { Γ' with flags := Flags.Known }
  /-- `not` leaves the flags alone. -/
  | notRM {Γ Γ' : Ctx} {w : Width} {dst : RM} :
    ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    Straight Ψ next Γ (.unary .not w dst) Γ'
  /-- A shift or rotate by a constant. The count decides which flags are
  defined afterwards. -/
  | shiftImm {Γ Γ' : Ctx} {op : ShiftOp} {w : Width} {dst : RM} {n : BitVec 8} :
    ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    Straight Ψ next Γ (.shift op w dst (.imm n))
      { Γ' with flags := op.flagsAfter (n.toNat % w.bits) Γ.flags }
  /-- A shift or rotate by `cl`. The count may be zero, which leaves the
  flags as they were, so nothing is known about them afterwards. -/
  | shiftCl {Γ Γ' : Ctx} {op : ShiftOp} {w : Width} {dst : RM} :
    ReadOk Ψ next Γ w.bytes.toNat dst → WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' →
    Straight Ψ next Γ (.shift op w dst .cl) { Γ' with flags := Flags.Any }
  | mulRM {Γ : Ctx} {w : Width} {src : RM} : ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.mulDiv .mul w src) (Γ.afterMulDiv Flags.AfterMul)
  | imulRM {Γ : Ctx} {w : Width} {src : RM} : ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.mulDiv .imul w src) (Γ.afterMulDiv Flags.AfterMul)
  | imul2RM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.imul2 w d src) { Γ.setReg d .int with flags := Flags.AfterMul }
  | imul3RM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} {imm : BitVec 32} :
    d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.imul3 w d src imm) { Γ.setReg d .int with flags := Flags.AfterMul }
  | popcntRM {Γ : Ctx} {w : Width} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat src →
    Straight Ψ next Γ (.popcnt w d src) { Γ.setReg d .int with flags := Flags.Known }
  | bswap {Γ : Ctx} {w : Width} {r : Reg} : r ≠ .rsp →
    Straight Ψ next Γ (.bswap w r) (Γ.setReg r .int)
  | cdq {Γ : Ctx} : Straight Ψ next Γ .cdq (Γ.setReg .rdx .int)
  | cqo {Γ : Ctx} : Straight Ψ next Γ .cqo (Γ.setReg .rdx .int)
  | movsxdRM {Γ : Ctx} {d : Reg} {src : RM} : d ≠ .rsp → ReadOk Ψ next Γ 4 src →
    Straight Ψ next Γ (.movsxd d src) (Γ.setReg d .int)
  /-- A conditional move needs flags that decide the condition. The
  destination is an integer afterwards whichever way it went. -/
  | cmovRM {Γ : Ctx} {c : Cond} {w : Width} {d : Reg} {src : RM} :
    d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat src → (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    Straight Ψ next Γ (.cmov c w d src) (Γ.setReg d .int)
  | setccRM {Γ Γ' : Ctx} {c : Cond} {dst : RM} :
    WriteIntOk Ψ next Γ 1 dst Γ' → (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    Straight Ψ next Γ (.setcc c dst) Γ'
  | movzxRM {Γ : Ctx} {w : Width} {d : Reg} {sw : NarrowW} {src : RM} :
    d ≠ .rsp → ReadOk Ψ next Γ sw.bytes src → Straight Ψ next Γ (.movzx w d sw src) (Γ.setReg d .int)
  | movsxRM {Γ : Ctx} {w : Width} {d : Reg} {sw : NarrowW} {src : RM} :
    d ≠ .rsp → ReadOk Ψ next Γ sw.bytes src → Straight Ψ next Γ (.movsx w d sw src) (Γ.setReg d .int)
  /-- A load of any width, as an integer. The 64-bit loads of a whole field
  or slot above keep its type instead. -/
  | loadInt {Γ : Ctx} {w : Width} {d : Reg} {m : Mem} :
    d ≠ .rsp → ReadOk Ψ next Γ w.bytes.toNat (.mem m) →
    Straight Ψ next Γ (.mov w (.r_m d m)) (Γ.setReg d .int)
  /-- A store of any width, of a register, treated as an integer. -/
  | storeInt {Γ Γ' : Ctx} {w : Width} {dst : RM} {s : Reg} :
    WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' → Straight Ψ next Γ (.mov w (.rm_r dst s)) Γ'
  /-- A store of a constant. -/
  | storeImm {Γ Γ' : Ctx} {w : Width} {dst : RM} {imm : BitVec 32} :
    WriteIntOk Ψ next Γ w.bytes.toNat dst Γ' → Straight Ψ next Γ (.mov w (.rm_i dst imm)) Γ'
  /-- A byte store. -/
  | store8RM {Γ Γ' : Ctx} {m : Mem} {s : Reg} :
    WriteIntOk Ψ next Γ 1 (.mem m) Γ' → Straight Ψ next Γ (.store8 m s) Γ'
  /-- A 16-bit store. -/
  | store16RM {Γ Γ' : Ctx} {m : Mem} {s : Reg} :
    WriteIntOk Ψ next Γ 2 (.mem m) Γ' → Straight Ψ next Γ (.store16 m s) Γ'
  -- The rules below compute with exactly known values: when every register
  -- an instruction reads holds a known value, so does the one it writes.
  -- At 32 bits a value is cut to its low half first, and the result is
  -- extended with zeros, as the machine does.
  /-- Clearing a register by `xor` with itself. -/
  | xorSelf {Γ : Ctx} {w : Width} {d : Reg} : d ≠ .rsp →
    Straight Ψ next Γ (.alu .xor w (.rm_r (.reg d) d))
      { Γ.setReg d (.eq 0) with flags := (· = Flags.ofResult (0 : BitVec w.bits) false false) }
  | mov32Exact {Γ : Ctx} {d s : Reg} {a : BitVec 64} : d ≠ .rsp → s ≠ .rsp → Γ.regs s = .eq a →
    Straight Ψ next Γ (.mov .w32 (.rm_r (.reg d) s)) (Γ.setReg d (.eq ((a.setWidth 32).setWidth 64)))
  | aluExact32 {Γ : Ctx} {op : AluOp} {d : Reg} {imm : BitVec 32} {a : BitVec 64} :
    d ≠ .rsp → Γ.regs d = .eq a → op.readsCarry = false →
    Straight Ψ next Γ (.alu op .w32 (.rm_i (.reg d) imm))
      { (bif op.writesDst then
          Γ.setReg d (.eq ((op.apply (a.setWidth 32) (imm.signExtend 32)).1.setWidth 64))
        else Γ) with
        flags := (· = (op.apply (a.setWidth 32) (imm.signExtend 32)).2) }
  | aluExactRR32 {Γ : Ctx} {op : AluOp} {d s : Reg} {a b : BitVec 64} :
    d ≠ .rsp → s ≠ .rsp → Γ.regs d = .eq a → Γ.regs s = .eq b → op.readsCarry = false →
    Straight Ψ next Γ (.alu op .w32 (.rm_r (.reg d) s))
      { (bif op.writesDst then
          Γ.setReg d (.eq ((op.apply (a.setWidth 32) (b.setWidth 32)).1.setWidth 64))
        else Γ) with
        flags := (· = (op.apply (a.setWidth 32) (b.setWidth 32)).2) }
  | shiftExact {Γ : Ctx} {op : ShiftOp} {w : Width} {d : Reg} {n : BitVec 8} {a : BitVec 64} :
    d ≠ .rsp → Γ.regs d = .eq a →
    Straight Ψ next Γ (.shift op w (.reg d) (.imm n))
      { Γ.setReg d (.eq ((op.apply (a.setWidth w.bits) (n.toNat % w.bits)).setWidth 64)) with
        flags := op.flagsAfter (n.toNat % w.bits) Γ.flags }
  /-- An address computed from an exactly known base. -/
  | leaExactB {Γ : Ctx} {d b : Reg} {disp : BitVec 32} {a : BitVec 64} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .eq a →
    Straight Ψ next Γ (.lea .w64 d (.sib (some b) none disp))
      (Γ.setReg d (.eq (a + disp.signExtend 64)))
  /-- An address computed from an exactly known base and index. -/
  | leaExactBI {Γ : Ctx} {d b : Reg} {x : IndexReg} {sc : Scale} {disp : BitVec 32}
      {a c : BitVec 64} :
    d ≠ .rsp → b ≠ .rsp → Γ.regs b = .eq a → Γ.regs x.toReg = .eq c →
    Straight Ψ next Γ (.lea .w64 d (.sib (some b) (some (x, sc)) disp))
      (Γ.setReg d (.eq (a + (c <<< sc.shift) + disp.signExtend 64)))
  | negExact {Γ : Ctx} {w : Width} {d : Reg} {a : BitVec 64} : d ≠ .rsp → Γ.regs d = .eq a →
    Straight Ψ next Γ (.unary .neg w (.reg d))
      { Γ.setReg d (.eq ((subBorrow 0 (a.setWidth w.bits) false).1.setWidth 64)) with
        flags := (· = (subBorrow 0 (a.setWidth w.bits) false).2) }
  | notExact {Γ : Ctx} {w : Width} {d : Reg} {a : BitVec 64} : d ≠ .rsp → Γ.regs d = .eq a →
    Straight Ψ next Γ (.unary .not w (.reg d))
      (Γ.setReg d (.eq ((~~~(a.setWidth w.bits)).setWidth 64)))
  | imul2Exact {Γ : Ctx} {w : Width} {d r : Reg} {a b : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs d = .eq a → Γ.regs r = .eq b →
    Straight Ψ next Γ (.imul2 w d (.reg r))
      { Γ.setReg d (.eq ((imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).1.setWidth 64)) with
        flags := (· = (imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).2) }
  | imul3Exact {Γ : Ctx} {w : Width} {d r : Reg} {imm : BitVec 32} {b : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq b →
    Straight Ψ next Γ (.imul3 w d (.reg r) imm)
      { Γ.setReg d (.eq ((imulTrunc (b.setWidth w.bits) (imm.signExtend w.bits)).1.setWidth 64)) with
        flags := (· = (imulTrunc (b.setWidth w.bits) (imm.signExtend w.bits)).2) }
  /-- A multiply or divide of exactly known values that is known to produce
  a result. This is the only rule for a divide: a divide is typed only when
  it is shown not to raise a divide error. -/
  | mulDivExact {Γ : Ctx} {op : MulDivOp} {w : Width} {r : Reg} {a d b : BitVec 64}
      {lo hi : BitVec w.bits} {fl : Flags} :
    r ≠ .rsp → Γ.regs .rax = .eq a → Γ.regs .rdx = .eq d → Γ.regs r = .eq b →
    op.eval (d.setWidth w.bits) (a.setWidth w.bits) (b.setWidth w.bits) = .next (lo, hi, fl) →
    Straight Ψ next Γ (.mulDiv op w (.reg r))
      { (Γ.setReg .rax (.eq (lo.setWidth 64))).setReg .rdx (.eq (hi.setWidth 64)) with
        flags := (· = fl) }
  | cdqExact {Γ : Ctx} {a : BitVec 64} : Γ.regs .rax = .eq a →
    Straight Ψ next Γ .cdq (Γ.setReg .rdx (.eq ((signFill (a.setWidth 32)).setWidth 64)))
  | cqoExact {Γ : Ctx} {a : BitVec 64} : Γ.regs .rax = .eq a →
    Straight Ψ next Γ .cqo (Γ.setReg .rdx (.eq (signFill a)))
  | movsxdExact {Γ : Ctx} {d r : Reg} {a : BitVec 64} : d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.movsxd d (.reg r)) (Γ.setReg d (.eq ((a.setWidth 32).signExtend 64)))
  | movzxExact {Γ : Ctx} {w : Width} {sw : NarrowW} {d r : Reg} {a : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.movzx w d sw (.reg r))
      (Γ.setReg d (.eq (((a.setWidth sw.bits).setWidth w.bits).setWidth 64)))
  | movsxExact {Γ : Ctx} {w : Width} {sw : NarrowW} {d r : Reg} {a : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.movsx w d sw (.reg r))
      (Γ.setReg d (.eq (((a.setWidth sw.bits).signExtend w.bits).setWidth 64)))
  | popcntExact {Γ : Ctx} {w : Width} {d r : Reg} {a : BitVec 64} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.popcnt w d (.reg r))
      { Γ.setReg d (.eq ((popcount (a.setWidth w.bits)).setWidth 64)) with
        flags := (· = ⟨some false, some (a.setWidth w.bits == 0), some false, some false⟩) }
  | bswapExact {Γ : Ctx} {w : Width} {r : Reg} {a : BitVec 64} : r ≠ .rsp → Γ.regs r = .eq a →
    Straight Ψ next Γ (.bswap w r) (Γ.setReg r (.eq ((TypedAsm.bswap w (a.setWidth w.bits)).setWidth 64)))
  /-- A conditional move between exactly known values, when the flags say
  which way it goes. -/
  | cmovExact {Γ : Ctx} {c : Cond} {w : Width} {d r : Reg} {x a : BitVec 64} {b : Bool} :
    d ≠ .rsp → r ≠ .rsp → Γ.regs d = .eq x → Γ.regs r = .eq a →
    (∀ f, Γ.flags f → c.eval f = some b) →
    Straight Ψ next Γ (.cmov c w d (.reg r))
      (Γ.setReg d (.eq ((if b then a.setWidth w.bits else x.setWidth w.bits).setWidth 64)))
  | setccExact {Γ : Ctx} {c : Cond} {d : Reg} {x : BitVec 64} {b : Bool} :
    d ≠ .rsp → Γ.regs d = .eq x → (∀ f, Γ.flags f → c.eval f = some b) →
    Straight Ψ next Γ (.setcc c (.reg d))
      (Γ.setReg d (.eq ((x &&& ~~~0xff) ||| (if b then (1 : BitVec 8) else 0).setWidth 64)))
  /-- Testing two exactly known values gives exactly known flags. -/
  | testExact {Γ : Ctx} {r r' : Reg} {a b : BitVec 64} :
    r ≠ .rsp → r' ≠ .rsp → Γ.regs r = .eq a → Γ.regs r' = .eq b →
    Straight Ψ next Γ (.test .w64 (.reg r) (.reg r'))
      { Γ with flags := (· = Flags.ofResult (a &&& b) false false) }

/-! ## Rules keep holding when the memory typing grows

A rule looks at the memory typing only to find a block at a known address,
and a block that was there still is. -/

theorem ReadOk.ext {Ψ Ψ' : MemTy} {next : BitVec 64} {Γ : Ctx} {n : Nat} {rm : RM}
    (h : ReadOk Ψ next Γ n rm) (he : Ψ.Ext Ψ') : ReadOk Ψ' next Γ n rm := by
  cases h with
  | global hl => apply ReadOk.global (he.blocks _ _ hl) <;> assumption
  | _ =>
    first
    | exact .reg _
    | (apply ReadOk.field <;> assumption)
    | (apply ReadOk.slot <;> assumption)
    | (apply ReadOk.slotIndexed <;> assumption)
    | (apply ReadOk.indexed <;> assumption)
    | (apply ReadOk.text <;> assumption)
    | (apply ReadOk.owned <;> assumption)

theorem WriteIntOk.ext {Ψ Ψ' : MemTy} {next : BitVec 64} {Γ Γ' : Ctx} {n : Nat} {rm : RM}
    (h : WriteIntOk Ψ next Γ n rm Γ') (he : Ψ.Ext Ψ') : WriteIntOk Ψ' next Γ n rm Γ' := by
  cases h with
  | global hl => apply WriteIntOk.global (he.blocks _ _ hl) <;> assumption
  | _ =>
    first
    | (apply WriteIntOk.reg <;> assumption)
    | (apply WriteIntOk.field <;> assumption)
    | (apply WriteIntOk.slot <;> assumption)
    | (apply WriteIntOk.slotIndexed <;> assumption)
    | (apply WriteIntOk.indexed <;> assumption)
    | (apply WriteIntOk.owned <;> assumption)
    | (apply WriteIntOk.ownedClear <;> assumption)

theorem Holds.ext {Ψ Ψ' : MemTy} {next : BitVec 64} {Γ : Ctx} {rm : RM} {τ : Ty}
    (h : Holds Ψ next Γ rm τ) (he : Ψ.Ext Ψ') : Holds Ψ' next Γ rm τ := by
  cases h with
  | global hl => apply Holds.global (he.blocks _ _ hl) <;> assumption
  | _ =>
    first
    | (apply Holds.reg <;> assumption)
    | (apply Holds.field <;> assumption)
    | (apply Holds.slot <;> assumption)
    | (apply Holds.indexed <;> assumption)

/-- Closes a premise of a rule being carried to a larger memory typing. -/
local macro "ext_premise" : tactic =>
  `(tactic| first
    | assumption
    | exact ReadOk.ext (by assumption) (by assumption)
    | exact WriteIntOk.ext (by assumption) (by assumption))

/-- Carries a rule, whichever it is, to a larger memory typing. -/
local macro "ext_rule" : tactic =>
  `(tactic| first
    | (apply Straight.nop <;> ext_premise)
    | (apply Straight.movRR64 <;> ext_premise)
    | (apply Straight.movRR32 <;> ext_premise)
    | (apply Straight.movRI <;> ext_premise)
    | (apply Straight.movAbs <;> ext_premise)
    | (apply Straight.leaRip <;> ext_premise)
    | (apply Straight.leaSp <;> ext_premise)
    | (apply Straight.lea <;> ext_premise)
    | (apply Straight.loadField <;> ext_premise)
    | (apply Straight.storeField <;> ext_premise)
    | (apply Straight.loadIndexed <;> ext_premise)
    | (apply Straight.storeIndexed <;> ext_premise)
    | (apply Straight.loadStack <;> ext_premise)
    | (apply Straight.loadStackIndexed <;> ext_premise)
    | (apply Straight.strNext <;> ext_premise)
    | (apply Straight.loadOwned <;> ext_premise)
    | (apply Straight.storeOwned <;> ext_premise)
    | (apply Straight.storeOwnedKeep <;> ext_premise)
    | (apply Straight.storeStack <;> ext_premise)
    | (apply Straight.push <;> ext_premise)
    | (apply Straight.pop <;> ext_premise)
    | (apply Straight.popPlain <;> ext_premise)
    | (apply Straight.aluRR <;> ext_premise)
    | (apply Straight.aluRI <;> ext_premise)
    | (apply Straight.aluExact <;> ext_premise)
    | (apply Straight.aluExactRR <;> ext_premise)
    | (apply Straight.allocFrame <;> ext_premise)
    | (apply Straight.freeFrame <;> ext_premise)
    | (apply Straight.addPtr <;> ext_premise)
    | (apply Straight.aluStoreR <;> ext_premise)
    | (apply Straight.aluStoreI <;> ext_premise)
    | (apply Straight.cmpR <;> ext_premise)
    | (apply Straight.cmpI <;> ext_premise)
    | (apply Straight.aluLoad <;> ext_premise)
    | (apply Straight.testRM <;> ext_premise)
    | (apply Straight.negRM <;> ext_premise)
    | (apply Straight.notRM <;> ext_premise)
    | (apply Straight.shiftImm <;> ext_premise)
    | (apply Straight.shiftCl <;> ext_premise)
    | (apply Straight.mulRM <;> ext_premise)
    | (apply Straight.imulRM <;> ext_premise)
    | (apply Straight.imul2RM <;> ext_premise)
    | (apply Straight.imul3RM <;> ext_premise)
    | (apply Straight.popcntRM <;> ext_premise)
    | (apply Straight.bswap <;> ext_premise)
    | (apply Straight.cdq <;> ext_premise)
    | (apply Straight.cqo <;> ext_premise)
    | (apply Straight.movsxdRM <;> ext_premise)
    | (apply Straight.cmovRM <;> ext_premise)
    | (apply Straight.setccRM <;> ext_premise)
    | (apply Straight.movzxRM <;> ext_premise)
    | (apply Straight.movsxRM <;> ext_premise)
    | (apply Straight.loadInt <;> ext_premise)
    | (apply Straight.storeInt <;> ext_premise)
    | (apply Straight.storeImm <;> ext_premise)
    | (apply Straight.store8RM <;> ext_premise)
    | (apply Straight.store16RM <;> ext_premise)
    | (apply Straight.xorSelf <;> ext_premise)
    | (apply Straight.mov32Exact <;> ext_premise)
    | (apply Straight.aluExact32 <;> ext_premise)
    | (apply Straight.aluExactRR32 <;> ext_premise)
    | (apply Straight.shiftExact <;> ext_premise)
    | (apply Straight.leaExactB <;> ext_premise)
    | (apply Straight.leaExactBI <;> ext_premise)
    | (apply Straight.negExact <;> ext_premise)
    | (apply Straight.notExact <;> ext_premise)
    | (apply Straight.imul2Exact <;> ext_premise)
    | (apply Straight.imul3Exact <;> ext_premise)
    | (apply Straight.mulDivExact <;> ext_premise)
    | (apply Straight.cdqExact <;> ext_premise)
    | (apply Straight.cqoExact <;> ext_premise)
    | (apply Straight.movsxdExact <;> ext_premise)
    | (apply Straight.movzxExact <;> ext_premise)
    | (apply Straight.movsxExact <;> ext_premise)
    | (apply Straight.popcntExact <;> ext_premise)
    | (apply Straight.bswapExact <;> ext_premise)
    | (apply Straight.cmovExact <;> ext_premise)
    | (apply Straight.setccExact <;> ext_premise)
    | (apply Straight.testExact <;> ext_premise))

theorem Straight.ext {Ψ Ψ' : MemTy} {next : BitVec 64} {Γ Γ' : Ctx} {i : Instr}
    (h : Straight Ψ next Γ i Γ') (he : Ψ.Ext Ψ') : Straight Ψ' next Γ i Γ' := by
  cases h with
  | loadGlobal hd hl haddr hi => exact .loadGlobal hd (he.blocks _ _ hl) haddr hi
  | storeGlobal hs hl hwr haddr hi hso hsub =>
    exact .storeGlobal hs (he.blocks _ _ hl) hwr haddr hi hso hsub
  | _ => ext_rule

/-! ## System calls

What a system call does is up to the operating system, so a `syscall` is
typed by a fact about the operating system at that point in the program. -/

/-- From any state matching `Γ`, the system call returns to where it was made
with a state matching `Γ'`. The memory typing may have grown by then, both
before the call (`Ψ₁`) and because of it (`Ψ₂`): this is how a call that
allocates memory is typed. -/
def SysReturns (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ Γ' : Ctx) : Prop :=
  ∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, WellTyped fetch sys Ψ₁ n Γ s →
    ∃ s', sys s = .next s' ∧ s'.rip = s.rip ∧
      ∃ Ψ₂ : MemTy, Ψ₁.Ext Ψ₂ ∧ Ψ₂.WF ∧ WellTyped fetch sys Ψ₂ n Γ' s'

/-- From any state matching `Γ`, instruction `i` runs and continues at the
next instruction in a state matching one of the contexts `Γ' x`. This is
the escape from the rules above to an argument about states, for a single
instruction: a step whose effect depends on what it finds, such as reading a
byte that may or may not be the end of a text, is typed by proving this. -/
def StepsTo (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (next : BitVec 64) (Γ : Ctx) (i : Instr)
    {ι : Type} (Γ' : ι → Ctx) : Prop :=
  ∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → s.rip = next →
    ∃ s' x, exec sys i s = .next s' ∧ s'.rip = s.rip ∧
      ∃ Ψ₂ : MemTy, Ψ₁.Ext Ψ₂ ∧ Ψ₂.WF ∧ WellTyped fetch sys Ψ₂ n (Γ' x) s'

/-- From any state matching `Γ`, the system call ends the program. -/
def SysExits (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ : Ctx) : Prop :=
  ∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → ∃ c, sys s = .exit c

/-! ## All typed instructions -/

/-- `HasType Φ fetch sys Ψ next Γ i`: in a state matching `Γ`, instruction `i`
executes safely, and wherever control goes next, the code there accepts the
resulting state. `next` is the address of the following instruction. -/
inductive HasType (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (next : BitVec 64) :
    Ctx → Instr → Prop
  | straight {Γ Γ' : Ctx} {i : Instr} : Straight Ψ next Γ i Γ' → Accepts Φ next Γ' → HasType Φ fetch sys Ψ next Γ i
  | jmp {Γ : Ctx} {d : BitVec 32} : Accepts Φ (next + d.signExtend 64) Γ →
    HasType Φ fetch sys Ψ next Γ (.jmp (.rel d))
  /-- A conditional jump needs flags that decide the condition. Each
  successor must accept, and may assume which way the condition went. -/
  | jcc {Γ : Ctx} {c : Cond} {d : BitVec 32} :
    (∀ f, Γ.flags f → ∃ b, c.eval f = some b) →
    (∀ f, Γ.flags f → c.eval f = some true → Accepts Φ (next + d.signExtend 64) Γ) →
    (∀ f, Γ.flags f → c.eval f = some false → Accepts Φ next Γ) →
    HasType Φ fetch sys Ψ next Γ (.jcc c d)
  /-- A call pushes the return address, typed as a pointer to code expecting
  the context required at the instruction after the call. The callee sees it
  on top of the stack. -/
  | call {Γ ret : Ctx} {d : BitVec 32} {n : Nat} : Γ.room = n + 8 → Φ next ret →
    Accepts Φ (next + d.signExtend 64)
      { Γ.moveSp (-8) with stack := .slot (.code ret) :: Γ.stack, room := n } →
    HasType Φ fetch sys Ψ next Γ (.call (.rel d))
  /-- A call whose return address is typed as code ready for any of a family
  of contexts: the instruction after the call must be typed for each. The
  callee chooses which one it returns into, once it knows. -/
  | callAll {Γ : Ctx} {ret : (Nat → BitVec 64) → Ctx} {d : BitVec 32} {n : Nat} :
    Γ.room = n + 8 →
    (∀ x, Φ next (ret x)) →
    Accepts Φ (next + d.signExtend 64)
      { Γ.moveSp (-8) with stack := .slot (.codeAll ret) :: Γ.stack, room := n } →
    HasType Φ fetch sys Ψ next Γ (.call (.rel d))
  /-- A return needs a code pointer on top of the stack, and the state with it
  popped must match what that code requires. -/
  | ret {Γ Δ : Ctx} {σ : List Shape} : Γ.stack = .slot (.code Δ) :: σ →
    CtxSub { Γ.moveSp 8 with stack := σ, room := Γ.room + 8 } Δ →
    HasType Φ fetch sys Ψ next Γ .ret
  /-- A system call that returns. It is typed only where the operating
  system is shown to return to the next instruction with a state matching
  `Γ'`; there is no rule for a call about which nothing is known. -/
  | syscall {Γ Γ' : Ctx} : SysReturns fetch sys Ψ Γ Γ' → Accepts Φ next Γ' →
    HasType Φ fetch sys Ψ next Γ .syscall
  /-- A system call that ends the program. Nothing after it needs a type. -/
  | syscallExit {Γ : Ctx} : SysExits fetch sys Ψ Γ → HasType Φ fetch sys Ψ next Γ .syscall
  /-- Jump through a register, field or stack slot holding a code pointer. -/
  | jmpInd {Γ Δ : Ctx} {rm : RM} : Holds Ψ next Γ rm (.code Δ) → CtxSub Γ Δ →
    HasType Φ fetch sys Ψ next Γ (.jmp (.ind rm))
  /-- Call through a register, field or stack slot holding a code pointer.
  The callee sees the return address on top of the stack. -/
  | callInd {Γ Δ ret : Ctx} {rm : RM} {n : Nat} : Holds Ψ next Γ rm (.code Δ) → Γ.room = n + 8 → Φ next ret →
    CtxSub { Γ.moveSp (-8) with stack := .slot (.code ret) :: Γ.stack, room := n } Δ →
    HasType Φ fetch sys Ψ next Γ (.call (.ind rm))
  /-- A register holding exactly the address of a function may be treated as
  a pointer to that function, to be called by any caller. -/
  | fnPtr {Γ : Ctx} {i : Instr} {r : Reg} {a : BitVec 64} {sig : FnSig} :
    r ≠ .rsp → Γ.regs r = .eq a → sig.At Φ a →
    HasType Φ fetch sys Ψ next (Γ.setReg r sig.ty) i → HasType Φ fetch sys Ψ next Γ i
  /-- Call through a register, field or stack slot holding a function
  pointer. The conditions are those of a direct call to that function. -/
  | callFn {Γ ret : Ctx} {rm : RM} {sig : FnSig} {m : Nat} :
    Holds Ψ next Γ rm sig.ty → Γ.room = m + 8 → Φ next ret →
    (∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsIn (Γ.moveSp (-8)).regs r)) →
    Sub ((Γ.regs .rsp).shift (-8)) (sig.regsIn (Γ.moveSp (-8)).regs .rsp) →
    CtxSub (sig.returned (Γ.moveSp (-8)).regs Γ.stack m ret.owned Γ.above) ret → sig.need ≤ m →
    ret.owned.take sig.gives.length = sig.gives →
    Γ.owned = sig.takes ++ ret.owned.drop sig.gives.length →
    HasType Φ fetch sys Ψ next Γ (.call (.ind rm))
  /-- A register holding exactly the address of a function whose results
  depend on a value it chooses may be treated as a pointer to that function. -/
  | fnPtrAll {ι : Type} [Chosen ι] {Γ : Ctx} {i : Instr} {r : Reg} {a : BitVec 64}
      {sig : FnSigEx ι} :
    r ≠ .rsp → Γ.regs r = .eq a → sig.At Φ a →
    HasType Φ fetch sys Ψ next (Γ.setReg r sig.ty) i → HasType Φ fetch sys Ψ next Γ i
  /-- Call through a register, field or stack slot holding a pointer to such
  a function. The instruction after the call must be typed for every value
  the function may choose. -/
  | callFnAll {ι : Type} [Chosen ι] {Γ : Ctx} {ret : ι → Ctx} {rm : RM} {sig : FnSigEx ι}
      {m : Nat} {frame : List (BitVec 64 × Shape)} :
    Holds Ψ next Γ rm sig.ty → Γ.room = m + 8 → (∀ x, Φ next (ret x)) →
    (∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsIn (Γ.moveSp (-8)).regs r)) →
    Sub ((Γ.regs .rsp).shift (-8)) (sig.regsIn (Γ.moveSp (-8)).regs .rsp) →
    (∀ x, CtxSub ((sig.pick x).returned (Γ.moveSp (-8)).regs Γ.stack m (ret x).owned Γ.above) (ret x)) →
    sig.need ≤ m → (∀ x, (ret x).owned.take (sig.gives x).length = sig.gives x) →
    (∀ x, (ret x).owned.drop (sig.gives x).length = frame) →
    Γ.owned = sig.takes ++ frame →
    HasType Φ fetch sys Ψ next Γ (.call (.ind rm))
  /-- Jump to such a function through a pointer to it: a tail call, made on
  behalf of a caller that is ready for whatever value is chosen. -/
  | jmpFnAll {ι : Type} [Chosen ι] {Γ : Ctx} {ret : ι → Ctx} {rm : RM} {sig : FnSigEx ι}
      {saved : Reg → Ty} {rest : List Shape} {room : Nat} {frame : List (BitVec 64 × Shape)}
      {above : Nat} :
    Holds Ψ next Γ rm sig.ty → sig.CallerOk saved ret rest room frame above →
    CtxSub Γ (sig.entry saved ret rest room frame above) → HasType Φ fetch sys Ψ next Γ (.jmp (.ind rm))
  /-- Jump to a function through a pointer to it: a tail call, made on
  behalf of the caller the current function would have returned to. -/
  | jmpFn {Γ ret : Ctx} {rm : RM} {sig : FnSig} {saved : Reg → Ty} {rest : List Shape}
      {room : Nat} :
    Holds Ψ next Γ rm sig.ty → sig.CallerOk saved ret rest room →
    CtxSub Γ (sig.entry saved ret rest room) → HasType Φ fetch sys Ψ next Γ (.jmp (.ind rm))
  /-- An instruction shown, by an argument about states, to continue at the
  next instruction in one of a family of contexts, each of which the code
  there accepts. -/
  | sem {ι : Type} {Γ : Ctx} {Γ' : ι → Ctx} {i : Instr} :
    StepsTo fetch sys Ψ next Γ i Γ' → (∀ x, Accepts Φ next (Γ' x)) →
    HasType Φ fetch sys Ψ next Γ i
  /-- Any instruction is well typed in a context no state can match. This is
  how code that is never reached, such as a `ud2` after an impossible branch,
  is typed. -/
  | unreachable {Γ : Ctx} {i : Instr} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, ¬WellTyped fetch sys Ψ₁ n Γ s) →
    HasType Φ fetch sys Ψ next Γ i
  /-- A register holding exactly the address of typed code may be treated as
  a pointer to that code. This is how a code pointer that is not a return
  address comes into being. -/
  | codePtr {Γ Δ : Ctx} {i : Instr} {r : Reg} {a : BitVec 64} :
    r ≠ .rsp → Γ.regs r = .eq a → Φ a Δ →
    HasType Φ fetch sys Ψ next (Γ.setReg r (.code Δ)) i → HasType Φ fetch sys Ψ next Γ i
  /-- Case analysis on the state: if every state matching `Γ` matches one of
  a family of contexts, and the instruction is typed in each of them, it is
  typed in `Γ`. This is how a value that is only known to be an integer gets
  a name: the family has one context for each value it could be. -/
  | cover {ι : Type} {Γ : Ctx} {Γ' : ι → Ctx} {i : Instr} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF →
      ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → ∃ x, WellTyped fetch sys Ψ₁ n (Γ' x) s) →
    (∀ x, HasType Φ fetch sys Ψ next (Γ' x) i) → HasType Φ fetch sys Ψ next Γ i
  /-- The memory typing may be found larger than it was: if every state
  matching `Γ` matches one of a family of contexts once some blocks are
  added to the memory typing, and the instruction is typed in each of them,
  it is typed in `Γ`. This is how memory a program owns becomes memory it
  shares: the block joins the memory typing, for good. -/
  | grow {ι : Type} {Γ : Ctx} {Γ' : ι → Ctx} {i : Instr} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF → ∀ n s, WellTyped fetch sys Ψ₁ n Γ s →
      ∃ Ψ₂ : MemTy, Ψ₁.Ext Ψ₂ ∧ Ψ₂.WF ∧ ∃ x, WellTyped fetch sys Ψ₂ n (Γ' x) s) →
    (∀ x, HasType Φ fetch sys Ψ next (Γ' x) i) → HasType Φ fetch sys Ψ next Γ i
  /-- The rule of consequence: an instruction typed in `Γ'` is typed in any
  context whose matching states all match `Γ'`. This is the escape from the
  syntactic rules to an arbitrary argument about states. -/
  | weaken {Γ Γ' : Ctx} {i : Instr} :
    (∀ Ψ₁ : MemTy, Ψ.Ext Ψ₁ → Ψ₁.WF →
      ∀ n s, WellTyped fetch sys Ψ₁ n Γ s → WellTyped fetch sys Ψ₁ n Γ' s) →
    HasType Φ fetch sys Ψ next Γ' i → HasType Φ fetch sys Ψ next Γ i

/-! ## Programs and states -/

/-- A program is well typed if, for every address and every context the code
typing allows there, the address holds an instruction that is well typed in
that context. -/
def ProgramOk (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) : Prop :=
  ∀ a Γ, Φ a Γ → ∃ i len, fetch a = some (i, len) ∧ HasType Φ fetch sys Ψ (a + len) Γ i

/-- A state is well typed if it matches a context the code typing allows at
its `rip`, at every step count. -/
def StateOk (Φ : CodeTy) (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (s : State) : Prop :=
  ∃ Γ, Φ s.rip Γ ∧ ∀ n, WellTyped fetch sys Ψ n Γ s

/-- The store that gives owned bytes a type, kept for values that have one:
a plain number is better stored as plain bytes, which stay plain. -/
theorem Straight.storeOwnedTyped {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {s : Reg} {m : Mem}
    {k : Nat} {a p off : BitVec 64} {S : Shape} (hs : s ≠ .rsp) (he : EaIs Γ m p)
    (hat : OwnedAt Γ.owned k a S p off) (hin : off.toNat + 8 ≤ S.size)
    (_typed : (Γ.regs s).isInt = false) :
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem m) s))
      { Γ with owned := Γ.owned.set k (a, S.set off.toNat (Γ.regs s)) } :=
  .storeOwned hs he hat hin

/-- Where an address falls in an owned block, as a number of bytes: the
block at place `k` is at `a` with shape `S`, and the address is `j` bytes
into it. For an index that is not known exactly, where the offset cannot be
worked out as a number. -/
structure OwnedByte (owned : List (BitVec 64 × Shape)) (k : Nat) (a : BitVec 64) (S : Shape)
    (p : BitVec 64) (j : Nat) : Prop where
  entry : owned[k]? = some (a, S)
  addr : p = a + BitVec.ofNat 64 j
  fit : S.size ≤ 2 ^ 64

theorem OwnedByte.toNat {owned : List (BitVec 64 × Shape)} {k : Nat} {a p : BitVec 64}
    {S : Shape} {j : Nat} (h : OwnedByte owned k a S p j) (hj : j < S.size) :
    (BitVec.ofNat 64 j).toNat = j := by
  have := h.fit
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Reading bytes of an owned block, the first given by its number. -/
theorem ReadOk.ownedAt {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {n : Nat} {m : Mem} {k j : Nat}
    {a p : BitVec 64} {S : Shape} (he : EaIs Γ m p) (hat : OwnedByte Γ.owned k a S p j)
    (hn : 0 < n) (hin : j + n ≤ S.size) : ReadOk Ψ next Γ n (.mem m) :=
  .owned he ⟨hat.entry, hat.addr⟩ (by rw [hat.toNat (by omega)]; exact hin)

/-- Overwriting plain bytes of an owned block, the first given by its number. -/
theorem WriteIntOk.ownedAt {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {n : Nat} {m : Mem}
    {k j : Nat} {a p : BitVec 64} {S : Shape} (he : EaIs Γ m p)
    (hat : OwnedByte Γ.owned k a S p j) (hn : 0 < n) (hin : j + n ≤ S.size)
    (hfree : S.free j n = true) : WriteIntOk Ψ next Γ n (.mem m) Γ := by
  have e := hat.toNat (j := j) (by omega)
  exact .owned he ⟨hat.entry, hat.addr⟩ (by rw [e]; exact hin) (by rw [e]; exact hfree)

end TypedAsm
