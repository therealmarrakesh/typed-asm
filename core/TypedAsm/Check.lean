import TypedAsm.Program
import TypedAsm.Blocks

/-!
# Checking by computation

The typing rules say when an instruction may run in a context and what
context it leaves. Here that is a function: given the context and the
instruction it works out the context afterwards, and says what, if
anything, is left to be shown. `straight_sound` says its answers are typing
steps. So typing a run of instructions is evaluating a function, with no
search among rules.

The function is defined on contexts as they are, not on a separate syntax
for them. Where it needs to know what a register holds it looks, and where
the context does not say, as for a register a function was handed by
whoever called it, it has no answer and the rules are used directly.

It covers the forms that work on registers alone, and those that work on
the stack: `push` and `pop`, making and giving back room, and loading and
storing at a place on it; and loads and stores through a pointer into a
block, of a typed value or of plain bytes. For an instruction with
several rules it takes the one that keeps most, in the order the rules are
tried by hand: an exactly known result where the operands are exactly
known, and otherwise a number.
-/

namespace TypedAsm

namespace Check

/-- What one instruction comes to: the context afterwards, and what is left
to be shown for the step to be a typing step. -/
structure Step where
  ctx : Ctx
  needs : Prop := True

/-- The value a type says a register holds exactly, if it says so. -/
def exactly : Ty → Option (BitVec 64)
  | .eq a => some a
  | _ => none

theorem exactly_eq {τ : Ty} {a : BitVec 64} (h : exactly τ = some a) : τ = .eq a := by
  cases τ <;> simp only [exactly, Option.some.injEq, reduceCtorEq] at h
  rw [h]

/-- What reading the carry flag asks: that it is defined. -/
def carryNeeds (Γ : Ctx) (op : AluOp) : Prop :=
  op.readsCarry = true → ∀ f, Γ.flags f → f.cf.isSome = true

/-- An operation that does not read the carry flag asks nothing of it. -/
theorem carryNeeds_of_false (Γ : Ctx) (op : AluOp) (h : op.readsCarry = false) :
    carryNeeds Γ op := fun h' => absurd h' (by rw [h]; decide)

/-- The displacement of a memory operand, where it reaches forward. -/
def dispOf (disp : BitVec 32) : Option Nat :=
  if disp.toNat < 2 ^ 31 then some disp.toNat else none

theorem dispOf_spec {disp : BitVec 32} {d : Nat} (h : dispOf disp = some d) : byteDisp d disp := by
  unfold dispOf at h
  split at h
  · next hlt => cases h; exact ⟨by simp, hlt⟩
  · cases h

/-- A 32-bit copy between registers. -/
def mov32 (Γ : Ctx) (d s : Reg) : Option Step :=
  if d = .rsp then none
  else match exactly (Γ.regs s) with
    | some a =>
      if s = .rsp then some ⟨Γ.setReg d .int, True⟩
      else some ⟨Γ.setReg d (.eq ((a.setWidth 32).setWidth 64)), True⟩
    | none => some ⟨Γ.setReg d .int, True⟩

/-- Arithmetic between two registers. -/
def aluRR (Γ : Ctx) (op : AluOp) (w : Width) (d s : Reg) : Option Step :=
  if d = .rsp then none
  else match exactly (Γ.regs d), exactly (Γ.regs s) with
    | some a, some b =>
      if s = .rsp ∨ op.readsCarry = true then some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩
      else match w with
        | .w64 =>
          some ⟨{ (bif op.writesDst then Γ.setReg d (.eq (op.apply a b).1) else Γ) with
            flags := (· = (op.apply a b).2) }, True⟩
        | .w32 =>
          some ⟨{ (bif op.writesDst then
              Γ.setReg d (.eq ((op.apply (a.setWidth 32) (b.setWidth 32)).1.setWidth 64))
            else Γ) with
            flags := (· = (op.apply (a.setWidth 32) (b.setWidth 32)).2) }, True⟩
    | _, _ => some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩

/-- Arithmetic between a register and a constant. A register that holds a
pointer is left to the rules: what becomes of it depends on the block. -/
def aluRI (Γ : Ctx) (op : AluOp) (w : Width) (d : Reg) (imm : BitVec 32) : Option Step :=
  if d = .rsp then none
  else match Γ.regs d with
    | .eq a =>
      if op.readsCarry = true then some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩
      else match w with
        | .w64 =>
          some ⟨{ (bif op.writesDst then Γ.setReg d (.eq (op.apply a (imm.signExtend 64)).1)
            else Γ) with flags := (· = (op.apply a (imm.signExtend 64)).2) }, True⟩
        | .w32 =>
          some ⟨{ (bif op.writesDst then
              Γ.setReg d (.eq ((op.apply (a.setWidth 32) (imm.signExtend 32)).1.setWidth 64))
            else Γ) with
            flags := (· = (op.apply (a.setWidth 32) (imm.signExtend 32)).2) }, True⟩
    | .int => some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩
    | .ptr S wr off =>
      -- a pointer moved on stays a pointer into its block, that much further in
      match op, w, dispOf imm with
      | .add, .w64, some k =>
        some ⟨{ Γ.setReg d (.ptr S wr (off + k)) with flags := Flags.Known }, True⟩
      | _, _, _ => none
    | .str true =>
      -- on from a byte of a text that is not its last
      match op, w with
      | .add, .w64 =>
        if imm = 1 then some ⟨{ Γ.setReg d (.str false) with flags := Flags.Known }, True⟩
        else none
      | _, _ => none
    | _ => none

/-- A `test` of one register against another. -/
def testRR (Γ : Ctx) (r r' : Reg) : Option Step :=
  match exactly (Γ.regs r), exactly (Γ.regs r') with
  | some a, some b =>
    if r = .rsp ∨ r' = .rsp then some ⟨{ Γ with flags := Flags.Known }, True⟩
    else some ⟨{ Γ with flags := (· = Flags.ofResult (a &&& b) false false) }, True⟩
  | _, _ => some ⟨{ Γ with flags := Flags.Known }, True⟩

/-- A `push`: eight bytes of the free room become a slot holding what the
register holds. Left to be shown: that there are eight bytes of room. -/
def push (Γ : Ctx) (r : Reg) : Option Step :=
  if r = .rsp then none
  else some ⟨{ Γ.moveSp (-8) with stack := .slot (Γ.regs r) :: Γ.stack, room := Γ.room - 8 },
    8 ≤ Γ.room⟩

/-- A `pop`: the top piece of the stack, if it is eight bytes, goes into the
register, with its type if it is one typed value. -/
def pop (Γ : Ctx) (r : Reg) : Option Step :=
  if r = .rsp then none
  else match Γ.stack with
    | ⟨8, [(0, τ)]⟩ :: σ =>
      some ⟨CtxOf.setReg { Γ.moveSp 8 with stack := σ, room := Γ.room + 8 } r τ, True⟩
    | S :: σ =>
      if S.size = 8 then
        some ⟨CtxOf.setReg { Γ.moveSp 8 with stack := σ, room := Γ.room + 8 } r .int, True⟩
      else none
    | [] => none

/-- Which piece of the stack byte `d` above the stack pointer is in, counting
pieces from `k`, and how far into it. -/
def pieceAt : List Shape → Nat → Nat → Option (Nat × Shape × Nat)
  | [], _, _ => none
  | S :: σ, k, d => if d < S.size then some (k, S, d) else pieceAt σ (k + 1) (d - S.size)

theorem pieceAt_spec : ∀ (σ : List Shape) (k₀ d : Nat) {k : Nat} {S : Shape} {i : Nat},
    pieceAt σ k₀ d = some (k, S, i) →
    ∃ j, k = k₀ + j ∧ σ[j]? = some S ∧ d = stackOff σ j + i ∧ i < S.size
  | [], _, _, _, _, _, h => by cases h
  | T :: σ, k₀, d, k, S, i, h => by
    unfold pieceAt at h
    split at h
    · next hlt =>
      cases h
      exact ⟨0, rfl, rfl, by simp, hlt⟩
    · next hge =>
      obtain ⟨j, hk, hj, hd, hi⟩ := pieceAt_spec σ (k₀ + 1) (d - T.size) h
      refine ⟨j + 1, by omega, hj, ?_, hi⟩
      show d = T.size + stackOff σ j + i
      omega

/-- Loading the typed value at a place on the stack. -/
def loadStack (Γ : Ctx) (r : Reg) (disp : BitVec 32) : Option Step :=
  if r = .rsp then none
  else match dispOf disp with
    | none => none
    | some d =>
      match pieceAt Γ.stack 0 d with
      | none => none
      | some (_, S, i) =>
        match S.valAt i with
        | some τ => some ⟨Γ.setReg r τ, True⟩
        | none => if i + 8 ≤ S.size then some ⟨Γ.setReg r .int, True⟩ else none

/-- Storing a register's eight bytes at a place on the stack: they take its type. -/
def storeStack (Γ : Ctx) (s : Reg) (disp : BitVec 32) : Option Step :=
  if s = .rsp then none
  else match dispOf disp with
    | none => none
    | some d =>
      match pieceAt Γ.stack 0 d with
      | none => none
      | some (k, S, i) =>
        if i + 8 ≤ S.size then
          some ⟨{ Γ with stack := Γ.stack.set k (S.set i (Γ.regs s)) }, True⟩
        else none

/-- Making room on the stack: so many bytes of the free room become one
piece of plain bytes. Left to be shown: that there is that much room. -/
def allocFrame (Γ : Ctx) (imm : BitVec 32) : Option Step :=
  match dispOf imm with
  | none => none
  | some k =>
    some ⟨{ Γ.moveSp (-BitVec.ofNat 64 k) with
      stack := .raw k :: Γ.stack, room := Γ.room - k, flags := Flags.Known }, k ≤ Γ.room⟩

/-- Giving back the pieces at the top of the stack that come to so many bytes. -/
def freeFrame (Γ : Ctx) (imm : BitVec 32) : Option Step :=
  match dispOf imm with
  | none => none
  | some k =>
    match stackDrop Γ.stack k with
    | none => none
    | some rest =>
      some ⟨{ Γ.moveSp (BitVec.ofNat 64 k) with
        stack := rest, room := Γ.room + k, flags := Flags.Known }, True⟩

/-- Whether `n` bytes may be read from an operand: a register, a place on
the stack inside one piece, or a place in the block a pointer points into. -/
def readOk (Γ : Ctx) (n : Nat) : RM → Bool
  | .reg _ => true
  | .mem (.sib (some b) none disp) =>
    match dispOf disp with
    | none => false
    | some d =>
      if b = .rsp then
        match pieceAt Γ.stack 0 d with
        | some (_, S, i) => decide (i + n ≤ S.size)
        | none => false
      else
        match Γ.regs b with
        | .ptr S _ off => decide (off + d + n ≤ S.size)
        | _ => false
  | _ => false

/-- The context after `n` plain bytes are stored to an operand, if they may
be: a register becomes a number, a piece of the stack forgets what typed
value reached into those bytes, and a block must have plain bytes there. -/
def writeInt (Γ : Ctx) (n : Nat) : RM → Option Ctx
  | .reg d => if d = .rsp then none else some (Γ.setReg d .int)
  | .mem (.sib (some b) none disp) =>
    match dispOf disp with
    | none => none
    | some d =>
      if b = .rsp then
        match pieceAt Γ.stack 0 d with
        | some (k, S, i) =>
          if i + n ≤ S.size then some { Γ with stack := Γ.stack.set k (S.clear i n) } else none
        | none => none
      else
        match Γ.regs b with
        | .ptr S true off =>
          if off + d + n ≤ S.size ∧ S.free (off + d) n = true then some Γ else none
        | _ => none
  | _ => none

/-- Loading eight bytes through a pointer: the typed value there, or a
number where the bytes are plain. -/
def loadField (Γ : Ctx) (d b : Reg) (disp : BitVec 32) : Option Step :=
  if d = .rsp ∨ b = .rsp then none
  else match Γ.regs b with
    | .ptr S _ off =>
      match dispOf disp with
      | none => none
      | some k =>
        match S.valAt (off + k) with
        | some τ => some ⟨Γ.setReg d τ, True⟩
        | none => if off + k + 8 ≤ S.size then some ⟨Γ.setReg d .int, True⟩ else none
    | _ => none

/-- Storing eight bytes through a writable pointer: over a typed value, a
value of its type, which is left to be shown; over plain bytes, anything. -/
def storeField (Γ : Ctx) (b s : Reg) (disp : BitVec 32) : Option Step :=
  if b = .rsp ∨ s = .rsp then none
  else match Γ.regs b with
    | .ptr S true off =>
      match dispOf disp with
      | none => none
      | some k =>
        match S.valAt (off + k) with
        | some τ => if S.sole (off + k) = true then some ⟨Γ, Sub (Γ.regs s) τ⟩ else none
        | none =>
          if off + k + 8 ≤ S.size ∧ S.free (off + k) 8 = true then some ⟨Γ, True⟩ else none
    | _ => none

/-- A load of a number from memory. -/
def loadInt (Γ : Ctx) (w : Width) (d : Reg) (m : Mem) : Option Step :=
  if d = .rsp then none
  else if readOk Γ w.bytes.toNat (.mem m) then some ⟨Γ.setReg d .int, True⟩ else none

/-- A store of plain bytes. -/
def storeInt (Γ : Ctx) (n : Nat) (dst : RM) : Option Step :=
  (writeInt Γ n dst).map fun Γ' => ⟨Γ', True⟩

/-- **The checker for one instruction that goes on to the next.** `next` is
the address of the instruction after it. -/
def straight (next : BitVec 64) (Γ : Ctx) : Instr → Option Step
  | .nop => some ⟨Γ, True⟩
  | .mov .w64 (.rm_r (.reg d) s) =>
    if d = .rsp ∨ s = .rsp then none else some ⟨Γ.setReg d (Γ.regs s), True⟩
  | .mov .w32 (.rm_r (.reg d) s) => mov32 Γ d s
  | .mov w (.rm_i (.reg d) imm) =>
    if d = .rsp then none
    else some ⟨Γ.setReg d (.eq ((imm.signExtend w.bits).setWidth 64)), True⟩
  | .movAbs d imm => if d = .rsp then none else some ⟨Γ.setReg d (.eq imm), True⟩
  | .lea .w64 d (.rip disp) =>
    if d = .rsp then none else some ⟨Γ.setReg d (.eq (next + disp.signExtend 64)), True⟩
  | .alu .xor w (.rm_r (.reg d) s) =>
    if d = s then
      if d = .rsp then none
      else some ⟨{ Γ.setReg d (.eq 0) with
        flags := (· = Flags.ofResult (0 : BitVec w.bits) false false) }, True⟩
    else aluRR Γ .xor w d s
  | .alu op w (.rm_r (.reg d) s) => aluRR Γ op w d s
  | .alu .sub .w64 (.rm_i (.reg .rsp) imm) => allocFrame Γ imm
  | .alu .add .w64 (.rm_i (.reg .rsp) imm) => freeFrame Γ imm
  | .alu op w (.rm_i (.reg d) imm) => aluRI Γ op w d imm
  | .mov .w64 (.r_m r (.sib (some .rsp) none disp)) => loadStack Γ r disp
  | .mov .w64 (.rm_r (.mem (.sib (some .rsp) none disp)) s) => storeStack Γ s disp
  | .mov .w64 (.r_m d (.sib (some b) none disp)) => loadField Γ d b disp
  | .mov .w64 (.rm_r (.mem (.sib (some b) none disp)) s) => storeField Γ b s disp
  | .mov .w32 (.r_m d m) => loadInt Γ .w32 d m
  | .mov .w32 (.rm_r (.mem m) _) => storeInt Γ 4 (.mem m)
  | .mov w (.rm_i (.mem m) _) => storeInt Γ w.bytes.toNat (.mem m)
  | .store8 m _ => storeInt Γ 1 (.mem m)
  | .store16 m _ => storeInt Γ 2 (.mem m)
  | .push r => push Γ r
  | .pop r => pop Γ r
  | .test .w64 (.reg r) (.reg r') => testRR Γ r r'
  | .test _ (.reg _) _ => some ⟨{ Γ with flags := Flags.Known }, True⟩
  | _ => none

variable {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx}

theorem mov32_sound {d s : Reg} {st : Step} (h : mov32 Γ d s = some st) :
    Straight Ψ next Γ (.mov .w32 (.rm_r (.reg d) s)) st.ctx := by
  unfold mov32 at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next a ha =>
      split at h
      · cases h; exact .movRR32 hd
      · next hs => cases h; exact .mov32Exact hd hs (exactly_eq ha)
    · cases h; exact .movRR32 hd

theorem aluRR_sound {op : AluOp} {w : Width} {d s : Reg} {st : Step}
    (h : aluRR Γ op w d s = some st) (hn : st.needs) :
    Straight Ψ next Γ (.alu op w (.rm_r (.reg d) s)) st.ctx := by
  unfold aluRR at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next a b ha hb =>
      split at h
      · cases h; exact .aluRR hd hn
      · next hc =>
        have hs : s ≠ .rsp := fun e => hc (.inl e)
        have hcarry : op.readsCarry = false := by
          cases hr : op.readsCarry with
          | false => rfl
          | true => exact absurd (.inr hr) hc
        split at h
        · cases h; exact .aluExactRR hd hs (exactly_eq ha) (exactly_eq hb) hcarry
        · cases h; exact .aluExactRR32 hd hs (exactly_eq ha) (exactly_eq hb) hcarry
    · cases h; exact .aluRR hd hn

theorem aluRI_sound {op : AluOp} {w : Width} {d : Reg} {imm : BitVec 32} {st : Step}
    (h : aluRI Γ op w d imm = some st) (hn : st.needs) :
    Straight Ψ next Γ (.alu op w (.rm_i (.reg d) imm)) st.ctx := by
  unfold aluRI at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next a ha =>
      split at h
      · cases h; exact .aluRI hd hn
      · next hc =>
        have hcarry : op.readsCarry = false := (Bool.not_eq_true _).mp hc
        split at h
        · cases h; exact .aluExact hd ha hcarry
        · cases h; exact .aluExact32 hd ha hcarry
    · cases h; exact .aluRI hd hn
    · next S wr off hΓ =>
      split at h
      · next k hk => cases h; exact .addPtr hd hΓ (dispOf_spec hk)
      · cases h
    · next hΓ =>
      split at h
      · split at h
        · next hi => cases h; subst hi; exact .strNext hd hΓ
        · cases h
      · cases h
    · cases h

theorem testRR_sound {r r' : Reg} {st : Step} (h : testRR Γ r r' = some st) :
    Straight Ψ next Γ (.test .w64 (.reg r) (.reg r')) st.ctx := by
  unfold testRR at h
  split at h
  · next a b ha hb =>
    split at h
    · cases h; exact .testRM (.reg _)
    · next hc =>
      cases h
      exact .testExact (fun e => hc (.inl e)) (fun e => hc (.inr e)) (exactly_eq ha) (exactly_eq hb)
  · cases h; exact .testRM (.reg _)

theorem push_sound {r : Reg} {st : Step} (h : push Γ r = some st) (hn : st.needs) :
    Straight Ψ next Γ (.push r) st.ctx := by
  unfold push at h
  split at h
  · cases h
  · next hr =>
    cases h
    have hroom : Γ.room = (Γ.room - 8) + 8 := by
      have : 8 ≤ Γ.room := hn
      omega
    exact .push hr hroom

theorem pop_sound {r : Reg} {st : Step} (h : pop Γ r = some st) :
    Straight Ψ next Γ (.pop r) st.ctx := by
  unfold pop at h
  split at h
  · cases h
  · next hr =>
    split at h
    · next τ σ hst => cases h; exact .pop hr hst
    · next S σ _ hst =>
      split at h
      · next hsz => cases h; exact .popPlain hr hst hsz
      · cases h
    · cases h

theorem loadStack_sound {r : Reg} {disp : BitVec 32} {st : Step}
    (h : loadStack Γ r disp = some st) :
    Straight Ψ next Γ (.mov .w64 (.r_m r (.sib (some .rsp) none disp))) st.ctx := by
  unfold loadStack at h
  split at h
  · cases h
  · next hr =>
    split at h
    · cases h
    · next d hd =>
      split at h
      · cases h
      · next k S i hp =>
        obtain ⟨j, hk, hj, hoff, _⟩ := pieceAt_spec _ _ _ hp
        split at h
        · next τ hv => cases h; exact .loadStack hr (dispOf_spec hd) ⟨hj, hoff⟩ hv
        · split at h
          · next hsz => cases h; exact .loadInt hr (.slot (dispOf_spec hd) ⟨hj, hoff⟩ hsz)
          · cases h

theorem storeStack_sound {s : Reg} {disp : BitVec 32} {st : Step}
    (h : storeStack Γ s disp = some st) :
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none disp)) s)) st.ctx := by
  unfold storeStack at h
  split at h
  · cases h
  · next hs =>
    split at h
    · cases h
    · next d hd =>
      split at h
      · cases h
      · next k S i hp =>
        obtain ⟨j, hk, hj, hoff, _⟩ := pieceAt_spec _ _ _ hp
        have hkj : k = j := by omega
        subst hkj
        split at h
        · next hsz => cases h; exact .storeStack hs (dispOf_spec hd) ⟨hj, hoff⟩ hsz
        · cases h

theorem allocFrame_sound {imm : BitVec 32} {st : Step} (h : allocFrame Γ imm = some st)
    (hn : st.needs) : Straight Ψ next Γ (.alu .sub .w64 (.rm_i (.reg .rsp) imm)) st.ctx := by
  unfold allocFrame at h
  split at h
  · cases h
  · next k hk =>
    cases h
    have hroom : Γ.room = (Γ.room - k) + k := by
      have : k ≤ Γ.room := hn
      omega
    exact .allocFrame (dispOf_spec hk) hroom

theorem freeFrame_sound {imm : BitVec 32} {st : Step} (h : freeFrame Γ imm = some st) :
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm)) st.ctx := by
  unfold freeFrame at h
  split at h
  · cases h
  · next k hk =>
    split at h
    · cases h
    · next rest hd =>
      cases h
      obtain ⟨top, hst, hlen⟩ := stackDrop_eq hd
      exact .freeFrame (dispOf_spec hk) hst hlen

theorem readOk_sound {n : Nat} {rm : RM} (h : readOk Γ n rm = true) :
    ReadOk Ψ next Γ n rm := by
  unfold readOk at h
  split at h
  · exact .reg _
  · next b disp =>
    split at h
    · cases h
    · next d hd =>
      split at h
      · next hb =>
        subst hb
        split at h
        · next k S i hp =>
          obtain ⟨j, _, hj, hoff, _⟩ := pieceAt_spec _ _ _ hp
          exact .slot (dispOf_spec hd) ⟨hj, hoff⟩ (of_decide_eq_true h)
        · cases h
      · next hb =>
        split at h
        · next S w off hΓ => exact .field hb hΓ (dispOf_spec hd) (of_decide_eq_true h)
        · cases h
  · cases h

theorem writeInt_sound {n : Nat} {rm : RM} {Γ' : Ctx} (h : writeInt Γ n rm = some Γ') :
    WriteIntOk Ψ next Γ n rm Γ' := by
  unfold writeInt at h
  split at h
  · split at h
    · cases h
    · next hd => cases h; exact .reg hd
  · next b disp =>
    split at h
    · cases h
    · next d hd =>
      split at h
      · next hb =>
        subst hb
        split at h
        · next k S i hp =>
          obtain ⟨j, hk, hj, hoff, _⟩ := pieceAt_spec _ _ _ hp
          have hkj : k = j := by omega
          subst hkj
          split at h
          · next hsz => cases h; exact .slot (dispOf_spec hd) ⟨hj, hoff⟩ hsz
          · cases h
        · cases h
      · next hb =>
        split at h
        · next S off hΓ =>
          split at h
          · next hc => cases h; exact .field hb hΓ (dispOf_spec hd) hc.1 hc.2
          · cases h
        · cases h
  · cases h

theorem loadField_sound {d b : Reg} {disp : BitVec 32} {st : Step}
    (h : loadField Γ d b disp = some st) :
    Straight Ψ next Γ (.mov .w64 (.r_m d (.sib (some b) none disp))) st.ctx := by
  unfold loadField at h
  split at h
  · cases h
  · next hc =>
    have hd : d ≠ .rsp := fun e => hc (.inl e)
    have hb : b ≠ .rsp := fun e => hc (.inr e)
    split at h
    · next S w off hΓ =>
      split at h
      · cases h
      · next k hk =>
        split at h
        · next τ hv => cases h; exact .loadField hd hb hΓ (dispOf_spec hk) hv
        · split at h
          · next hsz =>
            cases h
            exact .loadInt hd (.field hb hΓ (dispOf_spec hk) hsz)
          · cases h
    · cases h

theorem storeField_sound {b s : Reg} {disp : BitVec 32} {st : Step}
    (h : storeField Γ b s disp = some st) (hn : st.needs) :
    Straight Ψ next Γ (.mov .w64 (.rm_r (.mem (.sib (some b) none disp)) s)) st.ctx := by
  unfold storeField at h
  split at h
  · cases h
  · next hc =>
    have hb : b ≠ .rsp := fun e => hc (.inl e)
    have hs : s ≠ .rsp := fun e => hc (.inr e)
    split at h
    · next S off hΓ =>
      split at h
      · cases h
      · next k hk =>
        split at h
        · next τ hv =>
          split at h
          · next hso => cases h; exact .storeField hb hs hΓ (dispOf_spec hk) hv hso hn
          · cases h
        · split at h
          · next hc' =>
            cases h
            exact .storeInt (.field hb hΓ (dispOf_spec hk) hc'.1 hc'.2)
          · cases h
    · cases h

theorem loadInt_sound {w : Width} {d : Reg} {m : Mem} {st : Step}
    (h : loadInt Γ w d m = some st) : Straight Ψ next Γ (.mov w (.r_m d m)) st.ctx := by
  unfold loadInt at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next hr => cases h; exact .loadInt hd (readOk_sound hr)
    · cases h

theorem storeInt_spec {n : Nat} {dst : RM} {st : Step} (h : storeInt Γ n dst = some st) :
    WriteIntOk Ψ next Γ n dst st.ctx := by
  unfold storeInt at h
  cases hw : writeInt Γ n dst with
  | none => rw [hw] at h; cases h
  | some Γ' => rw [hw] at h; cases h; exact writeInt_sound hw

/-- **What the checker works out is a typing step.** -/
theorem straight_sound {i : Instr} {st : Step} (h : straight next Γ i = some st)
    (hn : st.needs) : Straight Ψ next Γ i st.ctx := by
  unfold straight at h
  split at h
  · cases h; exact .nop
  · split at h
    · cases h
    · next hc => cases h; exact .movRR64 (fun e => hc (.inl e)) (fun e => hc (.inr e))
  · exact mov32_sound h
  · split at h
    · cases h
    · next hd => cases h; exact .movRI hd
  · split at h
    · cases h
    · next hd => cases h; exact .movAbs hd
  · split at h
    · cases h
    · next hd => cases h; exact .leaRip hd
  · split at h
    · next hds =>
      subst hds
      split at h
      · cases h
      · next hd => cases h; exact .xorSelf hd
    · exact aluRR_sound h hn
  · exact aluRR_sound h hn
  · exact allocFrame_sound h hn
  · exact freeFrame_sound h
  · exact aluRI_sound h hn
  · exact loadStack_sound h
  · exact storeStack_sound h
  · exact loadField_sound h
  · exact storeField_sound h hn
  · exact loadInt_sound h
  · exact .storeInt (storeInt_spec h)
  · exact .storeImm (storeInt_spec h)
  · exact .store8RM (storeInt_spec h)
  · exact .store16RM (storeInt_spec h)
  · exact push_sound h hn
  · exact pop_sound h
  · exact testRR_sound h
  · cases h; exact .testRM (.reg _)
  · cases h

/-! ## The rest of the instructions

The forms above need nothing but the context. Those below also reach data by
its label, so they are told what blocks the program has. For an instruction
with a rule for exactly known operands and another for any, the first is
taken where the operands are exactly known, as above. -/

/-- The block an address is in, the block's layout, and how far in. -/
def blockAt (bs : List (BitVec 64 × Layout)) (a : BitVec 64) :
    Option (BitVec 64 × Layout × Nat) :=
  match bs.findSome? (fun x => if (a - x.1).toNat < x.2.shape.size then some x.1 else none) with
  | none => none
  | some base =>
    match bs.find? (·.1 = base) with
    | none => none
    | some y => some (base, y.2, (a - base).toNat)

theorem blockAt_spec {bs : List (BitVec 64 × Layout)} {kinds : List (Nat × Shape)}
    {a base : BitVec 64} {l : Layout} {d : Nat} (h : blockAt bs a = some (base, l, d)) :
    MemTy.ofList bs kinds base = some l ∧ a = base + BitVec.ofNat 64 d := by
  unfold blockAt at h
  split at h
  · cases h
  · next b _ =>
    split at h
    · cases h
    · next y hy =>
      cases h
      refine ⟨?_, ?_⟩
      · show (bs.find? _).map (·.2) = some y.2
        rw [hy]; rfl
      · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        bv_omega

/-- Whether `n` bytes may be read from an operand, data reached by its label
included. -/
def readOkG (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (n : Nat) (rm : RM) :
    Bool :=
  match rm with
  | .mem (.rip disp) =>
    match blockAt bs (next + disp.signExtend 64) with
    | some (_, l, d) => decide (d + n ≤ l.shape.size)
    | none => false
  | rm => readOk Γ n rm

/-- The context after `n` plain bytes are stored to an operand, data reached
by its label included: the block must be writable and have plain bytes
there. -/
def writeIntG (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (n : Nat) (rm : RM) :
    Option Ctx :=
  match rm with
  | .mem (.rip disp) =>
    match blockAt bs (next + disp.signExtend 64) with
    | some (_, l, d) =>
      if l.writable = true ∧ d + n ≤ l.shape.size ∧ l.shape.free d n = true then some Γ else none
    | none => none
  | rm => writeInt Γ n rm

variable {bs : List (BitVec 64 × Layout)} {kinds : List (Nat × Shape)}

theorem readOkG_sound {n : Nat} {rm : RM} (h : readOkG bs next Γ n rm = true) :
    ReadOk (MemTy.ofList bs kinds) next Γ n rm := by
  unfold readOkG at h
  split at h
  · next disp =>
    split at h
    · next base l d hb =>
      obtain ⟨hl, ha⟩ := blockAt_spec (kinds := kinds) hb
      exact .global hl ha (of_decide_eq_true h)
    · cases h
  · exact readOk_sound h

theorem writeIntG_sound {n : Nat} {rm : RM} {Γ' : Ctx} (h : writeIntG bs next Γ n rm = some Γ') :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n rm Γ' := by
  unfold writeIntG at h
  split at h
  · next disp =>
    split at h
    · next base l d hb =>
      obtain ⟨hl, ha⟩ := blockAt_spec (kinds := kinds) hb
      split at h
      · next hc => cases h; exact .global hl hc.1 ha hc.2.1 hc.2.2
      · cases h
    · cases h
  · exact writeInt_sound h

/-- A register operand that is not the stack pointer and holds an exactly
known value: the register and the value. -/
def exactReg (Γ : Ctx) : RM → Option (Reg × BitVec 64)
  | .reg d => if d = .rsp then none else (exactly (Γ.regs d)).map fun a => (d, a)
  | _ => none

theorem exactReg_spec {rm : RM} {d : Reg} {a : BitVec 64} (h : exactReg Γ rm = some (d, a)) :
    rm = .reg d ∧ d ≠ .rsp ∧ Γ.regs d = .eq a := by
  unfold exactReg at h
  split at h
  · next r =>
    split at h
    · cases h
    · next hr =>
      cases he : exactly (Γ.regs r) with
      | none => rw [he] at h; cases h
      | some b =>
        rw [he] at h
        cases h
        exact ⟨rfl, hr, exactly_eq he⟩
  · cases h

/-- That the flags decide a condition. -/
def decides (Γ : Ctx) (c : Cond) : Prop :=
  ∀ f, Γ.flags f → ∃ b, c.eval f = some b

/-- An operand read and written in place, where it is not an exactly known
register: what is written is a number. `flags` is what the instruction
leaves of the flags. -/
def inPlace (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (n : Nat) (dst : RM)
    (flags : Option (Flags → Prop)) : Option Step :=
  if readOkG bs next Γ n dst then
    (writeIntG bs next Γ n dst).map fun Γ' =>
      match flags with
      | some P => ⟨{ Γ' with flags := P }, True⟩
      | none => ⟨Γ', True⟩
  else none

theorem inPlace_spec {n : Nat} {dst : RM} {flags : Option (Flags → Prop)} {st : Step}
    (h : inPlace bs next Γ n dst flags = some st) :
    ∃ Γ', ReadOk (MemTy.ofList bs kinds) next Γ n dst ∧
      WriteIntOk (MemTy.ofList bs kinds) next Γ n dst Γ' ∧
      st.ctx = (match flags with
        | some P => { Γ' with flags := P }
        | none => Γ') := by
  unfold inPlace at h
  split at h
  · next hr =>
    cases hw : writeIntG bs next Γ n dst with
    | none => rw [hw] at h; cases h
    | some Γ' =>
      rw [hw] at h
      refine ⟨Γ', readOkG_sound hr, writeIntG_sound hw, ?_⟩
      cases flags <;> (cases h; rfl)
  · cases h

/-- `neg` and `not`. -/
def unary (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (op : UnOp) (w : Width)
    (dst : RM) : Option Step :=
  match exactReg Γ dst with
  | some (d, a) =>
    match op with
    | .neg =>
      some ⟨{ Γ.setReg d (.eq ((subBorrow 0 (a.setWidth w.bits) false).1.setWidth 64)) with
        flags := (· = (subBorrow 0 (a.setWidth w.bits) false).2) }, True⟩
    | .not => some ⟨Γ.setReg d (.eq ((~~~(a.setWidth w.bits)).setWidth 64)), True⟩
  | none =>
    match op with
    | .neg => inPlace bs next Γ w.bytes.toNat dst (some Flags.Known)
    | .not => inPlace bs next Γ w.bytes.toNat dst none

theorem unary_sound {op : UnOp} {w : Width} {dst : RM} {st : Step}
    (h : unary bs next Γ op w dst = some st) :
    Straight (MemTy.ofList bs kinds) next Γ (.unary op w dst) st.ctx := by
  unfold unary at h
  split at h
  · next d a he =>
    obtain ⟨rfl, hd, hΓ⟩ := exactReg_spec he
    split at h
    · cases h; exact .negExact hd hΓ
    · cases h; exact .notExact hd hΓ
  · split at h
    · obtain ⟨Γ', hr, hw, e⟩ := inPlace_spec (kinds := kinds) h
      rw [e]; exact .negRM hr hw
    · obtain ⟨Γ', hr, hw, e⟩ := inPlace_spec (kinds := kinds) h
      rw [e]; exact .notRM hr hw

/-- Shifts and rotates. -/
def shift (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (op : ShiftOp)
    (w : Width) (dst : RM) : Count → Option Step
  | .imm n =>
    match exactReg Γ dst with
    | some (d, a) =>
      some ⟨{ Γ.setReg d (.eq ((op.apply (a.setWidth w.bits) (n.toNat % w.bits)).setWidth 64)) with
        flags := op.flagsAfter (n.toNat % w.bits) Γ.flags }, True⟩
    | none =>
      inPlace bs next Γ w.bytes.toNat dst (some (op.flagsAfter (n.toNat % w.bits) Γ.flags))
  | .cl => inPlace bs next Γ w.bytes.toNat dst (some Flags.Any)

theorem shift_sound {op : ShiftOp} {w : Width} {dst : RM} {c : Count} {st : Step}
    (h : shift bs next Γ op w dst c = some st) :
    Straight (MemTy.ofList bs kinds) next Γ (.shift op w dst c) st.ctx := by
  unfold shift at h
  split at h
  · split at h
    · next d a he =>
      obtain ⟨rfl, hd, hΓ⟩ := exactReg_spec he
      cases h; exact .shiftExact hd hΓ
    · obtain ⟨Γ', hr, hw, e⟩ := inPlace_spec (kinds := kinds) h
      rw [e]; exact .shiftImm hr hw
  · obtain ⟨Γ', hr, hw, e⟩ := inPlace_spec (kinds := kinds) h
    rw [e]; exact .shiftCl hr hw

/-- The widening multiplies and the divides. A divide has an answer only
where the values are exactly known and it is seen not to fault. -/
def mulDiv (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (op : MulDivOp)
    (w : Width) (src : RM) : Option Step :=
  match exactReg Γ src, exactly (Γ.regs .rax), exactly (Γ.regs .rdx) with
  | some (_, b), some a, some d =>
    match op.eval (d.setWidth w.bits) (a.setWidth w.bits) (b.setWidth w.bits) with
    | .next (lo, hi, fl) =>
      some ⟨{ (Γ.setReg .rax (.eq (lo.setWidth 64))).setReg .rdx (.eq (hi.setWidth 64)) with
        flags := (· = fl) }, True⟩
    | _ => none
  | _, _, _ =>
    match op with
    | .mul | .imul =>
      if readOkG bs next Γ w.bytes.toNat src then some ⟨Γ.afterMulDiv Flags.AfterMul, True⟩
      else none
    | _ => none

theorem mulDiv_sound {op : MulDivOp} {w : Width} {src : RM} {st : Step}
    (h : mulDiv bs next Γ op w src = some st) :
    Straight (MemTy.ofList bs kinds) next Γ (.mulDiv op w src) st.ctx := by
  unfold mulDiv at h
  split at h
  · next r b a d he ha hd =>
    obtain ⟨rfl, hr, hΓ⟩ := exactReg_spec he
    split at h
    · next lo hi fl hev =>
      cases h
      exact .mulDivExact hr (exactly_eq ha) (exactly_eq hd) hΓ hev
    · cases h
  · split at h
    · split at h
      · next hr => cases h; exact .mulRM (readOkG_sound hr)
      · cases h
    · split at h
      · next hr => cases h; exact .imulRM (readOkG_sound hr)
      · cases h
    · cases h

/-- The two- and three-operand multiplies. -/
def imul2 (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (w : Width) (d : Reg)
    (src : RM) : Option Step :=
  if d = .rsp then none
  else match exactReg Γ src, exactly (Γ.regs d) with
    | some (_, b), some a =>
      some ⟨{ Γ.setReg d (.eq ((imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).1.setWidth 64))
        with flags := (· = (imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).2) }, True⟩
    | _, _ =>
      if readOkG bs next Γ w.bytes.toNat src then
        some ⟨{ Γ.setReg d .int with flags := Flags.AfterMul }, True⟩
      else none

theorem imul2_sound {w : Width} {d : Reg} {src : RM} {st : Step}
    (h : imul2 bs next Γ w d src = some st) :
    Straight (MemTy.ofList bs kinds) next Γ (.imul2 w d src) st.ctx := by
  unfold imul2 at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next r b a he ha =>
      obtain ⟨rfl, hr, hΓ⟩ := exactReg_spec he
      cases h; exact .imul2Exact hd hr (exactly_eq ha) hΓ
    · split at h
      · next hr => cases h; exact .imul2RM hd (readOkG_sound hr)
      · cases h

def imul3 (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (w : Width) (d : Reg)
    (src : RM) (imm : BitVec 32) : Option Step :=
  if d = .rsp then none
  else match exactReg Γ src with
    | some (_, b) =>
      some ⟨{ Γ.setReg d
          (.eq ((imulTrunc (b.setWidth w.bits) (imm.signExtend w.bits)).1.setWidth 64)) with
        flags := (· = (imulTrunc (b.setWidth w.bits) (imm.signExtend w.bits)).2) }, True⟩
    | none =>
      if readOkG bs next Γ w.bytes.toNat src then
        some ⟨{ Γ.setReg d .int with flags := Flags.AfterMul }, True⟩
      else none

theorem imul3_sound {w : Width} {d : Reg} {src : RM} {imm : BitVec 32} {st : Step}
    (h : imul3 bs next Γ w d src imm = some st) :
    Straight (MemTy.ofList bs kinds) next Γ (.imul3 w d src imm) st.ctx := by
  unfold imul3 at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next r b he =>
      obtain ⟨rfl, hr, hΓ⟩ := exactReg_spec he
      cases h; exact .imul3Exact hd hr hΓ
    · split at h
      · next hr => cases h; exact .imul3RM hd (readOkG_sound hr)
      · cases h

/-- Counting the bits set. -/
def popcnt (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (w : Width) (d : Reg)
    (src : RM) : Option Step :=
  if d = .rsp then none
  else match exactReg Γ src with
    | some (_, a) =>
      some ⟨{ Γ.setReg d (.eq ((popcount (a.setWidth w.bits)).setWidth 64)) with
        flags := (· = ⟨some false, some (a.setWidth w.bits == 0), some false, some false⟩) },
        True⟩
    | none =>
      if readOkG bs next Γ w.bytes.toNat src then
        some ⟨{ Γ.setReg d .int with flags := Flags.Known }, True⟩
      else none

theorem popcnt_sound {w : Width} {d : Reg} {src : RM} {st : Step}
    (h : popcnt bs next Γ w d src = some st) :
    Straight (MemTy.ofList bs kinds) next Γ (.popcnt w d src) st.ctx := by
  unfold popcnt at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next r a he =>
      obtain ⟨rfl, hr, hΓ⟩ := exactReg_spec he
      cases h; exact .popcntExact hd hr hΓ
    · split at h
      · next hr => cases h; exact .popcntRM hd (readOkG_sound hr)
      · cases h

/-- Reversing the bytes of a register. -/
def bswapR (Γ : Ctx) (w : Width) (r : Reg) : Option Step :=
  if r = .rsp then none
  else match exactly (Γ.regs r) with
    | some a =>
      some ⟨Γ.setReg r (.eq ((TypedAsm.bswap w (a.setWidth w.bits)).setWidth 64)), True⟩
    | none => some ⟨Γ.setReg r .int, True⟩

theorem bswapR_sound {w : Width} {r : Reg} {st : Step} (h : bswapR Γ w r = some st) :
    Straight Ψ next Γ (.bswap w r) st.ctx := by
  unfold bswapR at h
  split at h
  · cases h
  · next hr =>
    split at h
    · next a ha => cases h; exact .bswapExact hr (exactly_eq ha)
    · cases h; exact .bswap hr

/-- Extending a narrower value into a register. `n` is how many bytes are
read; `exact` is the result where the source is an exactly known register. -/
def extend (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (d : Reg) (n : Nat)
    (src : RM) (exact : BitVec 64 → BitVec 64) : Option Step :=
  if d = .rsp then none
  else match exactReg Γ src with
    | some (_, a) => some ⟨Γ.setReg d (.eq (exact a)), True⟩
    | none => if readOkG bs next Γ n src then some ⟨Γ.setReg d .int, True⟩ else none

theorem extend_spec {d : Reg} {n : Nat} {src : RM} {exact : BitVec 64 → BitVec 64} {st : Step}
    (h : extend bs next Γ d n src exact = some st) :
    d ≠ .rsp ∧
      ((∃ r a, src = .reg r ∧ r ≠ .rsp ∧ Γ.regs r = .eq a ∧ st.ctx = Γ.setReg d (.eq (exact a))) ∨
        (ReadOk (MemTy.ofList bs kinds) next Γ n src ∧ st.ctx = Γ.setReg d .int)) := by
  unfold extend at h
  split at h
  · cases h
  · next hd =>
    refine ⟨hd, ?_⟩
    split at h
    · next r a he =>
      obtain ⟨hs, hr, hΓ⟩ := exactReg_spec he
      cases h; exact .inl ⟨r, a, hs, hr, hΓ, rfl⟩
    · split at h
      · next hr => cases h; exact .inr ⟨readOkG_sound hr, rfl⟩
      · cases h

/-- A conditional move. Where both registers are exactly known the flags may
say which way it goes, and that is left to the rules. -/
def cmov (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (c : Cond) (w : Width)
    (d : Reg) (src : RM) : Option Step :=
  if d = .rsp then none
  else if (exactReg Γ src).isSome ∧ (exactly (Γ.regs d)).isSome then none
  else if readOkG bs next Γ w.bytes.toNat src then some ⟨Γ.setReg d .int, decides Γ c⟩
  else none

theorem cmov_sound {c : Cond} {w : Width} {d : Reg} {src : RM} {st : Step}
    (h : cmov bs next Γ c w d src = some st) (hn : st.needs) :
    Straight (MemTy.ofList bs kinds) next Γ (.cmov c w d src) st.ctx := by
  unfold cmov at h
  split at h
  · cases h
  · next hd =>
    split at h
    · cases h
    · split at h
      · next hr => cases h; exact .cmovRM hd (readOkG_sound hr) hn
      · cases h

/-- Setting a byte from a condition. For an exactly known register the
flags may say what is set, and that is left to the rules. -/
def setcc (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (c : Cond) (dst : RM) :
    Option Step :=
  if (exactReg Γ dst).isSome then none
  else (writeIntG bs next Γ 1 dst).map fun Γ' => ⟨Γ', decides Γ c⟩

theorem setcc_sound {c : Cond} {dst : RM} {st : Step} (h : setcc bs next Γ c dst = some st)
    (hn : st.needs) : Straight (MemTy.ofList bs kinds) next Γ (.setcc c dst) st.ctx := by
  unfold setcc at h
  split at h
  · cases h
  · cases hw : writeIntG bs next Γ 1 dst with
    | none => rw [hw] at h; cases h
    | some Γ' => rw [hw] at h; cases h; exact .setccRM (writeIntG_sound hw) hn

/-- Computing an address. It is exactly known where what it is computed from
is; otherwise it is a number. -/
def lea (Γ : Ctx) (w : Width) (d : Reg) (m : Mem) : Option Step :=
  if d = .rsp then none
  else match w, m with
    | .w64, .sib (some b) none disp =>
      match exactly (Γ.regs b) with
      | some a => some ⟨Γ.setReg d (.eq (a + disp.signExtend 64)), True⟩
      | none => some ⟨Γ.setReg d .int, True⟩
    | .w64, .sib (some b) (some (x, sc)) disp =>
      match exactly (Γ.regs b), exactly (Γ.regs x.toReg) with
      | some a, some c =>
        if b = .rsp then some ⟨Γ.setReg d .int, True⟩
        else some ⟨Γ.setReg d (.eq (a + (c <<< sc.shift) + disp.signExtend 64)), True⟩
      | _, _ => some ⟨Γ.setReg d .int, True⟩
    | _, _ => some ⟨Γ.setReg d .int, True⟩

theorem lea_sound {w : Width} {d : Reg} {m : Mem} {st : Step} (h : lea Γ w d m = some st) :
    Straight Ψ next Γ (.lea w d m) st.ctx := by
  unfold lea at h
  split at h
  · cases h
  · next hd =>
    split at h
    · next b disp =>
      split at h
      · next a ha =>
        cases h
        by_cases hb : b = .rsp
        · subst hb; exact .leaSp hd (exactly_eq ha)
        · exact .leaExactB hd hb (exactly_eq ha)
      · cases h; exact .lea hd
    · next b x sc disp =>
      split at h
      · next a c ha hc =>
        split at h
        · cases h; exact .lea hd
        · next hb => cases h; exact .leaExactBI hd hb (exactly_eq ha) (exactly_eq hc)
      · cases h; exact .lea hd
    · cases h; exact .lea hd

/-- Arithmetic with an operand in memory. -/
def aluMem (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (op : AluOp) (w : Width) :
    Operands → Option Step
  | .rm_r (.mem m) _ | .rm_i (.mem m) _ =>
    if op.writesDst then
      if readOkG bs next Γ w.bytes.toNat (.mem m) then
        (writeIntG bs next Γ w.bytes.toNat (.mem m)).map fun Γ' =>
          ⟨{ Γ' with flags := Flags.Known }, carryNeeds Γ op⟩
      else none
    else if readOkG bs next Γ w.bytes.toNat (.mem m) then
      some ⟨{ Γ with flags := Flags.Known }, True⟩
    else none
  | .r_m d m =>
    if d = .rsp then none
    else if readOkG bs next Γ w.bytes.toNat (.mem m) then
      some ⟨Γ.afterAlu op d, carryNeeds Γ op⟩
    else none
  | _ => none

theorem aluMem_sound {op : AluOp} {w : Width} {ops : Operands} {st : Step}
    (h : aluMem bs next Γ op w ops = some st) (hn : st.needs) :
    Straight (MemTy.ofList bs kinds) next Γ (.alu op w ops) st.ctx := by
  unfold aluMem at h
  split at h
  · next m s =>
    split at h
    · next hwd =>
      split at h
      · next hr =>
        cases hw : writeIntG bs next Γ w.bytes.toNat (.mem m) with
        | none => rw [hw] at h; cases h
        | some Γ' =>
          rw [hw] at h; cases h
          exact .aluStoreR hwd (readOkG_sound hr) (writeIntG_sound hw) hn
      · cases h
    · next hwd =>
      split at h
      · next hr => cases h; exact .cmpR ((Bool.not_eq_true _).mp hwd) (readOkG_sound hr)
      · cases h
  · next m imm =>
    split at h
    · next hwd =>
      split at h
      · next hr =>
        cases hw : writeIntG bs next Γ w.bytes.toNat (.mem m) with
        | none => rw [hw] at h; cases h
        | some Γ' =>
          rw [hw] at h; cases h
          exact .aluStoreI hwd (readOkG_sound hr) (writeIntG_sound hw) hn
      · cases h
    · next hwd =>
      split at h
      · next hr => cases h; exact .cmpI ((Bool.not_eq_true _).mp hwd) (readOkG_sound hr)
      · cases h
  · next d m =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next hr => cases h; exact .aluLoad hd (readOkG_sound hr) hn
      · cases h
  · cases h

/-- A 64-bit load of data reached by its label: the typed value there, or a
number where the bytes are plain. -/
def loadGlobal (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (d : Reg)
    (disp : BitVec 32) : Option Step :=
  if d = .rsp then none
  else match blockAt bs (next + disp.signExtend 64) with
    | none => none
    | some (_, l, k) =>
      match l.shape.valAt k with
      | some τ => some ⟨Γ.setReg d τ, True⟩
      | none => if k + 8 ≤ l.shape.size then some ⟨Γ.setReg d .int, True⟩ else none

theorem loadGlobal_sound {d : Reg} {disp : BitVec 32} {st : Step}
    (h : loadGlobal bs next Γ d disp = some st) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.r_m d (.rip disp))) st.ctx := by
  unfold loadGlobal at h
  split at h
  · cases h
  · next hd =>
    split at h
    · cases h
    · next base l k hb =>
      obtain ⟨hl, ha⟩ := blockAt_spec (kinds := kinds) hb
      split at h
      · next τ hv => cases h; exact .loadGlobal hd hl ha hv
      · split at h
        · next hsz => cases h; exact .loadInt hd (.global hl ha hsz)
        · cases h

/-- A 64-bit store to data reached by its label. -/
def storeGlobal (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (s : Reg)
    (disp : BitVec 32) : Option Step :=
  if s = .rsp then none
  else match blockAt bs (next + disp.signExtend 64) with
    | none => none
    | some (_, l, k) =>
      if l.writable = true then
        match l.shape.valAt k with
        | some τ => if l.shape.sole k = true then some ⟨Γ, Sub (Γ.regs s) τ⟩ else none
        | none =>
          if k + 8 ≤ l.shape.size ∧ l.shape.free k 8 = true then some ⟨Γ, True⟩ else none
      else none

theorem storeGlobal_sound {s : Reg} {disp : BitVec 32} {st : Step}
    (h : storeGlobal bs next Γ s disp = some st) (hn : st.needs) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.rm_r (.mem (.rip disp)) s)) st.ctx := by
  unfold storeGlobal at h
  split at h
  · cases h
  · next hs =>
    split at h
    · cases h
    · next base l k hb =>
      obtain ⟨hl, ha⟩ := blockAt_spec (kinds := kinds) hb
      split at h
      · next hwr =>
        split at h
        · next τ hv =>
          split at h
          · next hso => cases h; exact .storeGlobal hs hl hwr ha hv hso hn
          · cases h
        · split at h
          · next hc => cases h; exact .storeInt (.global hl hwr ha hc.1 hc.2)
          · cases h
      · cases h

/-- **The checker for the rest of the instructions that go on to the next.** -/
def more (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) : Instr → Option Step
  | .unary op w dst => unary bs next Γ op w dst
  | .shift op w dst c => shift bs next Γ op w dst c
  | .mulDiv op w src => mulDiv bs next Γ op w src
  | .imul2 w d src => imul2 bs next Γ w d src
  | .imul3 w d src imm => imul3 bs next Γ w d src imm
  | .popcnt w d src => popcnt bs next Γ w d src
  | .bswap w r => bswapR Γ w r
  | .cdq =>
    match exactly (Γ.regs .rax) with
    | some a => some ⟨Γ.setReg .rdx (.eq ((signFill (a.setWidth 32)).setWidth 64)), True⟩
    | none => some ⟨Γ.setReg .rdx .int, True⟩
  | .cqo =>
    match exactly (Γ.regs .rax) with
    | some a => some ⟨Γ.setReg .rdx (.eq (signFill a)), True⟩
    | none => some ⟨Γ.setReg .rdx .int, True⟩
  | .movsxd d src => extend bs next Γ d 4 src fun a => (a.setWidth 32).signExtend 64
  | .movzx w d sw src =>
    extend bs next Γ d sw.bytes src fun a => ((a.setWidth sw.bits).setWidth w.bits).setWidth 64
  | .movsx w d sw src =>
    extend bs next Γ d sw.bytes src fun a => ((a.setWidth sw.bits).signExtend w.bits).setWidth 64
  | .cmov c w d src => cmov bs next Γ c w d src
  | .setcc c dst => setcc bs next Γ c dst
  | .lea w d m => lea Γ w d m
  | .alu op w ops => aluMem bs next Γ op w ops
  | .test w (.mem m) _ =>
    if readOkG bs next Γ w.bytes.toNat (.mem m) then some ⟨{ Γ with flags := Flags.Known }, True⟩
    else none
  | .mov .w64 (.r_m d (.rip disp)) => loadGlobal bs next Γ d disp
  | .mov .w64 (.rm_r (.mem (.rip disp)) s) => storeGlobal bs next Γ s disp
  | .mov .w32 (.r_m d (.rip disp)) =>
    if d = .rsp then none
    else if readOkG bs next Γ 4 (.mem (.rip disp)) then some ⟨Γ.setReg d .int, True⟩ else none
  | .mov w (.rm_r (.mem (.rip disp)) _) =>
    (writeIntG bs next Γ w.bytes.toNat (.mem (.rip disp))).map fun Γ' => ⟨Γ', True⟩
  | .mov w (.rm_i (.mem (.rip disp)) _) =>
    (writeIntG bs next Γ w.bytes.toNat (.mem (.rip disp))).map fun Γ' => ⟨Γ', True⟩
  | .store8 (.rip disp) _ =>
    (writeIntG bs next Γ 1 (.mem (.rip disp))).map fun Γ' => ⟨Γ', True⟩
  | .store16 (.rip disp) _ =>
    (writeIntG bs next Γ 2 (.mem (.rip disp))).map fun Γ' => ⟨Γ', True⟩
  | _ => none

theorem writeIntG_step {n : Nat} {rm : RM} {st : Step}
    (h : (writeIntG bs next Γ n rm).map (fun Γ' => (⟨Γ', True⟩ : Step)) = some st) :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n rm st.ctx := by
  cases hw : writeIntG bs next Γ n rm with
  | none => rw [hw] at h; cases h
  | some Γ' => rw [hw] at h; cases h; exact writeIntG_sound hw

theorem more_sound {i : Instr} {st : Step} (h : more bs next Γ i = some st) (hn : st.needs) :
    Straight (MemTy.ofList bs kinds) next Γ i st.ctx := by
  unfold more at h
  split at h
  · exact unary_sound h
  · exact shift_sound h
  · exact mulDiv_sound h
  · exact imul2_sound h
  · exact imul3_sound h
  · exact popcnt_sound h
  · exact bswapR_sound h
  · split at h
    · next a ha => cases h; exact .cdqExact (exactly_eq ha)
    · cases h; exact .cdq
  · split at h
    · next a ha => cases h; exact .cqoExact (exactly_eq ha)
    · cases h; exact .cqo
  · obtain ⟨hd, ⟨r, a, rfl, hr, hΓ, e⟩ | ⟨hr, e⟩⟩ := extend_spec (kinds := kinds) h
    · rw [e]; exact .movsxdExact hd hr hΓ
    · rw [e]; exact .movsxdRM hd hr
  · obtain ⟨hd, ⟨r, a, rfl, hr, hΓ, e⟩ | ⟨hr, e⟩⟩ := extend_spec (kinds := kinds) h
    · rw [e]; exact .movzxExact hd hr hΓ
    · rw [e]; exact .movzxRM hd hr
  · obtain ⟨hd, ⟨r, a, rfl, hr, hΓ, e⟩ | ⟨hr, e⟩⟩ := extend_spec (kinds := kinds) h
    · rw [e]; exact .movsxExact hd hr hΓ
    · rw [e]; exact .movsxRM hd hr
  · exact cmov_sound h hn
  · exact setcc_sound h hn
  · exact lea_sound h
  · exact aluMem_sound h hn
  · split at h
    · next hr => cases h; exact .testRM (readOkG_sound hr)
    · cases h
  · exact loadGlobal_sound h
  · exact storeGlobal_sound h hn
  · split at h
    · cases h
    · next hd =>
      split at h
      · next hr => cases h; exact .loadInt hd (readOkG_sound hr)
      · cases h
  · exact .storeInt (writeIntG_step h)
  · exact .storeImm (writeIntG_step h)
  · exact .store8RM (writeIntG_step h)
  · exact .store16RM (writeIntG_step h)
  · cases h

/-- **The checker**: the forms that need only the context, then the rest. -/
def check (bs : List (BitVec 64 × Layout)) (next : BitVec 64) (Γ : Ctx) (i : Instr) :
    Option Step :=
  match straight next Γ i with
  | some st => some st
  | none => more bs next Γ i

/-- **What the checker works out is a typing step**, in a program whose
memory typing is its list of blocks. -/
theorem check_sound {i : Instr} {st : Step} (h : check bs next Γ i = some st) (hn : st.needs) :
    Straight (MemTy.ofList bs kinds) next Γ i st.ctx := by
  unfold check at h
  split at h
  · next st' hs => cases h; exact straight_sound hs hn
  · exact more_sound h hn

/-! ## Operands the context does not place by evaluation

A pointer some unknown number of bytes into its block, an index that is not
a number, a block the context owns at an address that is a variable: for
these, looking does not say where the operand's bytes are, since that turns
on a comparison between things that are not numbers. So the checker is told
where they are, and checks it: what it is told picks the block and the byte,
and what cannot be settled by evaluation, an equation between addresses or a
bound, is left to be shown with the rest. Being told wrongly costs nothing
but the step: the conditions left then do not hold. -/

/-- Where the bytes of a memory operand are. -/
inductive Where
  /-- In the block the base register points into. -/
  | ptr
  /-- Byte `j` of the block the context owns at place `k`. -/
  | owned (k j : Nat)
  /-- Byte `i` of piece `k` of the stack. -/
  | piece (k i : Nat)
  /-- Byte `d` of the program's block at `base`. -/
  | block (base : BitVec 64) (d : Nat)
  /-- The instruction has no operand in memory. -/
  | reg

/-- Which element of an array a byte is in: the block is `n` copies of
`shape`, and the byte is byte `f` of copy `i`. -/
structure Elem where
  n : Nat
  shape : Shape
  i : Nat
  f : Nat

/-- What the checker is told about an instruction. -/
structure Hint where
  place : Where
  /-- The element of an array the operand is in, where the block is one. -/
  elem : Option Elem := none
  /-- For a store over a typed value of an owned block: keep the type it has. -/
  keep : Bool := false
  /-- What the flags make of the instruction's condition, where they say. -/
  taken : Option Bool := none

/-- The address a memory operand names, where the registers it is computed
from hold exactly known values. -/
def ea (Γ : Ctx) : Mem → Option (BitVec 64)
  | .sib (some b) none disp =>
    if b = .rsp then none
    else match exactly (Γ.regs b) with
      | some v => some (v + disp.signExtend 64)
      | none => none
  | .sib (some b) (some (x, sc)) disp =>
    if b = .rsp then none
    else match exactly (Γ.regs b), exactly (Γ.regs x.toReg) with
      | some v, some c => some (v + (c <<< sc.shift) + disp.signExtend 64)
      | _, _ => none
  | .sib none none disp => some (disp.signExtend 64)
  | .sib none (some (x, sc)) disp =>
    match exactly (Γ.regs x.toReg) with
    | some c => some ((c <<< sc.shift) + disp.signExtend 64)
    | none => none
  | .rip _ => none

theorem ea_spec {m : Mem} {p : BitVec 64} (h : ea Γ m = some p) : EaIs Γ m p := by
  unfold ea at h
  split at h
  · split at h
    · cases h
    · next hb =>
      split at h
      · next v hv => cases h; exact .base hb (exactly_eq hv)
      · cases h
  · split at h
    · cases h
    · next hb =>
      split at h
      · next v c hv hc => cases h; exact .indexed hb (exactly_eq hv) (exactly_eq hc)
      · cases h
  · cases h; exact .abs
  · split at h
    · next c hc => cases h; exact .absIndexed (exactly_eq hc)
    · cases h
  · cases h

/-- How many bytes on from its base an operand reaches: its displacement,
and with an index that holds an exactly known value, that value scaled. -/
def reach (Γ : Ctx) : Option (IndexReg × Scale) → BitVec 32 → Option Nat
  | none, disp => dispOf disp
  | some (x, sc), disp =>
    match exactly (Γ.regs x.toReg), dispOf disp with
    | some c, some d => some (c.toNat * 2 ^ sc.shift + d)
    | _, _ => none

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

theorem dispOf_toNat {disp : BitVec 32} {d : Nat} (h : dispOf disp = some d) :
    d = disp.toNat ∧ disp.toNat < 2 ^ 31 := by
  unfold dispOf at h
  split at h
  · next hlt => cases h; exact ⟨rfl, hlt⟩
  · cases h

theorem reach_index {x : IndexReg} {sc : Scale} {disp : BitVec 32} {d : Nat}
    (h : reach Γ (some (x, sc)) disp = some d) :
    ∃ c, Γ.regs x.toReg = .eq c ∧ (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 d := by
  simp only [reach] at h
  split at h
  · next c k hc hk =>
    cases h
    obtain ⟨rfl, hlt⟩ := dispOf_toNat hk
    exact ⟨c, exactly_eq hc, index_bytes c sc disp hlt⟩
  · cases h

/-- That byte `o` of `S` is the byte of the element of an array that the
checker was told of, where it was told of one. -/
def inElem (S : Shape) (o : Nat) : Option Elem → Prop
  | none => True
  | some e => S = e.shape.rep e.n ∧ e.i < e.n ∧ o = e.i * e.shape.size + e.f

/-- The typed value at a byte of a block: looked up, or for an element of an
array, looked up in the element. -/
def typeAt (S : Shape) (o : Nat) : Option Elem → Option Ty
  | none => S.valAt o
  | some e => if e.shape.fits then e.shape.valAt e.f else none

/-- Whether the eight bytes at a byte of a block are one typed value's alone. -/
def soleAt (S : Shape) (o : Nat) : Option Elem → Bool
  | none => S.sole o
  | some e => e.shape.fits && (e.shape.sole e.f && decide (e.f + 8 ≤ e.shape.size))

/-- Whether `n` bytes of a block are plain. -/
def freeAt (S : Shape) (o n : Nat) : Option Elem → Bool
  | none => S.free o n
  | some e => e.shape.fits && (e.shape.free e.f n && decide (e.f + n ≤ e.shape.size))

theorem typeAt_spec {S : Shape} {o : Nat} {e : Option Elem} {τ : Ty}
    (h : typeAt S o e = some τ) (he : inElem S o e) : S.valAt o = some τ := by
  cases e with
  | none => exact h
  | some e =>
    obtain ⟨rfl, hi, rfl⟩ := he
    simp only [typeAt] at h
    split at h
    · next hf => exact ShapeOf.valAt_rep hf hi h
    · cases h

theorem soleAt_spec {S : Shape} {o : Nat} {e : Option Elem}
    (h : soleAt S o e = true) (he : inElem S o e) : S.sole o = true := by
  cases e with
  | none => exact h
  | some e =>
    obtain ⟨rfl, hi, rfl⟩ := he
    simp only [soleAt, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ShapeOf.sole_rep h.1 hi h.2.2 h.2.1

theorem freeAt_spec {S : Shape} {o n : Nat} {e : Option Elem}
    (h : freeAt S o n e = true) (he : inElem S o e) : S.free o n = true := by
  cases e with
  | none => exact h
  | some e =>
    obtain ⟨rfl, hi, rfl⟩ := he
    simp only [freeAt, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ShapeOf.free_rep h.1 hi h.2.2 h.2.1

theorem toNat_ofNat_lt {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_ofNat_add_le {j n m : Nat} (h : j + n ≤ m) : (BitVec.ofNat 64 j).toNat + n ≤ m := by
  rw [BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) h

variable {bs : List (BitVec 64 × Layout)} {kinds : List (Nat × Shape)}

/-- What is left to be shown for `n` bytes to be read from an operand that
is where the checker was told. -/
def readsAt (bs : List (BitVec 64 × Layout)) (Γ : Ctx) (w : Where) (n : Nat) (m : Mem) :
    Option Prop :=
  match w, m with
  | .ptr, .sib (some b) ix disp =>
    if b = .rsp then none
    else match Γ.regs b, reach Γ ix disp with
      | .ptr S _ off, some d => some (off + d + n ≤ S.size)
      | _, _ => none
  | .owned k j, m =>
    match ea Γ m, Γ.owned[k]? with
    | some p, some (a, S) => some (p = a + BitVec.ofNat 64 j ∧ j + n ≤ S.size)
    | _, _ => none
  | .piece k i, .sib (some .rsp) ix disp =>
    match reach Γ ix disp, Γ.stack[k]? with
    | some d, some S => some (d = stackOff Γ.stack k + i ∧ i + n ≤ S.size)
    | _, _ => none
  | .block base d, m =>
    match ea Γ m, bs.find? (·.1 = base) with
    | some p, some y => some (p = base + BitVec.ofNat 64 d ∧ d + n ≤ y.2.shape.size)
    | _, _ => none
  | _, _ => none

theorem readsAt_sound {w : Where} {n : Nat} {m : Mem} {P : Prop}
    (h : readsAt bs Γ w n m = some P) (hp : P) :
    ReadOk (MemTy.ofList bs kinds) next Γ n (.mem m) := by
  unfold readsAt at h
  split at h
  · next b ix disp =>
    split at h
    · cases h
    · next hb =>
      split at h
      · next S wr off d hΓ hr =>
        cases h
        cases ix with
        | none => exact .field hb hΓ (dispOf_spec hr) hp
        | some xs =>
          obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
          exact .indexed hb hΓ hx he hp
      · cases h
  · next k j m =>
    split at h
    · next p a S hea ho =>
      cases h
      exact .owned (ea_spec hea) ⟨ho, hp.1⟩ (toNat_ofNat_add_le hp.2)
    · cases h
  · next k i ix disp =>
    split at h
    · next d S hr hs =>
      cases h
      cases ix with
      | none => exact .slot (dispOf_spec hr) ⟨hs, hp.1⟩ hp.2
      | some xs =>
        obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
        exact .slotIndexed hx he ⟨hs, hp.1⟩ hp.2
    · cases h
  · split at h
    · next p y hea hy =>
      cases h
      refine .placed (ea_spec hea) (l := y.2) ?_ hp.1 hp.2
      show (bs.find? _).map (·.2) = some y.2
      rw [hy]; rfl
    · cases h
  · cases h

/-- The context after `n` plain bytes are stored to an operand that is where
the checker was told, and what is left to be shown. -/
def writesAt (bs : List (BitVec 64 × Layout)) (Γ : Ctx) (h : Hint) (n : Nat) (m : Mem) :
    Option (Ctx × Prop) :=
  match h.place, m with
  | .ptr, .sib (some b) ix disp =>
    if b = .rsp then none
    else match Γ.regs b, reach Γ ix disp with
      | .ptr S true off, some d =>
        if freeAt S (off + d) n h.elem then
          some (Γ, off + d + n ≤ S.size ∧ inElem S (off + d) h.elem)
        else none
      | _, _ => none
  | .owned k j, m =>
    match ea Γ m, Γ.owned[k]? with
    | some p, some (a, S) =>
      if freeAt S j n h.elem then
        some (Γ, (p = a + BitVec.ofNat 64 j ∧ j + n ≤ S.size) ∧ j < 2 ^ 64 ∧ inElem S j h.elem)
      else
        some ({ Γ with owned := Γ.owned.set k (a, S.clear j n) },
          (p = a + BitVec.ofNat 64 j ∧ j + n ≤ S.size) ∧ j < 2 ^ 64)
    | _, _ => none
  | .piece k i, .sib (some .rsp) ix disp =>
    match reach Γ ix disp, Γ.stack[k]? with
    | some d, some S =>
      some ({ Γ with stack := Γ.stack.set k (S.clear i n) },
        d = stackOff Γ.stack k + i ∧ i + n ≤ S.size)
    | _, _ => none
  | .block base d, m =>
    match ea Γ m, bs.find? (·.1 = base) with
    | some p, some y =>
      if y.2.writable ∧ freeAt y.2.shape d n h.elem then
        some (Γ, (p = base + BitVec.ofNat 64 d ∧ d + n ≤ y.2.shape.size) ∧
          inElem y.2.shape d h.elem)
      else none
    | _, _ => none
  | _, _ => none

theorem writesAt_sound {hint : Hint} {n : Nat} {m : Mem} {x : Ctx × Prop}
    (h : writesAt bs Γ hint n m = some x) (hp : x.2) :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n (.mem m) x.1 := by
  unfold writesAt at h
  split at h
  · next b ix disp _ =>
    split at h
    · cases h
    · next hb =>
      split at h
      · next S off d hΓ hr =>
        split at h
        · next hfree =>
          cases h
          have hf := freeAt_spec hfree hp.2
          cases ix with
          | none => exact .field hb hΓ (dispOf_spec hr) hp.1 hf
          | some xs =>
            obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
            exact .indexed hb hΓ hx he hp.1 hf
        · cases h
      · cases h
  · next k j m _ =>
    split at h
    · next p a S hea ho =>
      split at h
      · next hfree =>
        cases h
        have e := toNat_ofNat_lt hp.2.1
        exact .owned (ea_spec hea) ⟨ho, hp.1.1⟩ (by rw [e]; exact hp.1.2)
          (by rw [e]; exact freeAt_spec hfree hp.2.2)
      · cases h
        have e := toNat_ofNat_lt hp.2
        have := WriteIntOk.ownedClear (Ψ := MemTy.ofList bs kinds) (next := next) (n := n)
          (ea_spec hea) ⟨ho, hp.1.1⟩ (by rw [e]; exact hp.1.2)
        rw [e] at this
        exact this
    · cases h
  · next k i ix disp _ =>
    split at h
    · next d S hr hs =>
      cases h
      cases ix with
      | none => exact .slot (dispOf_spec hr) ⟨hs, hp.1⟩ hp.2
      | some xs =>
        obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
        exact .slotIndexed hx he ⟨hs, hp.1⟩ hp.2
    · cases h
  · split at h
    · next p y hea hy =>
      split at h
      · next hc =>
        cases h
        refine .placed (ea_spec hea) (l := y.2) ?_ hc.1 hp.1.1 hp.1.2 (freeAt_spec hc.2 hp.2)
        show (bs.find? _).map (·.2) = some y.2
        rw [hy]; rfl
      · cases h
    · cases h
  · cases h

/-- What lets bytes be stored also lets them be read. -/
theorem writesAt_reads {hint : Hint} {n : Nat} {m : Mem} {x : Ctx × Prop}
    (h : writesAt bs Γ hint n m = some x) (hp : x.2) :
    ReadOk (MemTy.ofList bs kinds) next Γ n (.mem m) := by
  obtain ⟨Γ', P⟩ := x
  have hw := writesAt_sound (kinds := kinds) (next := next) h hp
  cases hw with
  | field hb hΓ hd hin _ => exact .field hb hΓ hd hin
  | slot hd hat hin => exact .slot hd hat hin
  | slotIndexed hx he hat hin => exact .slotIndexed hx he hat hin
  | indexed hb hΓ hx he hin _ => exact .indexed hb hΓ hx he hin
  | global hl _ ha hin _ => exact .global hl ha hin
  | owned he hat hin _ => exact .owned he hat hin
  | ownedClear he hat hin => exact .owned he hat hin
  | placed he hl _ ha hin _ => exact .placed he hl ha hin

theorem find_ofList {base : BitVec 64} {y : BitVec 64 × Layout}
    (hy : bs.find? (·.1 = base) = some y) : MemTy.ofList bs kinds base = some y.2 := by
  show (bs.find? _).map (·.2) = some y.2
  rw [hy]; rfl

/-- A 64-bit load from an operand that is where the checker was told: the
typed value there, or a number where the bytes are plain. -/
def loadAt (bs : List (BitVec 64 × Layout)) (Γ : Ctx) (h : Hint) (d : Reg) (m : Mem) :
    Option Step :=
  if d = .rsp then none
  else match h.place, m with
    | .ptr, .sib (some b) ix disp =>
      if b = .rsp then none
      else match Γ.regs b, reach Γ ix disp with
        | .ptr S _ off, some k =>
          match typeAt S (off + k) h.elem with
          | some τ => some ⟨Γ.setReg d τ, inElem S (off + k) h.elem⟩
          | none => some ⟨Γ.setReg d .int, off + k + 8 ≤ S.size⟩
        | _, _ => none
    | .owned k j, m =>
      match ea Γ m, Γ.owned[k]? with
      | some p, some (a, S) =>
        match typeAt S j h.elem with
        | some τ =>
          some ⟨Γ.setReg d τ, p = a + BitVec.ofNat 64 j ∧ j < 2 ^ 64 ∧ inElem S j h.elem⟩
        | none => some ⟨Γ.setReg d .int, p = a + BitVec.ofNat 64 j ∧ j + 8 ≤ S.size⟩
      | _, _ => none
    | .piece k i, .sib (some .rsp) ix disp =>
      match reach Γ ix disp, Γ.stack[k]? with
      | some dd, some S =>
        match typeAt S i h.elem with
        | some τ => some ⟨Γ.setReg d τ, dd = stackOff Γ.stack k + i ∧ inElem S i h.elem⟩
        | none => some ⟨Γ.setReg d .int, dd = stackOff Γ.stack k + i ∧ i + 8 ≤ S.size⟩
      | _, _ => none
    | .block base dd, m =>
      match ea Γ m, bs.find? (·.1 = base) with
      | some p, some y =>
        match typeAt y.2.shape dd h.elem with
        | some τ =>
          some ⟨Γ.setReg d τ, p = base + BitVec.ofNat 64 dd ∧ inElem y.2.shape dd h.elem⟩
        | none =>
          some ⟨Γ.setReg d .int, p = base + BitVec.ofNat 64 dd ∧ dd + 8 ≤ y.2.shape.size⟩
      | _, _ => none
    | _, _ => none

theorem loadAt_sound {hint : Hint} {d : Reg} {m : Mem} {st : Step}
    (h : loadAt bs Γ hint d m = some st) (hn : st.needs) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.r_m d m)) st.ctx := by
  unfold loadAt at h
  split at h
  · cases h
  next hd =>
  split at h
  · next b ix disp _ =>
    split at h
    · cases h
    next hb =>
    split at h
    · next S wr off k hΓ hr =>
      split at h
      · next τ hτ =>
        cases h
        have hv := typeAt_spec hτ hn
        cases ix with
        | none => exact .loadField hd hb hΓ (dispOf_spec hr) hv
        | some xs =>
          obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
          exact .loadIndexed hd hb hΓ hx he hv
      · cases h
        cases ix with
        | none => exact .loadInt hd (.field hb hΓ (dispOf_spec hr) hn)
        | some xs =>
          obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
          exact .loadInt hd (.indexed hb hΓ hx he hn)
    · cases h
  · split at h
    · next p a S hea ho =>
      split at h
      · next τ hτ =>
        cases h
        have hv := typeAt_spec hτ hn.2.2
        rw [← toNat_ofNat_lt hn.2.1] at hv
        exact .loadOwned hd (ea_spec hea) ⟨ho, hn.1⟩ hv
      · cases h
        exact .loadInt hd (.owned (ea_spec hea) ⟨ho, hn.1⟩ (toNat_ofNat_add_le hn.2))
    · cases h
  · next k i ix disp _ =>
    split at h
    · next dd S hr hs =>
      split at h
      · next τ hτ =>
        cases h
        have hv := typeAt_spec hτ hn.2
        cases ix with
        | none => exact .loadStack hd (dispOf_spec hr) ⟨hs, hn.1⟩ hv
        | some xs =>
          obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
          exact .loadStackIndexed hd hx he ⟨hs, hn.1⟩ hv
      · cases h
        cases ix with
        | none => exact .loadInt hd (.slot (dispOf_spec hr) ⟨hs, hn.1⟩ hn.2)
        | some xs =>
          obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
          exact .loadInt hd (.slotIndexed hx he ⟨hs, hn.1⟩ hn.2)
    · cases h
  · split at h
    · next p y hea hy =>
      split at h
      · next τ hτ =>
        cases h
        exact .loadHeld hd (.placed (ea_spec hea) (find_ofList hy) hn.1 (typeAt_spec hτ hn.2))
      · cases h
        exact .loadInt hd (.placed (ea_spec hea) (find_ofList hy) hn.1 hn.2)
    · cases h
  · cases h

/-- A 64-bit store to an operand that is where the checker was told. Over a
typed value of a block that others may point into, a value of its type;
into a block the context owns or a piece of the stack, anything, and the
bytes take its type. -/
def storeAt (bs : List (BitVec 64 × Layout)) (Γ : Ctx) (h : Hint) (s : Reg) (m : Mem) :
    Option Step :=
  if s = .rsp then none
  else match h.place, m with
    | .ptr, .sib (some b) ix disp =>
      if b = .rsp then none
      else match Γ.regs b, reach Γ ix disp with
        | .ptr S true off, some k =>
          match typeAt S (off + k) h.elem with
          | some τ =>
            if soleAt S (off + k) h.elem then
              some ⟨Γ, inElem S (off + k) h.elem ∧ Sub (Γ.regs s) τ⟩
            else none
          | none => (writesAt bs Γ h 8 (.sib (some b) ix disp)).map fun x => ⟨x.1, x.2⟩
        | _, _ => none
    | .owned k j, m =>
      match ea Γ m, Γ.owned[k]? with
      | some p, some (a, S) =>
        if h.keep then
          match typeAt S j h.elem with
          | some τ =>
            if soleAt S j h.elem then
              some ⟨Γ, (p = a + BitVec.ofNat 64 j ∧ j < 2 ^ 64) ∧ inElem S j h.elem ∧
                Sub (Γ.regs s) τ⟩
            else none
          | none => none
        else if (Γ.regs s).isInt then (writesAt bs Γ h 8 m).map fun x => ⟨x.1, x.2⟩
        else
          some ⟨{ Γ with owned := Γ.owned.set k (a, S.set j (Γ.regs s)) },
            (p = a + BitVec.ofNat 64 j ∧ j + 8 ≤ S.size) ∧ j < 2 ^ 64⟩
      | _, _ => none
    | .piece k i, .sib (some .rsp) none disp =>
      match dispOf disp, Γ.stack[k]? with
      | some dd, some S =>
        some ⟨{ Γ with stack := Γ.stack.set k (S.set i (Γ.regs s)) },
          dd = stackOff Γ.stack k + i ∧ i + 8 ≤ S.size⟩
      | _, _ => none
    | _, m => (writesAt bs Γ h 8 m).map fun x => ⟨x.1, x.2⟩

theorem writesAt_step {hint : Hint} {n : Nat} {m : Mem} {st : Step}
    (h : (writesAt bs Γ hint n m).map (fun x => (⟨x.1, x.2⟩ : Step)) = some st) (hn : st.needs) :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n (.mem m) st.ctx := by
  cases hw : writesAt bs Γ hint n m with
  | none => rw [hw] at h; cases h
  | some x => rw [hw] at h; cases h; exact writesAt_sound hw hn

theorem storeAt_sound {hint : Hint} {s : Reg} {m : Mem} {st : Step}
    (h : storeAt bs Γ hint s m = some st) (hn : st.needs) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.rm_r (.mem m) s)) st.ctx := by
  unfold storeAt at h
  split at h
  · cases h
  next hs =>
  split at h
  · next b ix disp _ =>
    split at h
    · cases h
    next hb =>
    split at h
    · next S off k hΓ hr =>
      split at h
      · next τ hτ =>
        split at h
        · next hso =>
          cases h
          have hv := typeAt_spec hτ hn.1
          have hso' := soleAt_spec hso hn.1
          cases ix with
          | none => exact .storeField hb hs hΓ (dispOf_spec hr) hv hso' hn.2
          | some xs =>
            obtain ⟨c, hx, he⟩ := reach_index (x := xs.1) (sc := xs.2) hr
            exact .storeIndexed hb hs hΓ hx he hv hso' hn.2
        · cases h
      · exact .storeInt (writesAt_step h hn)
    · cases h
  · split at h
    · next p a S hea ho =>
      split at h
      · split at h
        · next τ hτ =>
          split at h
          · next hso =>
            cases h
            have e := toNat_ofNat_lt hn.1.2
            exact .storeOwnedKeep hs (ea_spec hea) ⟨ho, hn.1.1⟩
              (by rw [e]; exact typeAt_spec hτ hn.2.1) (by rw [e]; exact soleAt_spec hso hn.2.1)
              hn.2.2
          · cases h
        · cases h
      · split at h
        · exact .storeInt (writesAt_step h hn)
        · cases h
          have e := toNat_ofNat_lt hn.2
          have := Straight.storeOwned (Ψ := MemTy.ofList bs kinds) (next := next) hs
            (ea_spec hea) ⟨ho, hn.1.1⟩ (by rw [e]; exact hn.1.2)
          rw [e] at this
          exact this
    · cases h
  · next k i disp _ =>
    split at h
    · next dd S hr hs' =>
      cases h
      exact .storeStack hs (dispOf_spec hr) ⟨hs', hn.1⟩ hn.2
    · cases h
  · exact .storeInt (writesAt_step h hn)

/-- **The checker for an instruction it is told something about**: where the
operand in memory is, or what the flags make of a condition. -/
def hinted (bs : List (BitVec 64 × Layout)) (Γ : Ctx) (h : Hint) : Instr → Option Step
  | .mov .w64 (.r_m d m) => loadAt bs Γ h d m
  | .mov .w64 (.rm_r (.mem m) s) => storeAt bs Γ h s m
  | .mov w (.r_m d m) =>
    if d = .rsp then none
    else (readsAt bs Γ h.place w.bytes.toNat m).map fun P => ⟨Γ.setReg d .int, P⟩
  | .mov w (.rm_r (.mem m) _) => (writesAt bs Γ h w.bytes.toNat m).map fun x => ⟨x.1, x.2⟩
  | .mov w (.rm_i (.mem m) _) => (writesAt bs Γ h w.bytes.toNat m).map fun x => ⟨x.1, x.2⟩
  | .store8 m _ => (writesAt bs Γ h 1 m).map fun x => ⟨x.1, x.2⟩
  | .store16 m _ => (writesAt bs Γ h 2 m).map fun x => ⟨x.1, x.2⟩
  | .alu op w (.r_m d m) =>
    if d = .rsp then none
    else (readsAt bs Γ h.place w.bytes.toNat m).map fun P =>
      ⟨Γ.afterAlu op d, P ∧ carryNeeds Γ op⟩
  | .alu op w (.rm_r (.mem m) _) | .alu op w (.rm_i (.mem m) _) =>
    if op.writesDst then
      (writesAt bs Γ h w.bytes.toNat m).map fun x =>
        ⟨{ x.1 with flags := Flags.Known }, x.2 ∧ carryNeeds Γ op⟩
    else (readsAt bs Γ h.place w.bytes.toNat m).map fun P =>
      ⟨{ Γ with flags := Flags.Known }, P⟩
  | .test w (.mem m) _ =>
    (readsAt bs Γ h.place w.bytes.toNat m).map fun P => ⟨{ Γ with flags := Flags.Known }, P⟩
  | .unary .neg w (.mem m) =>
    (writesAt bs Γ h w.bytes.toNat m).map fun x => ⟨{ x.1 with flags := Flags.Known }, x.2⟩
  | .unary .not w (.mem m) => (writesAt bs Γ h w.bytes.toNat m).map fun x => ⟨x.1, x.2⟩
  | .shift op w (.mem m) (.imm n) =>
    (writesAt bs Γ h w.bytes.toNat m).map fun x =>
      ⟨{ x.1 with flags := op.flagsAfter (n.toNat % w.bits) Γ.flags }, x.2⟩
  | .shift _ w (.mem m) .cl =>
    (writesAt bs Γ h w.bytes.toNat m).map fun x => ⟨{ x.1 with flags := Flags.Any }, x.2⟩
  | .mulDiv .mul w (.mem m) =>
    (readsAt bs Γ h.place w.bytes.toNat m).map fun P => ⟨Γ.afterMulDiv Flags.AfterMul, P⟩
  | .mulDiv .imul w (.mem m) =>
    (readsAt bs Γ h.place w.bytes.toNat m).map fun P => ⟨Γ.afterMulDiv Flags.AfterMul, P⟩
  -- a divide of exactly known values that are not numbers: it is typed where
  -- it is shown not to fault
  | .mulDiv .div w (.reg r) =>
    if r = .rsp then none
    else match exactly (Γ.regs .rax), exactly (Γ.regs .rdx), exactly (Γ.regs r) with
      | some a, some d, some b =>
        some ⟨{ (Γ.setReg .rax (.eq ((a.setWidth w.bits / b.setWidth w.bits).setWidth 64))).setReg
            .rdx (.eq ((a.setWidth w.bits % b.setWidth w.bits).setWidth 64)) with
          flags := (· = Flags.unknown) },
          d.setWidth w.bits = 0 ∧ b.setWidth w.bits ≠ 0⟩
      | _, _, _ => none
  | .mulDiv .idiv w (.reg r) =>
    if r = .rsp then none
    else match exactly (Γ.regs .rax), exactly (Γ.regs .rdx), exactly (Γ.regs r) with
      | some a, some d, some b =>
        some ⟨{ (Γ.setReg .rax
            (.eq (((a.setWidth w.bits).sdiv (b.setWidth w.bits)).setWidth 64))).setReg
            .rdx (.eq (((a.setWidth w.bits).srem (b.setWidth w.bits)).setWidth 64)) with
          flags := (· = Flags.unknown) },
          d.setWidth w.bits = signFill (a.setWidth w.bits) ∧ b.setWidth w.bits ≠ 0 ∧
            (a.setWidth w.bits ≠ BitVec.intMin w.bits ∨ b.setWidth w.bits ≠ -1#w.bits)⟩
      | _, _, _ => none
  | .imul2 w d (.mem m) =>
    if d = .rsp then none
    else (readsAt bs Γ h.place w.bytes.toNat m).map fun P =>
      ⟨{ Γ.setReg d .int with flags := Flags.AfterMul }, P⟩
  | .imul3 w d (.mem m) _ =>
    if d = .rsp then none
    else (readsAt bs Γ h.place w.bytes.toNat m).map fun P =>
      ⟨{ Γ.setReg d .int with flags := Flags.AfterMul }, P⟩
  | .popcnt w d (.mem m) =>
    if d = .rsp then none
    else (readsAt bs Γ h.place w.bytes.toNat m).map fun P =>
      ⟨{ Γ.setReg d .int with flags := Flags.Known }, P⟩
  | .movsxd d (.mem m) =>
    if d = .rsp then none
    else (readsAt bs Γ h.place 4 m).map fun P => ⟨Γ.setReg d .int, P⟩
  | .movzx _ d sw (.mem m) =>
    if d = .rsp then none
    else (readsAt bs Γ h.place sw.bytes m).map fun P => ⟨Γ.setReg d .int, P⟩
  | .movsx _ d sw (.mem m) =>
    if d = .rsp then none
    else (readsAt bs Γ h.place sw.bytes m).map fun P => ⟨Γ.setReg d .int, P⟩
  | .cmov c w d (.mem m) =>
    if d = .rsp then none
    else (readsAt bs Γ h.place w.bytes.toNat m).map fun P =>
      ⟨Γ.setReg d .int, P ∧ decides Γ c⟩
  -- between exactly known values, where the flags say which way it goes
  | .cmov c w d (.reg r) =>
    if d = .rsp ∨ r = .rsp then none
    else match h.taken, exactly (Γ.regs d), exactly (Γ.regs r) with
      | some t, some x, some a =>
        some ⟨Γ.setReg d
          (.eq ((if t then a.setWidth w.bits else x.setWidth w.bits).setWidth 64)),
          ∀ f, Γ.flags f → c.eval f = some t⟩
      | _, _, _ => some ⟨Γ.setReg d .int, decides Γ c⟩
  | .setcc c (.mem m) => (writesAt bs Γ h 1 m).map fun x => ⟨x.1, x.2 ∧ decides Γ c⟩
  | .setcc c (.reg d) =>
    if d = .rsp then none
    else match h.taken, exactly (Γ.regs d) with
      | some t, some x =>
        some ⟨Γ.setReg d
          (.eq ((x &&& ~~~0xff) ||| (if t then (1 : BitVec 8) else 0).setWidth 64)),
          ∀ f, Γ.flags f → c.eval f = some t⟩
      | _, _ => some ⟨Γ.setReg d .int, decides Γ c⟩
  | _ => none

theorem readsAt_step {w : Where} {n : Nat} {m : Mem} {f : Prop → Step} {st : Step}
    (h : (readsAt bs Γ w n m).map f = some st) :
    ∃ P, readsAt bs Γ w n m = some P ∧ st = f P := by
  cases hr : readsAt bs Γ w n m with
  | none => rw [hr] at h; cases h
  | some P => rw [hr] at h; cases h; exact ⟨P, rfl, rfl⟩

theorem writesAt_map {hint : Hint} {n : Nat} {m : Mem} {f : Ctx × Prop → Step} {st : Step}
    (h : (writesAt bs Γ hint n m).map f = some st) :
    ∃ x, writesAt bs Γ hint n m = some x ∧ st = f x := by
  cases hw : writesAt bs Γ hint n m with
  | none => rw [hw] at h; cases h
  | some x => rw [hw] at h; cases h; exact ⟨x, rfl, rfl⟩

/-- **What the checker works out from what it is told is a typing step.** -/
theorem hinted_sound {hint : Hint} {i : Instr} {st : Step}
    (h : hinted bs Γ hint i = some st) (hn : st.needs) :
    Straight (MemTy.ofList bs kinds) next Γ i st.ctx := by
  unfold hinted at h
  split at h
  · exact loadAt_sound h hn
  · exact storeAt_sound h hn
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .loadInt hd (readsAt_sound hr hn)
  · exact .storeInt (writesAt_step h hn)
  · exact .storeImm (writesAt_step h hn)
  · exact .store8RM (writesAt_step h hn)
  · exact .store16RM (writesAt_step h hn)
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .aluLoad hd (readsAt_sound hr hn.1) hn.2
  · split at h
    · next hwd =>
      obtain ⟨x, hw, rfl⟩ := writesAt_map h
      exact .aluStoreR hwd (writesAt_reads hw hn.1) (writesAt_sound hw hn.1) hn.2
    · next hwd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .cmpR ((Bool.not_eq_true _).mp hwd) (readsAt_sound hr hn)
  · split at h
    · next hwd =>
      obtain ⟨x, hw, rfl⟩ := writesAt_map h
      exact .aluStoreI hwd (writesAt_reads hw hn.1) (writesAt_sound hw hn.1) hn.2
    · next hwd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .cmpI ((Bool.not_eq_true _).mp hwd) (readsAt_sound hr hn)
  · obtain ⟨P, hr, rfl⟩ := readsAt_step h
    exact .testRM (readsAt_sound hr hn)
  · obtain ⟨x, hw, rfl⟩ := writesAt_map h
    exact .negRM (writesAt_reads hw hn) (writesAt_sound hw hn)
  · obtain ⟨x, hw, rfl⟩ := writesAt_map h
    exact .notRM (writesAt_reads hw hn) (writesAt_sound hw hn)
  · obtain ⟨x, hw, rfl⟩ := writesAt_map h
    exact .shiftImm (writesAt_reads hw hn) (writesAt_sound hw hn)
  · obtain ⟨x, hw, rfl⟩ := writesAt_map h
    exact .shiftCl (writesAt_reads hw hn) (writesAt_sound hw hn)
  · obtain ⟨P, hr, rfl⟩ := readsAt_step h
    exact .mulRM (readsAt_sound hr hn)
  · obtain ⟨P, hr, rfl⟩ := readsAt_step h
    exact .imulRM (readsAt_sound hr hn)
  · split at h
    · cases h
    · next hr =>
      split at h
      · next a d b ha hd hb =>
        cases h
        exact .mulDivExact hr (exactly_eq ha) (exactly_eq hd) (exactly_eq hb)
          (by rw [hn.1]; exact MulDivOp.eval_div _ _ hn.2)
      · cases h
  · split at h
    · cases h
    · next hr =>
      split at h
      · next a d b ha hd hb =>
        cases h
        exact .mulDivExact hr (exactly_eq ha) (exactly_eq hd) (exactly_eq hb)
          (by rw [hn.1]; exact MulDivOp.eval_idiv _ _ hn.2.1 hn.2.2)
      · cases h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .imul2RM hd (readsAt_sound hr hn)
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .imul3RM hd (readsAt_sound hr hn)
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .popcntRM hd (readsAt_sound hr hn)
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .movsxdRM hd (readsAt_sound hr hn)
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .movzxRM hd (readsAt_sound hr hn)
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .movsxRM hd (readsAt_sound hr hn)
  · split at h
    · cases h
    · next hd =>
      obtain ⟨P, hr, rfl⟩ := readsAt_step h
      exact .cmovRM hd (readsAt_sound hr hn.1) hn.2
  · split at h
    · cases h
    · next hc =>
      split at h
      · next t x a _ hx ha =>
        cases h
        exact .cmovExact (fun e => hc (.inl e)) (fun e => hc (.inr e)) (exactly_eq hx)
          (exactly_eq ha) hn
      · cases h; exact .cmovRM (fun e => hc (.inl e)) (.reg _) hn
  · obtain ⟨x, hw, rfl⟩ := writesAt_map h
    exact .setccRM (writesAt_sound hw hn.1) hn.2
  · split at h
    · cases h
    · next hd =>
      split at h
      · next t x _ hx => cases h; exact .setccExact hd (exactly_eq hx) hn
      · cases h; exact .setccRM (.reg hd) hn
  · cases h

/-- A block that begins with an instruction the checker has worked out from
what it was told. -/
theorem hinted_block {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {a : BitVec 64} {i : Instr}
    {len : BitVec 64} {hint : Hint} {st : Step} (hf : fetch a = some (i, len))
    (hc : hinted bs Γ hint i = some st) (hn : st.needs)
    (hrest : BlockOk Φ fetch sys (MemTy.ofList bs kinds) (a + len) st.ctx) :
    BlockOk Φ fetch sys (MemTy.ofList bs kinds) a Γ :=
  .step hf (hinted_sound hc hn) hrest

/-! What the driver shows of the places it tells the checker of: each is
one lemma applied, with nothing searched for. -/

theorem own0 (a : BitVec 64) (disp : BitVec 32) :
    a + disp.signExtend 64 = a + BitVec.ofNat 64 (disp.signExtend 64).toNat := by simp

theorem own1 (a t : BitVec 64) (disp : BitVec 32) :
    a + t + disp.signExtend 64 = a + BitVec.ofNat 64 (t + disp.signExtend 64).toNat := by
  rw [BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ownI0 (a c : BitVec 64) (sc : Scale) (disp : BitVec 32) (hd : disp.toNat < 2 ^ 31) :
    a + (c <<< sc.shift) + disp.signExtend 64
      = a + BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift + disp.toNat) := by
  rw [BitVec.add_assoc, index_bytes c sc disp hd]

theorem ownI1 (a t c : BitVec 64) (sc : Scale) (disp : BitVec 32) (hd : disp.toNat < 2 ^ 31) :
    a + t + (c <<< sc.shift) + disp.signExtend 64
      = a + BitVec.ofNat 64 (t.toNat + (c.toNat * 2 ^ sc.shift + disp.toNat)) := by
  rw [BitVec.add_assoc, BitVec.add_assoc, index_bytes c sc disp hd,
    BitVec.ofNat_add (x := t.toNat), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem block_idx (c : BitVec 64) (sc : Scale) (disp : BitVec 32) (base : BitVec 64) (d : Nat)
    (h : disp.signExtend 64 = base + BitVec.ofNat 64 d) :
    (c <<< sc.shift) + disp.signExtend 64
      = base + BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift + d) := by
  have hc : c <<< sc.shift = BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [h, hc, BitVec.ofNat_add]
  ac_rfl

theorem piece_at (x D P R : Nat) (h : D = P + R) : x + D = P + (x + R) := by omega

theorem piece_at0 (x D : Nat) : x + D = D + x := Nat.add_comm x D

theorem elem_at (x es q f R : Nat) (h : R = q * es + f) : x * es + R = (x + q) * es + f := by
  rw [h, Nat.add_mul]; omega

theorem elem_at0 (x es q : Nat) : x * es + q * es = (x + q) * es + 0 := by
  rw [Nat.add_mul]; rfl

theorem elem_comm (a k D : Nat) : a * k + D = k * a + D := by rw [Nat.mul_comm]

theorem elem_idx (x es L D q f : Nat) (h : L + D = q * es + f) :
    L + (x * es + D) = (x + q) * es + f := by
  rw [Nat.add_mul]; omega

theorem elem_idx0 (x es L D f : Nat) (h : L + D = f) : L + (x * es + D) = x * es + f := by
  omega

theorem eval_exact (c : Cond) (fl : Flags) (b : Bool) (h : c.eval fl = some b) :
    ∀ f, f = fl → c.eval f = some b := fun _ hf => hf ▸ h

end Check

export Check (sext_toNat index_bytes)

/-- A block that begins with an instruction the checker has worked out. -/
theorem BlockOk.checked {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {a : BitVec 64} {Γ : Ctx} {i : Instr} {len : BitVec 64} {st : Check.Step}
    (hf : fetch a = some (i, len)) (hc : Check.straight (a + len) Γ i = some st)
    (hn : st.needs) (hrest : BlockOk Φ fetch sys Ψ (a + len) st.ctx) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .step hf (Check.straight_sound hc hn) hrest

end TypedAsm
