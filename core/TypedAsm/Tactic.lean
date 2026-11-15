import Lean
import TypedAsm.Program
import TypedAsm.Fn
import TypedAsm.Print
import TypedAsm.Blocks
import TypedAsm.Linux
import TypedAsm.Owned
import TypedAsm.RegMap
import TypedAsm.Entry
import TypedAsm.Segments
import TypedAsm.EndToEnd
import TypedAsm.Lookup
import TypedAsm.FnEx

/-!
# Tactics for typing programs

These build typing derivations; the kernel checks the result, so nothing here
is trusted. They handle the mechanical parts and leave as goals whatever
needs an argument, typically a fact about values at a branch.

* `ty_block` types a whole block of a labelled program, finding jump targets
  by label. `ty_call sig` types a call. These are the usual entry points.
* `ty_steps` types the straight-line instructions at the start of a block.
* `ty_step` types one. `ty_step_with r` types one with a rule you name.
* `ty_branch` types a conditional jump and leaves the side that carries on.
* `ty_straight` types a single instruction; the two above are built on it.
* `ty_name r as v` gives the value in a register a name; `ty_name_slot i as v`
  does the same for a stack slot.
* `ty_open r` and `ty_null r` open a pointer to a kind of block and
  split a value that may be null.
* `ty_mmap shape` and `ty_mmap_kind tag` type an `mmap` for fresh memory;
  `ty_err r as e` then splits what it handed back into an error number and
  a pointer.
* `ty_fn_ptr r to sig` turns a register holding a function's address into a
  pointer to that function.
* `ty_code_ptr r to Δ` turns a register holding a label's address into a
  code pointer, for indirect jumps and calls.
* `ty_accept h` shows the current context is accepted at an address, given
  the fact `h` that the code typing allows some context there.
* `ty_into h` types one instruction and ends the block there, handing over
  to the label that follows.
* `ty_mmap_own as p` types an `mmap` whose memory the program then owns, at
  an address called `p`; `ty_munmap` types giving an owned block back;
  `ty_freeze r` turns the owned block whose address is in `r` into an
  ordinary shared block, and `r` into a pointer to it.
* `ty_split r at m` regards the owned block whose address is in `r` as two,
  the first `m` fields and the rest; `ty_join r` regards that block and the
  one that starts where it ends as one.
* `ty_own_first r` lists the owned block whose address is in `r` first, which
  is where a call takes the blocks it hands over from. A system call's
  buffer may be in an owned block, and a signature may take and give blocks
  (`FnSig.takes`, `FnSig.gives`).
* `ty_call sig returning ret` types a call to a function that hands back
  something it made (`FnSigEx`); inside such a function, `ty_return_as x`
  says which of the contexts it returns into.
* `ty_byte as b` types the load of a byte of text and splits on it: zero, or
  some `b` that is not, after which the pointer may be stepped forward.
* `ctx_sub` and `sub_regs` compare contexts.
-/

namespace TypedAsm

/-! ## Lemmas the tactics apply -/

/-- The byte a displacement reaches, computed from the displacement. -/
theorem byteDisp_of (disp : BitVec 32) (hlt : disp.toNat < 2 ^ 31) :
    byteDisp disp.toNat disp := by
  refine ⟨?_, hlt⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- Releasing the pieces at the top of the stack that come to `k` bytes, with
what is left of the stack computed. -/
theorem Straight.freeFrame' {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {k : Nat} {imm : BitVec 32}
    {rest : List Shape} (hk : byteDisp k imm) (hd : stackDrop Γ.stack k = some rest) :
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm))
      { Γ.moveSp (BitVec.ofNat 64 k) with
        stack := rest, room := Γ.room + k, flags := Flags.Known } := by
  obtain ⟨top, hst, hlen⟩ := stackDrop_eq hd
  exact .freeFrame hk hst hlen

/-! Which piece of the stack a byte above the stack pointer is in: at a fixed
distance, through an index scaled by eight, and through any index. -/

theorem stackAt_lit {d o : Nat} (h : o ≤ d) : d = o + (d - o) := by omega

theorem stackAt_idx8 {x j o : Nat} (ho : o % 8 = 0) (hm : o / 8 ≤ j) :
    8 * (x + j) = o + (0 + 8 * (x + (j - o / 8))) := by omega

theorem stackAt_bytes {x dd o : Nat} (h : o ≤ dd) : x + dd = o + (x + (dd - o)) := by omega

/-- A piece of the stack may be regarded as two, cut a fixed distance above
the stack pointer. -/
theorem BlockOk.splitStackAt {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {a : BitVec 64} {Γ : Ctx} {k d : Nat} {S : Shape}
    (hk : Γ.stack[k]? = some S) (_hlo : stackOff Γ.stack k < d)
    (hm : d - stackOff Γ.stack k ≤ S.size)
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.take k ++
          [S.take (d - stackOff Γ.stack k), S.drop (d - stackOff Γ.stack k)] ++
          Γ.stack.drop (k + 1) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .splitStack hk hm hrest

/-- The two pieces of the stack that meet a fixed distance above the stack
pointer may be regarded as one. -/
theorem BlockOk.joinStackAt {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {a : BitVec 64} {Γ : Ctx} {k d : Nat} {S₁ S₂ : Shape}
    (hk : Γ.stack[k]? = some S₁) (hk' : Γ.stack[k + 1]? = some S₂)
    (_hd : stackOff Γ.stack (k + 1) = d)
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.take k ++ [S₁.append S₂] ++ Γ.stack.drop (k + 2) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .joinStack hk hk' hrest

/-- Eight bytes of the stack, a fixed distance above the stack pointer, may
be given a name for the value they hold. -/
theorem BlockOk.nameSlotAt {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {a : BitVec 64} {Γ : Ctx} {k d : Nat} {S : Shape}
    (hk : Γ.stack[k]? = some S) (_hlo : stackOff Γ.stack k ≤ d)
    (hi : d - stackOff Γ.stack k + 8 ≤ S.size)
    (hrest : ∀ v, BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.set k (S.set (d - stackOff Γ.stack k) (.eq v)) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .nameSlot hk hi hrest

/-! Operands at a fixed address. Which block the address falls in, and where,
is found by computation: the first premise of each lemma below is there only
to be solved by `rfl`, which determines the block and the byte. -/

/-- The block among `bs` that contains address `a`, with the byte of it that
`a` is at. -/
def MemTy.locate (bs : List (BitVec 64 × Layout)) (a : BitVec 64) :
    Option (BitVec 64 × Nat) :=
  bs.findSome? fun x =>
    if (a - x.1).toNat < x.2.size then some (x.1, (a - x.1).toNat) else none

section Globals

variable {bs : List (BitVec 64 × Layout)} {kinds : List (Nat × Shape)} {next base : BitVec 64}
  {Γ : Ctx} {l : Layout} {d n : Nat} {disp : BitVec 32} {τ : Ty}

theorem ReadOk.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hin : d + n ≤ l.shape.size) :
    ReadOk (MemTy.ofList bs kinds) next Γ n (.mem (.rip disp)) :=
  .global hl haddr hin

theorem WriteIntOk.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l) (hw : l.writable = true)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hin : d + n ≤ l.shape.size) (hfree : l.shape.free d n = true) :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n (.mem (.rip disp)) Γ :=
  .global hl hw haddr hin hfree

theorem Holds.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hi : l.shape.valAt d = some τ) :
    Holds (MemTy.ofList bs kinds) next Γ (.mem (.rip disp)) τ :=
  .global hl haddr hi

theorem Straight.loadGlobal_of {r : Reg} (hd : r ≠ .rsp)
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hi : l.shape.valAt d = some τ) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.r_m r (.rip disp))) (Γ.setReg r τ) :=
  .loadGlobal hd hl haddr hi

theorem Straight.storeGlobal_of {s : Reg} (hs : s ≠ .rsp)
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l) (hw : l.writable = true)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hi : l.shape.valAt d = some τ) (hso : l.shape.sole d = true) (hsub : Sub (Γ.regs s) τ) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.rm_r (.mem (.rip disp)) s)) Γ :=
  .storeGlobal hs hl hw haddr hi hso hsub

end Globals

/-! Indexed operands: which byte a scaled index lands on. These hold for any
index, since addresses wrap; what needs a bound on the index is the byte
being inside the block. -/

theorem sext_toNat {disp : BitVec 32} (hd : disp.toNat < 2 ^ 31) :
    disp.signExtend 64 = BitVec.ofNat 64 disp.toNat := by
  have h := sext_small hd
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

/-- An index scaled by 8 with a displacement that is a multiple of 8 lands
on a whole eight-byte cell. -/
theorem index8_slot (c : BitVec 64) (disp : BitVec 32)
    (h8 : disp.toNat % 8 = 0) (hd : disp.toNat < 2 ^ 31) :
    (c <<< Scale.s8.shift) + disp.signExtend 64
      = BitVec.ofNat 64 (8 * (c.toNat + disp.toNat / 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Scale.shift]
  omega

/-- An index with any scale and displacement, as a number of bytes. -/
theorem index_bytes (c : BitVec 64) (sc : Scale) (disp : BitVec 32) (hd : disp.toNat < 2 ^ 31) :
    (c <<< sc.shift) + disp.signExtend 64
      = BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift + disp.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize c.toNat * 2 ^ sc.shift = m
  omega

/-- After `cmp a, b`, "below" holds exactly when `a` is less than `b` as
unsigned numbers. This is the fact a bounds check establishes. -/
theorem cmp_below_iff (a b : BitVec 64) :
    Cond.eval (AluOp.apply .cmp a b).2 .b = some (decide (a.toNat < b.toNat)) := by
  have h := subBorrow_cf .w64 a b
  simp only [AluOp.apply, Cond.eval]
  rw [h]
  rfl

theorem cmp_below {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .b = some true) :
    a.toNat < b.toNat := by
  rw [cmp_below_iff] at h
  simpa using h

theorem cmp_not_below {a b : BitVec 64}
    (h : Cond.eval (AluOp.apply .cmp a b).2 .b = some false) : b.toNat ≤ a.toNat := by
  rw [cmp_below_iff] at h
  simpa using h

/-- After `cmp a, b`, "less" holds exactly when `a` is less than `b` as
signed numbers. -/
theorem cmp_less_iff (a b : BitVec 64) :
    Cond.eval (AluOp.apply .cmp a b).2 .l = some (a.slt b) := by
  have := a.isLt; have := b.isLt
  simp only [AluOp.apply, Cond.eval, subBorrow, Flags.ofResult, bind, Option.bind, pure,
    Option.some.injEq, BitVec.slt]
  rw [Bool.eq_iff_iff]
  simp [BitVec.msb_eq_decide, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toInt_eq_toNat_cond]
  generalize hr : (36893488147419103232 - b.toNat % 36893488147419103232 + a.toNat)
    % 18446744073709551616 = r
  by_cases h1 : 9223372036854775808 ≤ a.toNat <;> by_cases h2 : 9223372036854775808 ≤ b.toNat <;>
    by_cases h3 : 9223372036854775808 ≤ r <;> simp [h1, h2, h3] <;> omega

theorem cmp_less {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .l = some true) :
    a.slt b = true := by
  rw [cmp_less_iff] at h
  simpa using h

theorem cmp_not_less {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .l = some false) :
    a.slt b = false := by
  rw [cmp_less_iff] at h
  simpa using h

/-- After `cmp a, b`, "above or equal" failing means `a` is less than `b` as
unsigned numbers: the way a loop over a count carries on. -/
theorem cmp_not_ae {a b : BitVec 64}
    (h : Cond.eval (AluOp.apply .cmp a b).2 .ae = some false) : a.toNat < b.toNat := by
  have e : Cond.eval (AluOp.apply .cmp a b).2 .ae
      = (Cond.eval (AluOp.apply .cmp a b).2 .b).map (!·) := rfl
  rw [e, cmp_below_iff] at h
  simpa using h

/-- After `cmp a, b`, "above or equal" holding means `b` is at most `a`. -/
theorem cmp_ae {a b : BitVec 64}
    (h : Cond.eval (AluOp.apply .cmp a b).2 .ae = some true) : b.toNat ≤ a.toNat := by
  have e : Cond.eval (AluOp.apply .cmp a b).2 .ae
      = (Cond.eval (AluOp.apply .cmp a b).2 .b).map (!·) := rfl
  rw [e, cmp_below_iff] at h
  simpa using h

theorem getElem?_replicate_of_lt {n i : Nat} {τ : Ty} (h : i < n) :
    (List.replicate n τ)[i]? = some τ := by
  simp [h]

/-- Exact-value types are compared by comparing the values. -/
theorem Sub.of_eq {a b : BitVec 64} (h : a = b) : Sub (.eq a) (.eq b) :=
  h ▸ .refl _

/-- An unsigned divide whose dividend has a zero upper half and whose divisor
is known not to be zero cannot raise a divide error. -/
theorem Straight.divSafe {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {w : Width} {r : Reg}
    {a d b : BitVec 64} (hr : r ≠ .rsp) (hΓa : Γ.regs .rax = .eq a) (hΓd : Γ.regs .rdx = .eq d)
    (hΓr : Γ.regs r = .eq b) (hd : d.setWidth w.bits = 0) (hb : b.setWidth w.bits ≠ 0) :
    Straight Ψ next Γ (.mulDiv .div w (.reg r))
      { (Γ.setReg .rax (.eq ((a.setWidth w.bits / b.setWidth w.bits).setWidth 64))).setReg .rdx
          (.eq ((a.setWidth w.bits % b.setWidth w.bits).setWidth 64)) with
        flags := (· = Flags.unknown) } :=
  .mulDivExact hr hΓa hΓd hΓr (by rw [hd]; exact MulDivOp.eval_div _ _ hb)

/-- A signed divide whose dividend has been sign-extended into `rdx` (as
`cqo` and `cdq` do) and whose divisor is known not to be zero cannot raise a
divide error, unless it is the most negative number divided by minus one. -/
theorem Straight.idivSafe {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {w : Width} {r : Reg}
    {a d b : BitVec 64} (hr : r ≠ .rsp) (hΓa : Γ.regs .rax = .eq a) (hΓd : Γ.regs .rdx = .eq d)
    (hΓr : Γ.regs r = .eq b) (hd : d.setWidth w.bits = signFill (a.setWidth w.bits))
    (hb : b.setWidth w.bits ≠ 0)
    (hov : a.setWidth w.bits ≠ BitVec.intMin w.bits ∨ b.setWidth w.bits ≠ -1#w.bits) :
    Straight Ψ next Γ (.mulDiv .idiv w (.reg r))
      { (Γ.setReg .rax (.eq (((a.setWidth w.bits).sdiv (b.setWidth w.bits)).setWidth 64))).setReg
          .rdx (.eq (((a.setWidth w.bits).srem (b.setWidth w.bits)).setWidth 64)) with
        flags := (· = Flags.unknown) } :=
  .mulDivExact hr hΓa hΓd hΓr (by rw [hd]; exact MulDivOp.eval_idiv _ _ hb hov)

theorem Flags.cf_isSome_of_known {f : Flags} (h : Flags.Known f) : f.cf.isSome = true := by
  simp only [Flags.Known, Flags.defined, Bool.and_eq_true] at h
  exact h.1.1.1

/-- When the flags are known, every condition is decided. -/
theorem Cond.decided_of_known {P : Flags → Prop} (hP : ∀ f, P f → Flags.Known f) (c : Cond) :
    ∀ f, P f → ∃ b, c.eval f = some b :=
  fun f hf => Cond.eval_some (hP f hf) c

/-! ## Comparing contexts

A note on how these are written. A side condition is never proved by a
nested `by` inside a term: when such a block fails, Lean logs the error and
carries on, so a `first` would not move on to its next alternative. Instead
each side condition becomes a goal and is proved by a following tactic. -/

/-- Proves `Sub τ υ` when it holds for a structural reason. -/
syntax "ty_sub" : tactic

/-- A `Sub` goal restated with both types reduced to their outermost form,
and whether both are exactly known values. Comparing the reduced types
keeps the comparison from wandering into whatever the unreduced ones
mention along the way. -/
private def headForm? (g : Lean.MVarId) : Lean.Meta.MetaM (Option (Lean.MVarId × Bool)) :=
  g.withContext do
    let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
    unless t.isAppOfArity ``Sub 2 do return none
    let a ← Lean.Meta.whnf t.appFn!.appArg!
    let b ← Lean.Meta.whnf t.appArg!
    let g' ← g.change (Lean.mkApp2 (Lean.mkConst ``Sub) a b)
    return some (g', a.isAppOfArity ``Ty.eq 1 && b.isAppOfArity ``Ty.eq 1)

open Lean Meta Elab Tactic in
/-- Compares two exactly known values. They are never compared by unfolding
arithmetic, which runs away when a variable has a large constant added to
it: values with no variables in them are compared by computing, and others
as written, then from the hypotheses, then by bit-vector arithmetic. -/
elab "ty_sub_exact" : tactic => do
  let some (g, true) ← headForm? (← getMainGoal) | throwError "not two exactly known values"
  let t ← g.getType
  let closed := !(t.hasFVar || t.hasExprMVar)
  replaceMainGoal [g]
  if closed then
    evalTactic (← `(tactic| (refine Sub.of_eq ?_; first | rfl | decide)))
  else
    -- Constants added one after another are first added up, so that a value
    -- moved down and back up is seen to be the value it was.
    evalTactic (← `(tactic|
      try simp only [BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceSignExtend,
        BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero]))
    evalTactic (← `(tactic| first
      | (with_reducible exact Sub.refl _)
      | (refine Sub.of_eq ?_; first | assumption | bv_omega)))

open Lean Meta Elab Tactic in
/-- Restates the goal with both types in their outermost form. Fails when
both are exactly known values, which `ty_sub_exact` owns. -/
elab "ty_sub_other" : tactic => do
  match ← headForm? (← getMainGoal) with
  | some (_, true) => throwError "two exactly known values"
  | some (g, false) => replaceMainGoal [g]
  | none => pure ()

macro_rules
  | `(tactic| ty_sub) =>
    `(tactic| first
      | ty_sub_exact
      | (ty_sub_other
         first
         | exact Sub.refl _
         | exact Sub.int _
         | exact Sub.readOnly _ _ _
         | exact Sub.refReadOnly _ _ _
         | exact Sub.null _
         | (refine Sub.nullableMono ?_; ty_sub)
         | (refine Sub.nullable ?_; ty_sub)
         | exact Sub.strLess _
         | (refine Sub.orErrMono ?_; ty_sub)
         | (refine Sub.orErr ?_; ty_sub)
         -- the stack pointer's type after moves that cancel or add up
         | (simp only [Ty.shift_shift]
            first | exact Sub.refl _ | (refine Sub.shift_congr ?_; decide))))

/-- Compares register types one register at a time. Registers it cannot
settle are left as goals. -/
macro "sub_regs" : tactic =>
  `(tactic| (intro r hr; cases r <;> first | exact absurd rfl hr | (try ty_sub)))

/-- Compares two pieces of the stack: the same, a typed value at a weaker
type, or what one holds forgotten. -/
macro "ty_subshape" : tactic =>
  `(tactic| focus first
    | exact SubShape.refl _
    | (refine SubShape.slot ?_; ty_sub)
    | exact SubShape.raw _
    -- each typed value wanted is found among those there, at a weaker type
    | (refine SubShape.mk rfl ?_
       repeat (first
         | (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩
            first
            | (refine ⟨_, List.mem_cons_self .., rfl, ?_⟩; ty_sub)
            | (refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, ?_⟩; ty_sub)
            | (refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
                rfl, ?_⟩; ty_sub)
            | (refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_self ..))), rfl, ?_⟩; ty_sub))
         | (intro _ h; cases h))
       done))

/-- Compares two stacks piece by piece. -/
macro "ty_stack" : tactic =>
  `(tactic| first
    | exact SubList.refl _
    | ((repeat (first
        | exact SubList.refl _
        | (refine SubList.cons ?_ ?_; ty_subshape))); done))

/-- Shows one flags predicate implies another, in the common cases. -/
macro "ty_flags" : tactic => do
  -- `rfl` must be written without macro hygiene, or `rintro` takes it for a name.
  let subst := Lean.mkIdent `rfl
  `(tactic| first
    | exact fun _ h => h
    | exact fun _ _ => trivial
    | (rintro f $subst:ident; exact Flags.ofResult_defined _ _ _))

open Lean Meta Elab Tactic in
/-- Proves `CtxSub Γ Δ` when `Δ` is still to be chosen, by choosing `Γ`: a
label that allows every context allows this one. -/
elab "ctx_same" : tactic => withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOfArity ``CtxSub 2 && t.appArg!.isMVar do
    throwError "the context to compare with is known"
  evalTactic (← `(tactic| exact CtxSub.refl _))

/-- Proves `CtxSub Γ Δ`. The stack, room and flags must be settled
automatically; register comparisons it cannot settle are left as goals. -/
macro "ctx_sub" : tactic =>
  `(tactic| first | ctx_same | (
    refine CtxSub.mk ?regs ?stack ?room ?flags ?sp ?owned
    case owned => rfl
    case stack => ty_stack
    case room => first | rfl | omega
    case flags => ty_flags
    case sp => ty_sub
    sub_regs))

/-- `ty_accept h` proves `Accepts Φ a Γ` by comparing `Γ` with a context `Δ`
that is allowed at `a`. The fact `h` is either `Φ a Δ` itself or, for a
labelled program, a statement that `Δ` is allowed at the label whose address
is `a`. Holes in `h` become goals. -/
macro "ty_accept " h:term : tactic =>
  `(tactic| ((first | refine ⟨_, $h, ?sub⟩ | refine ⟨_, CodeTy.ofLabels.intro $h, ?sub⟩);
             case' sub => ctx_sub))

/-! ## Typing instructions -/

/-- Proves a field lookup `fields[i]? = some τ`. -/
macro "ty_field" : tactic =>
  `(tactic| first
    | rfl
    | (refine getElem?_replicate_of_lt ?_
       first
         | assumption
         | omega
         | (simp; first | assumption | omega)
         | (simp [Scale.shift]; first | assumption | omega))
    -- a slot after the first of a list that goes on as a run of one type
    | (show (_ :: _)[_ + 1]? = _
       rw [List.getElem?_cons_succ]
       refine getElem?_replicate_of_lt ?_
       first | assumption | omega | (simp; first | assumption | omega))
    -- a slot after the first, in the first of two runs that follow it
    | (show (_ :: _)[_ + 1]? = _
       rw [List.getElem?_cons_succ,
         List.getElem?_append_left (by simp only [List.length_replicate]; omega)]
       refine getElem?_replicate_of_lt ?_
       first | assumption | omega | (simp; first | assumption | omega))
    | (simp [*]; done))

/-- Proves that an operation's need for the carry flag is met. -/
macro "ty_carry" : tactic => do
  let subst := Lean.mkIdent `rfl
  `(tactic| first
    | (intro h; exact absurd h (by decide))
    | exact fun _ _ hf => Flags.cf_isSome_of_known hf
    | (rintro - f $subst:ident; rfl))

/-- Proves that the flags decide a condition. -/
macro "ty_decided" : tactic => do
  let subst := Lean.mkIdent `rfl
  `(tactic| first
    | exact Cond.decided_of_known (fun _ h => h) _
    | (rintro f $subst:ident; exact ⟨_, rfl⟩)
    | (refine Cond.decided_of_defined _ ?_; decide))

/-- Proves that exactly known flags give a condition a particular answer. -/
macro "ty_cond_value" : tactic => do
  let subst := Lean.mkIdent `rfl
  `(tactic| (rintro f $subst:ident; rfl))

/-- Proves which byte a scaled index lands on. -/
macro "ty_index" : tactic =>
  `(tactic| first
    | (refine index8_slot _ _ ?_ ?_ <;> decide)
    | (refine index_bytes _ _ _ ?_; decide))

open Lean Meta Elab Tactic in
/-- Writes out a shape that the goal asks the size or the typed values of,
where it is named by a definition: `node.size` becomes the size of what
`node` is defined as. Fails if there is nothing to write out. -/
elab "ty_shape_open" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let fns := [``ShapeOf.size, ``ShapeOf.free, ``ShapeOf.valAt, ``ShapeOf.sole]
  let changed ← IO.mkRef false
  let target' ← Meta.transform target (pre := fun e => do
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConst && fns.contains f.constName! && args.size ≥ 2 then
      let S := args[1]!
      if S.isAppOf ``ShapeOf.mk || S.hasLooseBVars then return .continue
      let S' ← whnf S
      if S'.isAppOf ``ShapeOf.mk then
        changed.set true
        return .continue (mkAppN f (args.set! 1 S'))
    return .continue)
  unless ← changed.get do throwError "no shape to write out"
  replaceMainGoal [← goal.replaceTargetDefEq target']

/-! An array of `n` elements of one shape, reached three ways: through a
pointer stepped along it (`a * k + f`: element `k`, byte `f` of it), at a
fixed number of bytes from its start, and through an index scaled by the
element's size. -/

namespace ShapeOf

variable {S : Shape} {n a k f o i off m : Nat} {t : Ty}

theorem valAt_rep_elem (hf : S.fits = true) (ha : a = S.size) (hi : k < n)
    (hv : S.valAt f = some t) : (S.rep n).valAt (a * k + f) = some t := by
  subst ha; rw [Nat.mul_comm]; exact valAt_rep hf hi hv

theorem sole_rep_elem (hf : S.fits = true) (ha : a = S.size) (hi : k < n)
    (hin : f + 8 ≤ S.size) (hs : S.sole f = true) : (S.rep n).sole (a * k + f) = true := by
  subst ha; rw [Nat.mul_comm]; exact sole_rep hf hi hin hs

theorem free_rep_elem (hf : S.fits = true) (ha : a = S.size) (hi : k < n)
    (hin : f + m ≤ S.size) (hfree : S.free f m = true) :
    (S.rep n).free (a * k + f) m = true := by
  subst ha; rw [Nat.mul_comm]; exact free_rep hf hi hin hfree

theorem valAt_rep_at (hf : S.fits = true) (hi : o / S.size < n)
    (hv : S.valAt (o % S.size) = some t) : (S.rep n).valAt o = some t := by
  have := valAt_rep hf hi hv
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

theorem sole_rep_at (hf : S.fits = true) (hi : o / S.size < n)
    (hin : o % S.size + 8 ≤ S.size) (hs : S.sole (o % S.size) = true) :
    (S.rep n).sole o = true := by
  have := sole_rep hf hi hin hs
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

theorem free_rep_at (hf : S.fits = true) (hi : o / S.size < n)
    (hin : o % S.size + m ≤ S.size) (hfree : S.free (o % S.size) m = true) :
    (S.rep n).free o m = true := by
  have := free_rep hf hi hin hfree
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

theorem valAt_rep_idx (hf : S.fits = true) (h8 : S.size = 8) (hoff : off % 8 = 0)
    (hi : off / 8 + i < n) (hv : S.valAt 0 = some t) :
    (S.rep n).valAt (off + 8 * i) = some t := by
  have := valAt_rep hf hi hv
  rw [h8] at this
  rwa [show (off / 8 + i) * 8 + 0 = off + 8 * i by omega] at this

theorem sole_rep_idx (hf : S.fits = true) (h8 : S.size = 8) (hoff : off % 8 = 0)
    (hi : off / 8 + i < n) (hs : S.sole 0 = true) :
    (S.rep n).sole (off + 8 * i) = true := by
  have := sole_rep hf hi (f := 0) (by omega) hs
  rw [h8] at this
  rwa [show (off / 8 + i) * 8 + 0 = off + 8 * i by omega] at this

end ShapeOf

/-- Proves a premise about an element of an array: a bound on which element
it is, from the hypotheses, or a fact about the element's own shape, by
working it out. -/
macro "ty_elem" : tactic =>
  `(tactic| first
    | exact rfl
    | decide
    | assumption
    | omega
    | ((try ty_shape_open)
       simp only [ShapeOf.raw, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
         Nat.reduceSub, Nat.zero_add, Nat.add_zero, BitVec.reduceToNat, BitVec.toNat_ofNat,
         Nat.reducePow, List.cons_append, List.nil_append, stackOff_zero, stackOff_cons_succ,
         ShapeOf.slot_size, ShapeOf.raw_size]
       first | assumption | omega))

open Lean Meta Elab Tactic in
/-- Proves a premise about an element of an array if it is a proposition,
and passes over it if it is a value still to be found: another premise
settles that. -/
elab "ty_elem_goal" : tactic => do
  if ← isProp (← getMainTarget) then
    evalTactic (← `(tactic| ty_elem))

/-- Proves which typed value an array has at a place in one of its elements,
that it is the only one there, or that bytes of an element are plain. -/
macro "ty_val" : tactic =>
  `(tactic| first
    | (refine' ShapeOf.valAt_rep_elem ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.sole_rep_elem ?_ ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.free_rep_elem ?_ ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.valAt_rep_idx ?_ ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.sole_rep_idx ?_ ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.valAt_rep_at ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.sole_rep_at ?_ ?_ ?_ ?_ <;> ty_elem_goal)
    | (refine' ShapeOf.free_rep_at ?_ ?_ ?_ ?_ <;> ty_elem_goal))

/-- Proves a fact with no unknowns in it from the hypotheses: the fact
itself, or one side of an "or". A goal with unknowns is refused, since a
hypothesis of the right shape would settle them whether or not it was the
one meant. -/
syntax "ty_known" : tactic

/-- Proves a side condition of a typing rule, or fails. -/
syntax "ty_side" : tactic

/-- Applies one typing rule and proves all its premises, or fails. The
premises are attempted in order and then again, because proving one can
determine what an earlier one refers to. -/
syntax "ty_rule " term : tactic

/-- Like `ty_rule`, but proves the premises strictly in order and gives up
at the first that fails. For rules whose first premise computes what the
others refer to, where carrying on after a failure would be slow. -/
syntax "ty_rule_ordered " term : tactic

/-- Proves that an operand can be read, can be written, or holds a value of
a given type: it is a register, a stack slot, a field of a pointer, or a field
of a block at a fixed address. -/
macro "ty_operand" : tactic =>
  `(tactic| first
    | ty_rule_ordered ReadOk.reg | ty_rule_ordered ReadOk.slot | ty_rule_ordered ReadOk.slotIndexed
    | ty_rule_ordered ReadOk.field
    | ty_rule_ordered ReadOk.owned | ty_rule_ordered WriteIntOk.owned
    | ty_rule_ordered ReadOk.ownedAt | ty_rule_ordered WriteIntOk.ownedAt
    | ty_rule_ordered WriteIntOk.ownedClear
    | ty_rule_ordered ReadOk.indexed | ty_rule_ordered ReadOk.global_of
    | ty_rule_ordered WriteIntOk.reg | ty_rule_ordered WriteIntOk.slot
    | ty_rule_ordered WriteIntOk.slotIndexed
    | ty_rule_ordered WriteIntOk.field | ty_rule_ordered WriteIntOk.indexed
    | ty_rule_ordered WriteIntOk.global_of
    | ty_rule_ordered Holds.reg | ty_rule_ordered Holds.slot | ty_rule_ordered Holds.field
    | ty_rule_ordered Holds.indexed | ty_rule_ordered Holds.global_of)

/-- Shows that a known offset falls inside a block of known length. -/
macro "ty_inside" : tactic =>
  `(tactic| first
    | decide
    | (simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
         ShapeOf.append, ShapeOf.rep_size,
         List.length_replicate, List.length_set, List.length_cons, List.length_nil,
         List.length_take, List.length_drop, List.length_append]
       first | decide | omega))

/-- Proves that an address is some bytes into an owned block: the block is
looked for among the first few the context lists, and is the one the address
falls inside. The address may be written from the block's own start or from
that of a block next to it, as it is or with a known amount added. -/
syntax "ty_owned_at" : tactic

/-- A block's own address is that of its first byte. -/
theorem owned_addr0 (a : BitVec 64) : a = a + BitVec.ofNat 64 0 := by simp

/-- An address a known number of bytes into a block. -/
theorem owned_addrOff (a d : BitVec 64) : a + d = a + BitVec.ofNat 64 d.toNat := by simp

/-- The address reached through an index with any scale, as a number of
bytes from the base. -/
theorem owned_addrScaled (a c : BitVec 64) (sc : Scale) (disp : BitVec 32)
    (hd : disp.toNat < 2 ^ 31) :
    a + (c <<< sc.shift) + disp.signExtend 64
      = a + BitVec.ofNat 64 (c.toNat * 2 ^ sc.shift + disp.toNat) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize c.toNat * 2 ^ sc.shift = m
  omega

/-- Proves which byte of an owned block an address reached through an index
is that of. -/
syntax "ty_owned_byte" : tactic

/-- Proves which piece of the stack a byte above the stack pointer is in, and
which byte of the piece: the pieces the context lists are tried from the top. -/
syntax "ty_stack_at" : tactic

/-- Shows a fact about where a piece of the stack starts and how long it
is: that a byte or a run of bytes is inside it, say. -/
macro "ty_stack_in" : tactic =>
  `(tactic| first
    | decide
    | omega
    | (simp only [List.cons_append, List.nil_append, ShapeOf.rep_size, ShapeOf.slot_size,
         ShapeOf.raw_size, stackOff_zero,
         stackOff_cons_succ, Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat,
         BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
         Nat.reduceSub, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.pow_zero]
       first | omega | decide)
    | (simp only [List.cons_append, List.nil_append, ShapeOf.rep_size, ShapeOf.slot_size,
         ShapeOf.raw_size, stackOff_zero,
         stackOff_cons_succ, Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat,
         BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
         Nat.reduceSub, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.pow_zero,
         Nat.le_refl]
       done))

open Lean Meta Elab Tactic in
/-- Fails unless the goal is a proposition. A rule's unknowns are goals too,
and a side-condition tactic let loose on one of them would fill it with
whatever of the right type lies nearest. -/
elab "ty_prop_only" : tactic => do
  unless ← isProp (← getMainTarget) do
    throwError "not a proposition"

macro_rules
  | `(tactic| ty_side) =>
    `(tactic| ty_prop_only; first
      -- which byte an index lands on, before anything else: left to `rfl`,
      -- the byte would be found as an unevaluated sum of the two addresses
      | ty_index
      -- not the `rfl` tactic: on an inequality it would compare the two sides
      -- as if for equality, working both out in full, before giving up
      | exact rfl
      | decide
      | exact EaIs.base (by decide) rfl
      | exact EaIs.indexed (by decide) rfl rfl
      | ty_owned_at
      | ty_owned_byte
      | ty_stack_at
      -- a bound against the length of a long list, without counting it out
      | (simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
           ShapeOf.append, ShapeOf.rep_size,
           List.length_replicate, List.length_set, List.length_cons, List.length_nil]
         first | decide | omega)
      -- a bound on a byte reached through an index, from a bound on the index
      | (simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
           ShapeOf.append, ShapeOf.rep_size,
           List.length_replicate, List.length_set, List.length_cons, List.length_nil,
           Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow,
           Nat.reduceMod,
           Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.pow_zero]
         omega)
      -- the same, against a shape named by a definition
      | (ty_shape_open
         simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
           ShapeOf.append, ShapeOf.rep_size,
           List.length_replicate, List.length_set, List.length_cons, List.length_nil,
           Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat, BitVec.reduceToNat,
           Nat.reducePow, Nat.reduceMod,
           Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.pow_zero]
         omega)
      -- bytes reached through an index keep clear of each typed value of the
      -- block, from a bound on the index
      | ((try ty_shape_open)
         simp only [ShapeOf.free, ShapeOf.clearOf, List.all_cons, List.all_nil, Bool.and_true,
           Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
           Scale.shift, NarrowW.bytes, Width.bytes, BitVec.toNat_ofNat, BitVec.reduceToNat,
           Nat.reducePow, Nat.reduceMod,
           Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_one, Nat.add_zero, Nat.pow_zero]
         omega)
      | (refine byteDisp_of _ ?_; decide)
      | ty_stack_in
      | ty_val
      | ty_field
      | ty_sub
      | ty_carry
      | ty_decided
      | ty_cond_value
      | ty_known
      | ty_operand)

macro_rules
  | `(tactic| ty_rule $r) =>
    `(tactic| (((refine' $r .. <;> try ty_side) <;> try ty_side); done))

/-- A pointer stepped one element past element `b` of elements `a` bytes
long is at element `b + 1`: the form a loop's invariant is stated in. -/
theorem elem_succ (a b : Nat) : a * b + a = a * (b + 1) := rfl

open Lean Meta Simp in
/-- Decides a test of whether one named register is another, and takes the
branch. Looking a register up in a context leaves such tests behind. -/
dsimproc_decl regIte (ite (@Eq Reg _ _) _ _) := fun e => do
  let_expr ite _ c _ a b := e | return .continue
  let_expr Eq _ x y := c | return .continue
  let .const nx _ := x | return .continue
  let .const ny _ := y | return .continue
  unless (← isConstructorApp x) && (← isConstructorApp y) do return .continue
  return .visit (if nx == ny then a else b)

/-- Simplifies the context in a block goal, without changing its shape. Each
rule wraps the previous context in a record update that mentions it once per
field, so without this the context would multiply in size with every
instruction. -/
macro "ty_dsimp_ctx" : tactic =>
  `(tactic| try dsimp only [↓regIte, RegMap.get, entryCtx, entryCtxArgs,
      CtxOf.setReg, CtxOf.moveSp, Ty.shift, CtxOf.afterAlu, CtxOf.afterSyscall,
      CtxOf.afterMulDiv,
      ShiftOp.apply, Scale.shift,
      ShiftOp.flagsAfter, Width.bits, Nat.reduceEqDiff, Nat.reduceBEq, ↓reduceIte,
      AluOp.writesDst, List.set_cons_zero, List.set_cons_succ, List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ, List.cons_append, List.nil_append, List.length_cons,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      stackOff_zero, stackOff_cons_succ, ShapeOf.slot_size, ShapeOf.raw_size,
      List.length_nil, List.drop_zero,
      Bool.cond_true, Bool.cond_false, Nat.add_zero, Nat.zero_add, BitVec.reduceToNat, Nat.reduceDiv,
      elem_succ,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub,
      BitVec.reduceSetWidth, BitVec.reduceSignExtend, BitVec.reduceAdd, BitVec.reduceSub,
      BitVec.reduceNeg, BitVec.reduceOfNat])

/-- Brings a block goal to the form it is kept in between instructions: the
address as a number, the register types as a table, and everything in the
context that can be worked out, worked out. A goal of another kind has its
context simplified. -/
syntax "ty_normalize" : tactic

/-- `ty_name r as v`: from here on, the value in register `r` is called `v`
and the register is typed as exactly `v`. Use it on a register typed as an
integer, for example one just loaded from memory, before testing it or
computing with it, so that what is learnt about the value can be used. -/
syntax "ty_name " term " as " ident : tactic

syntax "ty_name_slot " term " as " ident : tactic
syntax "ty_stack_split " "at " term : tactic
syntax "ty_stack_join " "at " term : tactic
syntax "ty_open " term : tactic
syntax "ty_null " term : tactic
syntax "ty_err " term " as " ident : tactic
syntax "ty_mmap " term : tactic
syntax "ty_mmap_kind " term : tactic
syntax "ty_into " term : tactic
syntax "ty_byte " "as " ident : tactic
syntax "ty_mmap_own " "as " ident : tactic
syntax "ty_munmap" : tactic
syntax "ty_freeze " term : tactic
syntax "ty_freeze_kind " term " as " term : tactic
syntax "ty_split " term " at " term : tactic
syntax "ty_join " term : tactic
syntax "ty_own_first " term : tactic

/-! ## Choosing the rule from the instruction

The tactics below are metaprograms. They look at the instruction, try only
the rules written for its shape, and when none applies they say which
premise of each stood in the way. -/

open Lean Meta Elab Tactic

elab_rules : tactic
  | `(tactic| ty_known) => withMainContext do
    let ty ← instantiateMVars (← (← getMainGoal).getType)
    if ty.hasExprMVar then throwError "ty_known: the goal has unknowns"
    -- A goal that asks for a value, not a fact, is never settled this way.
    unless ← isProp ty do throwError "ty_known: the goal is not a proposition"
    evalTactic (← `(tactic| first
      | assumption
      | (refine Or.inl ?_; first | assumption | decide)
      | (refine Or.inr ?_; first | assumption | decide)))

elab_rules : tactic
  | `(tactic| ty_rule_ordered $r) => Tactic.withoutRecover do
    evalTactic (← `(tactic| refine' $r ..))
    for g in ← getGoals do
      if ← g.isAssigned then continue
      unless ← isProp (← g.getType) do continue
      setGoals [g]
      evalTactic (← `(tactic| ty_side))
      unless (← getUnsolvedGoals).isEmpty do throwError "premise not proved"
    setGoals []

/-- Gives the value in a register a name, on the main goal, which must be a block. -/
def nameRegister (r : Term) (v : Ident) : TacticM Unit := do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  setGoals [goal]
  -- the stack pointer has a rule of its own
  let saved ← saveState
  let rest? ← try
      evalTactic (← `(tactic| refine BlockOk.name (r := $r) ?_ ?_))
      let mut rest? : Option MVarId := none
      for g in ← getGoals do
        let t ← instantiateMVars (← g.getType)
        if t.isAppOf ``Ne then
          setGoals [g]
          evalTactic (← `(tactic| decide))
        else rest? := some g
      pure rest?
    catch _ =>
      saved.restore
      setGoals [goal]
      evalTactic (← `(tactic| refine BlockOk.nameSp (Γ := ?_) ?_))
      pure (← getGoals).head?
  let some rest := rest? | throwError "ty_name: unexpected goals"
  setGoals [rest]
  evalTactic (← `(tactic| (intro $v:ident; ty_normalize)))
  setGoals ((← getGoals) ++ others)

elab_rules : tactic
  | `(tactic| ty_name $r as $v) => nameRegister r v

/-- Applies a rule that turns the main block goal into one or more block
goals, proving its side condition that a register is not `rsp`. The new
block goals come back simplified and in order. -/
def refineBlocks (tac : TSyntax `tactic) : TacticM Unit := do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  setGoals [goal]
  evalTactic tac
  let mut blocks : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then
      setGoals [g]
      evalTactic (← `(tactic| ty_normalize))
      blocks := blocks ++ (← getGoals)
    else
      setGoals [g]
      evalTactic (← `(tactic| decide))
  setGoals (blocks ++ others)

/-- `ty_open r`: register `r` holds a pointer to a block of some kind. From
here on `r` is an ordinary pointer to a block of the shape the memory typing
lists for that kind, which can be loaded from and stored to. -/
elab_rules : tactic
  | `(tactic| ty_open $r) => do
    refineBlocks (← `(tactic| refine BlockOk.openRef (r := $r) ?_ rfl rfl ?_))

/-- `ty_null r`: register `r` holds a value that may be null. Two goals
follow: the rest of the block with `r` exactly zero, then with `r` a value
of the type itself. A test of `r` then decides in each which way it goes. -/
elab_rules : tactic
  | `(tactic| ty_null $r) => do
    refineBlocks (← `(tactic| refine BlockOk.splitNull (r := $r) ?_ rfl ?_ ?_))

/-- `ty_err r as e`: register `r` holds what a system call handed back, an
error number or a value. Two goals follow: the rest of the block with `r`
exactly an error number `e`, then with `r` a value of the type itself. A
test of `r` then decides in the first which way it goes. -/
elab_rules : tactic
  | `(tactic| ty_err $r as $e) => do
    let goal ← getMainGoal
    let others := (← getGoals).drop 1
    setGoals [goal]
    evalTactic (← `(tactic| refine BlockOk.splitErr (r := $r) ?_ rfl ?_ ?_))
    let mut blocks : List MVarId := []
    for g in ← getGoals do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      setGoals [g]
      if t.isAppOf ``BlockOk then
        evalTactic (← `(tactic| ty_normalize))
        blocks := blocks ++ (← getGoals)
      else if t.isForall then
        evalTactic (← `(tactic| (intro $e:ident herr; ty_normalize)))
        blocks := blocks ++ (← getGoals)
      else
        evalTactic (← `(tactic| decide))
    setGoals (blocks ++ others)

/-- The rules whose premises are proved in order, stopping at the first that
fails: those for operands, whose premises each depend on the ones before. -/
def orderedRules : List Name := [``Straight.loadGlobal_of, ``Straight.storeGlobal_of,
  ``ReadOk.reg, ``ReadOk.slot, ``ReadOk.slotIndexed, ``ReadOk.field, ``ReadOk.indexed,
  ``ReadOk.global_of, ``ReadOk.text, ``ReadOk.owned, ``WriteIntOk.owned,
  ``WriteIntOk.reg, ``WriteIntOk.slot, ``WriteIntOk.slotIndexed, ``WriteIntOk.field,
  ``WriteIntOk.indexed, ``WriteIntOk.global_of, ``Holds.reg, ``Holds.slot, ``Holds.field, ``Holds.indexed,
  ``Holds.global_of]

/-- The straight-line rules that can type an instruction of this shape, most
informative first. An empty list means the type system has no rule for it. -/
def Instr.rules : Instr → List Name
  | .nop => [``Straight.nop]
  -- moves between registers and constants
  | .mov .w64 (.rm_r (.reg _) _) => [``Straight.movRR64]
  | .mov .w32 (.rm_r (.reg _) _) => [``Straight.mov32Exact, ``Straight.movRR32]
  | .mov _ (.rm_i (.reg _) _) => [``Straight.movRI]
  | .movAbs _ _ => [``Straight.movAbs]
  | .lea .w64 _ (.rip _) => [``Straight.leaRip, ``Straight.lea]
  | .lea .w64 _ (.sib (some .rsp) none _) => [``Straight.leaSp, ``Straight.lea]
  | .lea .w64 _ (.sib (some _) none _) => [``Straight.leaExactB, ``Straight.lea]
  | .lea .w64 _ (.sib (some _) (some _) _) => [``Straight.leaExactBI, ``Straight.lea]
  | .lea _ _ _ => [``Straight.lea]
  -- loads: a whole slot or field keeps its type, anything else is an integer
  | .mov .w64 (.r_m _ (.sib (some .rsp) none _)) => [``Straight.loadStack, ``Straight.loadInt]
  | .mov .w64 (.r_m _ (.sib (some _) none _)) =>
    [``Straight.loadField, ``Straight.loadOwned, ``Straight.loadInt]
  | .mov .w64 (.r_m _ (.rip _)) => [``Straight.loadGlobal_of, ``Straight.loadInt]
  | .mov .w64 (.r_m _ (.sib (some .rsp) (some _) _)) =>
    [``Straight.loadStackIndexed, ``Straight.loadInt]
  | .mov .w64 (.r_m _ (.sib (some _) (some _) _)) =>
    [``Straight.loadIndexed, ``Straight.loadOwned, ``Straight.loadInt]
  | .mov _ (.r_m _ _) => [``Straight.loadInt]
  | .movzx _ _ _ (.reg _) => [``Straight.movzxExact, ``Straight.movzxRM]
  | .movzx _ _ _ _ => [``Straight.movzxRM]
  | .movsx _ _ _ (.reg _) => [``Straight.movsxExact, ``Straight.movsxRM]
  | .movsx _ _ _ _ => [``Straight.movsxRM]
  | .movsxd _ (.reg _) => [``Straight.movsxdExact, ``Straight.movsxdRM]
  | .movsxd _ _ => [``Straight.movsxdRM]
  -- stores
  | .mov .w64 (.rm_r (.mem (.sib (some .rsp) none _)) _) => [``Straight.storeStack]
  | .mov .w64 (.rm_r (.mem (.sib (some _) none _)) _) =>
    [``Straight.storeField, ``Straight.storeOwnedKeep, ``Straight.storeOwnedTyped,
      ``Straight.storeInt]
  | .mov .w64 (.rm_r (.mem (.rip _)) _) => [``Straight.storeGlobal_of, ``Straight.storeInt]
  | .mov .w64 (.rm_r (.mem (.sib (some _) (some _) _)) _) =>
    [``Straight.storeIndexed, ``Straight.storeOwnedKeep, ``Straight.storeOwnedTyped,
      ``Straight.storeInt]
  | .mov _ (.rm_r (.mem _) _) => [``Straight.storeInt]
  | .mov _ (.rm_i (.mem _) _) => [``Straight.storeImm]
  | .store8 _ _ => [``Straight.store8RM]
  | .store16 _ _ => [``Straight.store16RM]
  | .push _ => [``Straight.push]
  | .pop _ => [``Straight.pop, ``Straight.popPlain]
  -- arithmetic
  | .alu .sub .w64 (.rm_i (.reg .rsp) _) => [``Straight.allocFrame]
  | .alu .add .w64 (.rm_i (.reg .rsp) _) => [``Straight.freeFrame']
  | .alu _ .w64 (.rm_i (.reg _) _) =>
    [``Straight.aluExact, ``Straight.addPtr, ``Straight.strNext, ``Straight.aluRI]
  | .alu _ _ (.rm_i (.reg _) _) => [``Straight.aluExact32, ``Straight.aluRI]
  | .alu .xor w (.rm_r (.reg d) s) =>
    -- `xor r, r` clears `r` whatever it held
    if d = s then [``Straight.xorSelf]
    else match w with
      | .w64 => [``Straight.aluExactRR, ``Straight.aluRR]
      | .w32 => [``Straight.aluExactRR32, ``Straight.aluRR]
  | .alu _ .w64 (.rm_r (.reg _) _) => [``Straight.aluExactRR, ``Straight.aluRR]
  | .alu _ _ (.rm_r (.reg _) _) => [``Straight.aluExactRR32, ``Straight.aluRR]
  | .alu _ _ (.r_m _ _) => [``Straight.aluLoad]
  | .alu op _ (.rm_r (.mem _) _) =>
    if op.writesDst then [``Straight.aluStoreR] else [``Straight.cmpR]
  | .alu op _ (.rm_i (.mem _) _) =>
    if op.writesDst then [``Straight.aluStoreI] else [``Straight.cmpI]
  | .test .w64 (.reg _) (.reg _) => [``Straight.testExact, ``Straight.testRM]
  | .test _ _ _ => [``Straight.testRM]
  | .unary .neg _ (.reg _) => [``Straight.negExact, ``Straight.negRM]
  | .unary .neg _ _ => [``Straight.negRM]
  | .unary .not _ (.reg _) => [``Straight.notExact, ``Straight.notRM]
  | .unary .not _ _ => [``Straight.notRM]
  | .shift _ _ (.reg _) (.imm _) => [``Straight.shiftExact, ``Straight.shiftImm]
  | .shift _ _ _ (.imm _) => [``Straight.shiftImm]
  | .shift _ _ _ .cl => [``Straight.shiftCl]
  | .mulDiv .mul _ (.reg _) => [``Straight.mulDivExact, ``Straight.mulRM]
  | .mulDiv .mul _ _ => [``Straight.mulRM]
  | .mulDiv .imul _ (.reg _) => [``Straight.mulDivExact, ``Straight.imulRM]
  | .mulDiv .imul _ _ => [``Straight.imulRM]
  -- a divide is typed only when shown not to raise a divide error
  | .mulDiv .div _ (.reg _) => [``Straight.mulDivExact, ``Straight.divSafe]
  | .mulDiv .idiv _ (.reg _) => [``Straight.mulDivExact, ``Straight.idivSafe]
  | .imul2 _ _ (.reg _) => [``Straight.imul2Exact, ``Straight.imul2RM]
  | .imul2 _ _ _ => [``Straight.imul2RM]
  | .imul3 _ _ (.reg _) _ => [``Straight.imul3Exact, ``Straight.imul3RM]
  | .imul3 _ _ _ _ => [``Straight.imul3RM]
  | .popcnt _ _ (.reg _) => [``Straight.popcntExact, ``Straight.popcntRM]
  | .popcnt _ _ _ => [``Straight.popcntRM]
  | .bswap _ _ => [``Straight.bswapExact, ``Straight.bswap]
  | .cdq => [``Straight.cdqExact, ``Straight.cdq]
  | .cqo => [``Straight.cqoExact, ``Straight.cqo]
  | .cmov _ _ _ (.reg _) => [``Straight.cmovExact, ``Straight.cmovRM]
  | .cmov _ _ _ _ => [``Straight.cmovRM]
  | .setcc _ (.reg _) => [``Straight.setccExact, ``Straight.setccRM]
  | .setcc _ _ => [``Straight.setccRM]
  -- control transfers end a block and are not typed by a straight-line rule
  | _ => []

/-- Rules that only sharpen what a more general rule for the same
instruction already gives: they apply when values are exactly known. When an
instruction cannot be typed, why one of these did not apply is not reported,
since the general rule's reason is the one that matters. -/
def sharpeningRules : List Name := [``Straight.leaSp, ``Straight.mov32Exact, ``Straight.aluExact32,
  ``Straight.aluExactRR32, ``Straight.shiftExact, ``Straight.leaExactB, ``Straight.leaExactBI,
  ``Straight.negExact, ``Straight.notExact, ``Straight.imul2Exact, ``Straight.imul3Exact,
  ``Straight.mulDivExact, ``Straight.cdqExact, ``Straight.cqoExact,
  ``Straight.movsxdExact, ``Straight.movzxExact, ``Straight.movsxExact, ``Straight.popcntExact,
  ``Straight.bswapExact, ``Straight.cmovExact, ``Straight.setccExact]

/-- Why an instruction form has no rule, where there is something more
useful to say than that. -/
def Instr.noRuleReason : Instr → Option String
  | .mulDiv .div _ (.mem _) | .mulDiv .idiv _ (.mem _) =>
    some "a divide is typed only when its divisor is shown not to be zero, and values in \
      memory are not tracked: load the divisor into a register first"
  | _ => none

/-- The registers whose values an instruction's rules need to speak of. If
one of them is typed as an integer, the tactic gives its value a name first,
so that the rules for exactly known values apply. -/
def Instr.wantsNamed : Instr → List Reg
  | .mulDiv .div _ (.reg r) | .mulDiv .idiv _ (.reg r) => [.rax, .rdx, r]
  | .cqo | .cdq => [.rax]
  | _ => []

/-- Whether the instruction can send control somewhere other than the next
instruction, which is where a block ends. -/
def Instr.endsBlock : Instr → Bool
  | .jmp _ | .jcc _ _ | .call _ | .ret | .syscall | .ud2 => true
  | _ => false

/-- Every straight-line rule, for instructions whose shape is not known. -/
def allStraightRules : List Name := sharpeningRules ++ [``Straight.movRR64, ``Straight.movRR32, ``Straight.movRI, ``Straight.movAbs, ``Straight.leaRip, ``Straight.lea, ``Straight.loadStack, ``Straight.loadField, ``Straight.storeStack, ``Straight.storeField, ``Straight.push, ``Straight.pop, ``Straight.allocFrame, ``Straight.freeFrame', ``Straight.aluExact, ``Straight.aluExactRR, ``Straight.addPtr, ``Straight.aluRR, ``Straight.aluRI, ``Straight.testExact, ``Straight.nop, ``Straight.aluStoreR, ``Straight.aluStoreI, ``Straight.cmpR, ``Straight.cmpI, ``Straight.aluLoad, ``Straight.testRM, ``Straight.negRM, ``Straight.notRM, ``Straight.shiftImm, ``Straight.shiftCl, ``Straight.mulRM, ``Straight.imulRM, ``Straight.divSafe, ``Straight.idivSafe, ``Straight.imul2RM, ``Straight.imul3RM, ``Straight.popcntRM, ``Straight.bswap, ``Straight.cdq, ``Straight.cqo, ``Straight.movsxdRM, ``Straight.cmovRM, ``Straight.setccRM, ``Straight.movzxRM, ``Straight.movsxRM, ``Straight.loadInt, ``Straight.storeInt, ``Straight.storeImm, ``Straight.store8RM, ``Straight.store16RM, ``Straight.loadGlobal_of, ``Straight.storeGlobal_of, ``Straight.xorSelf,
  ``Straight.loadIndexed, ``Straight.storeIndexed, ``Straight.loadStackIndexed,
  ``Straight.loadOwned, ``Straight.storeOwnedTyped, ``Straight.storeOwnedKeep]

private unsafe def evalInstrUnsafe (e : Expr) : MetaM Instr :=
  evalExpr Instr (mkConst ``Instr) e

private unsafe def evalAddrUnsafe (e : Expr) : MetaM Nat := do
  let v ← evalExpr (BitVec 64) (mkApp (mkConst ``BitVec) (mkNatLit 64)) e
  return v.toNat

/-- The number a closed address term denotes. -/
@[implemented_by evalAddrUnsafe]
private opaque evalAddr (e : Expr) : MetaM Nat

deriving instance ToExpr for Reg
deriving instance ToExpr for Width
deriving instance ToExpr for NarrowW
deriving instance ToExpr for Cond
deriving instance ToExpr for Scale
deriving instance ToExpr for IndexReg
deriving instance ToExpr for Mem
deriving instance ToExpr for RM
deriving instance ToExpr for Operands
deriving instance ToExpr for RI
deriving instance ToExpr for AluOp
deriving instance ToExpr for UnOp
deriving instance ToExpr for ShiftOp
deriving instance ToExpr for MulDivOp
deriving instance ToExpr for Count
deriving instance ToExpr for Target
deriving instance ToExpr for Instr

private unsafe def evalFetchUnsafe (e : Expr) : MetaM (Option (Instr × BitVec 64)) := do
  evalExpr (Option (Instr × BitVec 64)) (← inferType e) e

/-- What a closed lookup of an instruction comes to. -/
@[implemented_by evalFetchUnsafe]
private opaque evalFetch (e : Expr) : MetaM (Option (Instr × BitVec 64))

private unsafe def evalTableUnsafe (e : Expr) : MetaM (List (Nat × Instr × BitVec 64)) := do
  evalExpr (List (Nat × Instr × BitVec 64)) (← inferType e) e

/-- The instructions, each with its address, that a closed table comes to. -/
@[implemented_by evalTableUnsafe]
private opaque evalTable (e : Expr) : MetaM (List (Nat × Instr × BitVec 64))

deriving instance ToExpr for Lookup

instance : Inhabited Lookup := ⟨.none⟩

/-- A balanced search tree over instructions listed with their addresses. -/
private partial def lookupTree (xs : Array (Nat × Instr × BitVec 64)) (lo hi : Nat) : Lookup :=
  if hi ≤ lo then .none
  else if hi = lo + 1 then
    match xs[lo]? with
    | some (a, i, len) => .leaf a i len
    | none => .none
  else
    let m := (lo + hi) / 2
    .node (lookupTree xs lo m) ((xs[m]?.map (·.1)).getD 0) (lookupTree xs m hi)

/-- For each program's instruction table met so far: its instructions with
their addresses, as the program gives them, and its search tree written out. -/
initialize layoutCache : IO.Ref (Std.HashMap Expr (Expr × Expr)) ← IO.mkRef {}

/-- A program's instruction table as a function that searches a tree written
out in full, with a proof that the table is that function. The proof is
`Lookup.sound`, whose premises the kernel settles by computing once for the
program; it is kept as a lemma of its own, and every lookup afterwards is a
few comparisons of numbers. -/
private def layoutOf (fetch : Expr) : MetaM (Option (Expr × Expr)) := do
  let (table, tree) ← do
    if let some r := (← layoutCache.get)[fetch]? then pure r
    else
      -- unfold to `Asm.fetch base prog`, a walk along `Asm.table base prog`
      let mut f := fetch
      for _ in [0:8] do
        if f.isAppOf ``Asm.fetch then break
        let some f' ← unfoldDefinition? f | return none
        f := f'.headBeta
      unless f.isAppOfArity ``Asm.fetch 4 do return none
      let table ← mkAppM ``Asm.table #[f.appFn!.appArg!, f.appArg!]
      let listed ← try pure (← evalTable table).toArray catch _ => return none
      let r := (table, toExpr (lookupTree listed 0 listed.size))
      layoutCache.modify (·.insert fetch r)
      pure r
  let a := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let found ← withLocalDeclD `a a fun x => do
    mkLambdaFVars #[x] (mkApp2 (mkConst ``Lookup.find) tree (← mkAppM ``BitVec.toNat #[x]))
  let type ← mkEq fetch found
  let rflTrue ← mkEqRefl (mkConst ``Bool.true)
  let value := mkAppN (mkConst ``Lookup.sound)
    #[table, tree, rflTrue, ← mkEqRefl (mkApp (mkConst ``Lookup.toList) tree)]
  let name ← mkAuxLemma [] type (← mkExpectedTypeHint value type)
  return some (found, mkConst name)

/-- `ty_fetch` proves `fetch a = some (i, len)` for a known program and
address by running the lookup, and fills in whatever of `i` and `len` is
unknown with what it found, written out in full. The proof is by `rfl`, but
it is the kernel alone that checks it: found by unifying, the instruction
would be an unevaluated term that walks the whole program again each time it
is looked at. -/
elab "ty_fetch" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := t.consumeMData.eq? | throwError "ty_fetch: not an equation"
  if lhs.hasFVar || lhs.hasMVar then
    evalTactic (← `(tactic| rfl))
    return
  let v? ← try pure (some (← evalFetch lhs)) catch _ => pure none
  let some v := v? | do
    evalTactic (← `(tactic| rfl))
    return
  let some (i, len) := v | throwError "there is no instruction at this address"
  let found := toExpr (some (i, len))
  unless ← isDefEq rhs found do
    throwError "the instruction at this address is{indentExpr (toExpr i)}"
  let direct ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs found)
  let proof ←
    if lhs.isApp then
      match ← layoutOf lhs.appFn! with
      | some (table, h) =>
        let walked := mkApp table lhs.appArg!
        mkEqTrans (← mkCongrFun h lhs.appArg!)
          (← mkExpectedTypeHint (← mkEqRefl walked) (← mkEq walked found))
      | none => pure direct
    else pure direct
  g.assign proof
  replaceMainGoal []

/-- Whether a term is an address written as a number. -/
private def isAddrLit (e : Expr) : Bool :=
  e.isAppOfArity ``BitVec.ofNat 2 && e.appArg!.nat?.isSome

/-- A list with its spine worked out: each tail brought to the form of an
element followed by a list, as far as that goes, and a number of elements
dropped from an unknown list written as a number. -/
private partial def normList (e : Expr) : MetaM Expr := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    return mkApp3 e.appFn!.appFn!.appFn! e.appFn!.appFn!.appArg! e.appFn!.appArg!
      (← normList e.appArg!)
  if e.isAppOfArity ``List.drop 3 then
    let n := e.appFn!.appArg!
    if n.nat?.isNone then
      let n' ← whnf n
      if let some k := n'.nat? then
        return mkApp2 e.appFn!.appFn! (mkNatLit k) e.appArg!
  return e

/-- A number written out, if the term is one that can be worked out. -/
private def natOf (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.nat? then return some n
  if e.hasMVar then return none
  let v ← whnf e
  match v with
  | .lit (.natVal n) => return some n
  | _ => return v.nat?

/-- The elements of a list term, as far as its spine is written out, and
whether that is all of it. -/
private partial def consElems (e : Expr) : MetaM (Array Expr × Bool) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    let (rest, whole) ← consElems e.appArg!
    return (#[e.appFn!.appArg!] ++ rest, whole)
  return (#[], e.isAppOfArity ``List.nil 1)

/-- A block's shape with its size and its typed values worked out: the form
it is kept in after a split, a join or a store has been applied to it. -/
private def normShape (S : Expr) : MetaM Expr := do
  let S' ← whnf S
  unless S'.isAppOfArity ``ShapeOf.mk 3 do return S
  let τ := S'.appFn!.appFn!.appArg!
  let size ← match ← natOf S'.appFn!.appArg! with
    | some n => pure (mkNatLit n)
    | none => pure S'.appFn!.appArg!
  let (elems, whole) ← consElems S'.appArg!
  unless whole do return mkApp3 (S'.getAppFn) τ size S'.appArg!
  let mut out : Array Expr := #[]
  for p in elems do
    let p' ← whnf p
    if p'.isAppOfArity ``Prod.mk 4 then
      let o ← match ← natOf p'.appFn!.appArg! with
        | some n => pure (mkNatLit n)
        | none => pure p'.appFn!.appArg!
      out := out.push (mkApp2 p'.appFn!.appFn! o p'.appArg!)
    else out := out.push p
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, τ]
  return mkApp3 (S'.getAppFn) τ size (← mkListLit pairTy out.toList)

/-- A list of owned blocks with its spine and each block's shape worked out. -/
private partial def normOwned (e : Expr) : MetaM Expr := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    let hd := e.appFn!.appArg!
    let hd' ← whnf hd
    let hd'' ← if hd'.isAppOfArity ``Prod.mk 4 then
        pure (mkApp hd'.appFn! (← normShape hd'.appArg!))
      else pure hd
    return mkApp3 e.appFn!.appFn!.appFn! e.appFn!.appFn!.appArg! hd'' (← normOwned e.appArg!)
  normList e

/-- The stack with each piece that an instruction has just changed worked
out, as far as its spine is written out: eight bytes holding one typed value
are written as a slot, bytes holding none as plain bytes. -/
private partial def normStack (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  unless e'.isAppOfArity ``List.cons 3 do return e
  let hd := e'.appFn!.appArg!
  let keep := hd.isAppOf ``ShapeOf.slot || hd.isAppOf ``ShapeOf.raw || hd.isAppOf ``ShapeOf.rep
    || hd.isFVar
  let hd' ← if keep then pure hd else do
    let S ← normShape hd
    if S.isAppOfArity ``ShapeOf.mk 3 then
      let τ := S.appFn!.appFn!.appArg!
      let size := S.appFn!.appArg!
      let (elems, whole) ← consElems S.appArg!
      if whole && elems.size == 0 then pure (mkApp2 (mkConst ``ShapeOf.raw) τ size)
      else if whole && elems.size == 1 then
        let p := elems[0]!
        if p.isAppOfArity ``Prod.mk 4 && size.nat? == some 8 && p.appFn!.appArg!.nat? == some 0
        then pure (mkApp2 (mkConst ``ShapeOf.slot) τ p.appArg!)
        else pure S
      else pure S
    else pure S
  return mkApp3 e'.appFn!.appFn!.appFn! e'.appFn!.appFn!.appArg! hd' (← normStack e'.appArg!)

/-- A context written as its five parts, with each register's type and the
list of owned blocks worked out where a definition stood in for them: a
signature's field, say. Returns nothing if there was nothing to do. -/
private def workOutCtx (ctx : Expr) : MetaM (Option Expr) := do
  unless ctx.isAppOfArity ``CtxOf.mk 6 do return none
  let args := ctx.getAppArgs
  let mut regs := args[1]!
  let mut changed := false
  if regs.isAppOfArity ``RegMap.get 2 && regs.appArg!.isAppOfArity ``RegMap.mk 17 then
    let tbl := regs.appArg!.getAppArgs
    let mut out := tbl
    for i in [1:17] do
      let e := tbl[i]!
      unless (← isConstructorApp e) || e.getAppFn.isFVar do
        let e' ← whnf e
        unless e' == e do
          out := out.set! i e'
          changed := true
    regs := mkApp regs.appFn! (mkAppN regs.appArg!.getAppFn out)
  let owned ← normOwned args[5]!
  unless owned == args[5]! do changed := true
  let stack ← normStack args[2]!
  unless stack == args[2]! do changed := true
  unless changed do return none
  return some (mkAppN ctx.getAppFn (((args.set! 1 regs).set! 2 stack).set! 5 owned))

elab_rules : tactic
  | `(tactic| ty_normalize) => do
    let g ← getMainGoal
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isAppOfArity ``BlockOk 6 do
      evalTactic (← `(tactic| ty_dsimp_ctx))
      return
    -- a context given by name is opened up
    let mut opened := t
    for _ in [0:4] do
      let ctx := opened.appArg!
      if ctx.isAppOf ``CtxOf.mk || ctx.isFVar || ctx.isMVar || !ctx.getAppFn.isConst then break
      let some ctx' ← unfoldDefinition? ctx | break
      opened := mkApp opened.appFn! ctx'.headBeta
    unless opened == t do
      replaceMainGoal [← g.replaceTargetDefEq opened]
    -- the register types, as a table of the sixteen
    let regs ← whnfR (← mkAppM ``CtxOf.regs #[opened.appArg!])
    unless regs.isAppOf ``RegMap.get && regs.appArg!.isAppOf ``RegMap.mk do
      evalTactic (← `(tactic| refine BlockOk.regsEta ?_))
    evalTactic (← `(tactic| ty_dsimp_ctx))
    -- what a definition still stands in for, worked out
    let g ← getMainGoal
    let t := (← instantiateMVars (← g.getType)).consumeMData
    if t.isAppOfArity ``BlockOk 6 then
      if let some ctx' ← g.withContext (workOutCtx t.appArg!) then
        replaceMainGoal [← g.replaceTargetDefEq (mkApp t.appFn! ctx')]
        evalTactic (← `(tactic| ty_dsimp_ctx))
    -- the address, as a number
    let g ← getMainGoal
    let t := (← instantiateMVars (← g.getType)).consumeMData
    if t.isAppOfArity ``BlockOk 6 then
      let a := t.appFn!.appArg!
      unless isAddrLit a || a.hasFVar || a.hasMVar do
        try
          let n ← evalAddr a
          let lit := toExpr (BitVec.ofNat 64 n)
          let g' ← g.replaceTargetDefEq (mkApp (mkApp t.appFn!.appFn! lit) t.appArg!)
          replaceMainGoal [g']
        catch _ => pure ()

/-- The instruction a closed term denotes. -/
@[implemented_by evalInstrUnsafe]
private opaque evalInstr (e : Expr) : MetaM Instr

/-- The instruction in a goal, if it is fully known. -/
private def knownInstr (e : Expr) : MetaM (Option Instr) := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasFVar then return none
  try return some (← evalInstr e) catch _ => return none

/-- Runs a tactic with room for long lists. A stack described slot by slot
can be long, and walking such a list takes more nested calls than Lean allows
by default. -/
def deep {α : Type} (x : TacticM α) : TacticM α :=
  withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 16384 }) x

/-- Tries one rule on the main goal, undoing everything if it does not finish. -/
private def tryRule (rule : Name) : TacticM Bool := deep do
  let saved ← saveState
  try
    if orderedRules.contains rule then
      evalTactic (← `(tactic| ty_rule_ordered $(mkIdent rule)))
    else
      evalTactic (← `(tactic| ty_rule $(mkIdent rule)))
    return true
  catch _ =>
    saved.restore
    return false

/-- Shows a term without the internal names of unknowns. -/
private def ppClean (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.mvars false) (ppExpr (← instantiateMVars e))
  -- One line, however long: these appear inside sentences.
  return fmt.pretty (width := 100000)

/-- The elements of a list written out in full, if the term is one. -/
private partial def listElems? (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.nil 1 then some []
  else if e.isAppOfArity ``List.cons 3 then
    (listElems? e.appArg!).map (e.appFn!.appArg! :: ·)
  else none

mutual

/-- A block's shape in the notation used in messages: `16 bytes` for plain
bytes, the typed values with where they start otherwise, and `4 × (…)` for
an array. -/
private partial def ppShape (S : Expr) : MetaM String := do
  let S ← instantiateMVars S
  if S.isAppOfArity ``ShapeOf.rep 3 then
    return s!"{← ppClean S.appFn!.appArg!} × ({← ppShape S.appArg!})"
  if S.isAppOfArity ``ShapeOf.raw 2 then
    return s!"{← ppClean S.appArg!} bytes"
  if S.isAppOfArity ``ShapeOf.mk 3 then
    let size ← ppClean S.appFn!.appArg!
    match listElems? S.appArg! with
    | some [] => return s!"{size} bytes"
    | some elems =>
      let mut parts : List String := []
      for p in elems do
        if p.isAppOfArity ``Prod.mk 4 then
          parts := parts ++ [s!"{← ppTy p.appArg!} at byte {← ppClean p.appFn!.appArg!}"]
        else parts := parts ++ [← ppClean p]
      return s!"{size} bytes with {", ".intercalate parts}"
    | none => return ← ppClean S
  ppClean S

/-- A type in the notation used in messages: `int`, `exactly 5`,
`pointer to [int, int]`. Falls back to the Lean term for anything else. -/
private partial def ppTy (e : Expr) : MetaM String := do
  -- a type read out of a block's shape arrives as a projection to be worked out
  let e ← whnfR (← instantiateMVars e)
  if e.isConstOf ``Ty.int then return "int"
  if e.isAppOfArity ``Ty.eq 1 then return s!"exactly {← ppClean e.appArg!}"
  if e.isAppOfArity ``Ty.code 1 then return "code pointer"
  if e.isAppOf ``Ty.fn || e.isAppOf ``FnSig.ty || e.isAppOf ``Ty.fnAll || e.isAppOf ``FnSigEx.ty then
    return "function pointer"
  if e.isAppOfArity ``Ty.nullable 1 then return s!"{← ppTy e.appArg!} or null"
  if e.isAppOfArity ``Ty.orErr 1 then return s!"{← ppTy e.appArg!} or an error number"
  if e.isAppOfArity ``Ty.str 1 then
    return if e.appArg!.isConstOf ``Bool.true then "pointer into text, not at its end"
      else "pointer into text"
  if e.isAppOfArity ``Ty.ref 3 then
    let args := e.getAppArgs
    let kind := if args[1]!.isConstOf ``Bool.true then "pointer" else "read-only pointer"
    let index ← ppClean args[2]!
    return s!"{kind} to a block of kind {← ppClean args[0]!}" ++
      (if index == "0" then "" else s!", at byte {index}")
  if e.isAppOfArity ``Ty.ptr 3 then
    let args := e.getAppArgs
    let kind := if args[1]!.isConstOf ``Bool.true then "pointer" else "read-only pointer"
    let index ← ppClean args[2]!
    return s!"{kind} to {← ppShape args[0]!}" ++
      (if index == "0" then "" else s!", at byte {index}")
  ppClean e

end

/-- The name of a register, if the term is one. -/
private def regName? (e : Expr) : Option String :=
  match e.constName? with
  | some (.str ``Reg n) => some n
  | _ => none

/-- Describes, in terms of the program, a rule premise that could not be proved. -/
private def describePremise (ty : Expr) : MetaM MessageData := do
  let ty ← instantiateMVars ty
  if let some (_, lhs, rhs) := ty.eq? then
    -- what a divide needs of the upper half of its dividend
    if lhs.isAppOf ``BitVec.setWidth && rhs.isAppOf ``signFill then
      return m!"`rdx` is not known to hold the sign extension of `rax`: use `cqo` or `cdq` \
        before the divide"
    if lhs.isAppOf ``BitVec.setWidth && !rhs.isAppOf ``BitVec.setWidth then
      return m!"`rdx`, the upper half of the dividend, is not known to be zero: clear it \
        before the divide"
    -- what a register must hold
    if lhs.isAppOfArity ``CtxOf.regs 3 then
      let reg := (regName? (← whnf lhs.appArg!)).getD "the register"
      let actual ← ppTy (← reduce lhs)
      if lhs.appArg!.isAppOf ``IndexReg.toReg then
        return m!"the index register `{reg}` must hold an exactly known value, but its type \
          is `{actual}`; `ty_name` gives an integer a name"
      let wanted :=
        if rhs.isAppOf ``Ty.ptr then
          if rhs.getAppArgs[1]!.isConstOf ``Bool.true then "a writable pointer" else "a pointer"
        else if rhs.isAppOf ``Ty.eq then "an exactly known value"
        else if rhs.isAppOf ``Ty.code then "a code pointer"
        else if rhs.isAppOf ``Ty.fn || rhs.isAppOf ``FnSig.ty || rhs.isAppOf ``Ty.fnAll ||
            rhs.isAppOf ``FnSigEx.ty then "a function pointer"
        else "a value of another type"
      let held ← reduce lhs
      let hint :=
        if held.isAppOf ``Ty.nullable then
          ": it must be tested for null first, and `ty_null` then gives the two cases"
        else if held.isAppOf ``Ty.orErr then
          ": it must be tested for an error first, and `ty_err` then gives the two cases"
        else if held.isAppOf ``Ty.ref && rhs.isAppOf ``Ty.ptr then
          ": `ty_open` turns it into a pointer to a block of that kind's shape"
        else ""
      return m!"`{reg}` must hold {wanted}, but its type is `{actual}`{hint}"
    if lhs.isAppOf ``MemTy.locate then
      return m!"the address is not inside any memory block"
    if lhs.isAppOf ``AluOp.readsCarry then
      return m!"this rule does not cover operations that read the carry flag"
    if lhs.isAppOf ``stackDrop then
      return m!"the pieces at the top of the stack do not come to exactly that many bytes"
    if lhs.isAppOfArity ``CtxOf.room 2 then
      return m!"there is not enough free stack: the context has room for {← ppClean (← reduce lhs)}"
    if lhs.isAppOf ``ShapeOf.free then
      if ty.hasFVar then
        return m!"the bytes are not known to be clear of the typed values the block holds"
      return m!"a typed value of the block reaches into those bytes, and plain bytes may not \
        be stored over it"
    if lhs.isAppOf ``ShapeOf.sole then
      return m!"another typed value of the block reaches into those eight bytes"
    -- a typed value or stack slot lookup
    let actual ← reduce lhs
    if actual.isAppOf ``Option.none then
      if lhs.isAppOf ``ShapeOf.valAt then
        return m!"no typed value of the block starts at that offset"
      return m!"there is no stack slot at that offset"
    if lhs.isAppOf ``ShapeOf.valAt && !actual.isAppOf ``Option.some then
      return m!"the block is not known to hold a typed value there: a bound on the index is \
        needed among the hypotheses"
    if rhs.isAppOf ``Option.some && actual.isAppOf ``Option.some then
      return m!"the field must have type `{← ppTy rhs.appArg!}`, but has type \
        `{← ppTy actual.appArg!}`"
    if rhs.isAppOf ``Option.some then
      return m!"the field is not known to be inside the block: a bound on the index is needed \
        among the hypotheses"
    return m!"needs `{← ppClean ty}`, but the left side is `{← ppClean actual}`"
  if ty.isAppOf ``StackAt then
    return m!"those bytes are not known to be inside one piece of the stack"
  if ty.isAppOf ``byteDisp then
    return m!"the displacement must be non-negative"
  if ty.isAppOfArity ``Sub 2 then
    return m!"a value of type `{← ppTy (← reduce ty.appFn!.appArg!)}` cannot be stored \
      where `{← ppTy ty.appArg!}` is required"
  if ty.isAppOfArity ``Ne 3 && (regName? ty.appArg!) == some "rsp" then
    return m!"`rsp` cannot be this operand"
  if ty.isAppOfArity ``Ne 3 && ty.appFn!.appArg!.isAppOf ``BitVec.setWidth then
    return m!"the divisor, `{← ppClean ty.appFn!.appArg!.appArg!}`, is not known to be \
      non-zero: a check is needed before the divide"
  if ty.isAppOfArity ``Ne 3 then
    return m!"`{← ppClean ty}` is not known: it is needed among the hypotheses"
  if ty.isAppOfArity ``Or 2 then
    return m!"neither `{← ppClean ty.appFn!.appArg!}` nor `{← ppClean ty.appArg!}` is known: \
      one is needed among the hypotheses"
  if ty.isAppOf ``LE.le && ty.appArg!.isAppOf ``ShapeOf.size then
    if ty.hasFVar then
      return m!"the bytes are not known to be inside the block: a bound on the index is \
        needed among the hypotheses"
    return m!"the access would reach past the end of the block"
  if ty.isAppOf ``LE.le then
    return m!"the access would reach past the end of its piece of the stack"
  if ty.isForall && ty.getForallBody.isAppOf ``Exists then
    return m!"the flags are not known here, so they do not decide the condition"
  if ty.isForall then
    return m!"the operation reads the carry flag, which is not known to be defined here"
  if ty.isAppOf ``OwnedAt || ty.isAppOf ``OwnedByte then
    return m!"the address is not known to be inside a block the context owns"
  if ty.isAppOf ``EaIs then
    return m!"the registers the address is computed from must each hold an exactly known \
      value; a register holding some number is given a name with `ty_name`"
  return m!"needs `{← ppClean ty}`"

/-- The rules for an operand judgment, in the order to try them. -/
private def operandRules (ty : Expr) : List Name :=
  if ty.isAppOf ``ReadOk then
    [``ReadOk.reg, ``ReadOk.slot, ``ReadOk.slotIndexed, ``ReadOk.field, ``ReadOk.indexed,
      ``ReadOk.global_of, ``ReadOk.text,
      ``ReadOk.owned]
  else if ty.isAppOf ``WriteIntOk then [``WriteIntOk.reg, ``WriteIntOk.slot,
    ``WriteIntOk.slotIndexed, ``WriteIntOk.field, ``WriteIntOk.indexed,
    ``WriteIntOk.global_of]
  else if ty.isAppOf ``Holds then [``Holds.reg, ``Holds.slot, ``Holds.field, ``Holds.indexed, ``Holds.global_of]
  else []

/-- The rule for an operand in an owned block, reached through its number of bytes. -/
private def ownedOperandRule (ty : Expr) : Option Name :=
  if ty.isAppOf ``ReadOk then some ``ReadOk.ownedAt
  else if ty.isAppOf ``WriteIntOk then some ``WriteIntOk.ownedAt
  else none

/-- The rules about the stack, whose premises speak of a piece of the stack
where the rules about blocks speak of a block. -/
private def stackRules : List Name :=
  [``ReadOk.slot, ``ReadOk.slotIndexed, ``WriteIntOk.slot, ``WriteIntOk.slotIndexed,
    ``Holds.slot, ``Straight.loadStack, ``Straight.loadStackIndexed, ``Straight.storeStack]

/-- A premise's description, in the words for the stack where the rule is
one about the stack. -/
private def describeFor (rule : Name) (ty : Expr) : MetaM MessageData := do
  let msg ← describePremise ty
  unless stackRules.contains rule do return msg
  let text ← msg.toString
  let text := text.replace "the block is not known to hold" "that piece of the stack is not known to hold"
  let text := text.replace "inside the block" "inside one piece of the stack"
  let text := text.replace "the end of the block" "the end of the piece of the stack it starts in"
  let text := text.replace " of the block" " of that piece of the stack"
  return m!"{text}"

/-- Applies a rule to the main goal and describes the first premise that
cannot be proved. `none` if the rule is for a goal of a different form. A
premise about an operand is explained by the rule for that kind of operand. -/
private partial def explainPremises (rule : Name) : TacticM (Option MessageData) := do
  try
    evalTactic (← `(tactic| refine' $(mkIdent rule) ..))
  catch _ =>
    return none
  let goals ← getGoals
  -- Premises are attempted in order and then again, as in `ty_rule`, so that
  -- what is reported is a premise that fails once everything else is known.
  let mut failed : Array (MVarId × Expr) := #[]
  let mut stop := false
  for pass in [0, 1] do
    for g in goals do
      if ← g.isAssigned then continue
      unless ← isProp (← g.getType) do continue
      setGoals [g]
      let attempt ← saveState
      let ok ← try
          evalTactic (← `(tactic| ty_side))
          pure true
        catch _ =>
          attempt.restore
          pure false
      if !ok then
        let ty ← instantiateMVars (← g.getType)
        -- Where premises build on one another, nothing after the first
        -- failure can be judged.
        if orderedRules.contains rule then
          failed := #[(g, ty)]
          stop := true
          break
        if pass == 1 then failed := failed.push (g, ty)
    if stop then break
  -- A premise about the displacement is reported first: the others cannot
  -- be judged until it holds. After that, prefer a premise with no unknowns.
  let isDisp (e : MVarId × Expr) : Bool :=
    e.2.isAppOf ``byteDisp
  let chosen := (failed.find? isDisp <|> failed.find? (!·.2.hasExprMVar) <|> failed[0]?)
  match chosen with
  | some (g, ty) =>
    let inner := operandRules ty
    if inner.isEmpty then return some (← describeFor rule ty)
    -- Where the address is exactly known the operand is in an owned block or
    -- nowhere, and the rule for owned blocks is the one to explain.
    if let some r := ownedOperandRule ty then
      setGoals [g]
      let saved ← saveState
      let exact ← try
          evalTactic (← `(tactic| refine' $(mkIdent r) ..))
          let mut ok := false
          for h in ← getGoals do
            if (← instantiateMVars (← h.getType)).isAppOf ``EaIs then
              setGoals [h]
              evalTactic (← `(tactic| ty_side))
              ok := true
          pure ok
        catch _ => pure false
      saved.restore
      if exact then
        setGoals [g]
        if let some msg ← explainPremises r then return some msg
    for r in inner do
      setGoals [g]
      if let some msg ← explainPremises r then return some msg
    return some m!"this form of operand has no rule: a memory operand needs a base register \
      or `rip`"
  | none => return some m!"every premise holds separately, but not together"

/-- Says why a rule did not apply: the first premise that could not be proved. -/
private def explainRule (rule : Name) : TacticM MessageData := do
  let saved ← saveState
  let name := rule.components.getLast!
  try
    match ← explainPremises rule with
    | some msg => return m!"{name}: {msg}"
    | none => return m!"{name}: is for a different form of this instruction"
  finally
    saved.restore

/-- Types the instruction in a `Straight Ψ next Γ i ?Γ'` goal, or explains why not. -/
def typeStraight : TacticM Unit := deep <| withMainContext do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOfArity ``Straight 5 do
    throwError "ty_straight: the goal is not of the form `Straight Ψ next Γ i Γ'`"
  let instrExpr := ty.getAppArgs[3]!
  let instr? ← knownInstr instrExpr
  let rules := match instr? with
    | some i => i.rules
    | none => allStraightRules
  for rule in rules do
    if ← tryRule rule then return
  let shown : MessageData := match instr? with
    | some i => m!"`{i.toAsm}`"
    | none => m!"{instrExpr}"
  if rules.isEmpty then
    match instr?.bind Instr.noRuleReason with
    | some why => throwError "cannot type {shown}: {why}"
    | none => throwError "the type system has no rule for {shown}"
  let mut msg := m!"cannot type {shown} in the current context"
  -- Why a rule for owned blocks did not apply is of no interest where
  -- nothing is owned.
  let ownsNothing ← try
      let goalTy ← instantiateMVars (← (← getMainGoal).getType)
      let owned ← whnf (← mkAppM ``CtxOf.owned #[goalTy.getAppArgs[2]!])
      pure (owned.isAppOf ``List.nil)
    catch _ => pure false
  let general := rules.filter fun r =>
    !sharpeningRules.contains r &&
      !(ownsNothing && [``Straight.loadOwned, ``Straight.storeOwnedTyped,
        ``Straight.storeOwnedKeep].contains r)
  -- rules that fail for the same reason are listed once, under the first
  let mut said : List String := []
  for rule in (if general.isEmpty then rules else general) do
    let why ← explainRule rule
    let text ← why.toString
    let reason := (text.splitOn ": ").drop 1 |> String.intercalate ": "
    if said.contains reason then continue
    said := reason :: said
    msg := msg ++ m!"\n• {why}"
  throwError msg

/-- Types the instruction in a `Straight` goal, choosing the rule from the
instruction's shape. When no rule applies, the error names the instruction
and, for each rule that could have applied, the premise that failed. -/
elab "ty_straight" : tactic => typeStraight

/-- The outcome of trying to take one step in a block. -/
private inductive StepResult
  | stepped
  | endOfBlock (instr : Instr)
  | notABlock

/-- Runs a tactic on one goal and returns the goals it leaves. -/
private def runOn (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  setGoals [g]
  -- Without this a failing step is logged and its goal admitted, and the
  -- caller would carry on as if it had succeeded. The fresh scope gives the
  -- named placeholders in `tac` names of their own: without it, a second use
  -- of the same step in one tactic call would be handed the first one's proof.
  deep (Tactic.withoutRecover (withFreshMacroScope tac))
  getUnsolvedGoals

/-- The system call number a context puts in `rax`, if it is exactly known. -/
private def syscallNumber (ctx : Expr) : MetaM (Option Nat) := do
  let regTy ← whnf (← mkAppM ``CtxOf.regs #[ctx, mkConst ``Reg.rax])
  unless regTy.isAppOfArity ``Ty.eq 1 do return none
  let v ← instantiateMVars regTy.appArg!
  if v.hasExprMVar || v.hasFVar then return none
  try return some (← evalAddr v) catch _ => return none

/-- A system call that returns and asks nothing of the program's memory:
its number, its name and its rule. -/
private def plainCalls : List (Nat × String × Name) :=
  [(1, "write", ``linux_write), (3, "close", ``linux_close), (8, "lseek", ``linux_lseek),
   (257, "openat", ``linux_openat)]

/-- A system call that stores into a buffer: its number and name, the rule
for a buffer in a memory block and the rule for one on the stack, the
register holding the buffer, and how much is stored there: the count in a
register, or a fixed number of bytes. -/
private def bufferCalls : List (Nat × String × Name × Name × String × (String ⊕ Nat)) :=
  [(0, "read", ``linux_read, ``linux_read_stack, "rsi", .inl "rdx"),
   (5, "fstat", ``linux_fstat, ``linux_fstat_stack, "rsi", .inr 144),
   (228, "clock_gettime", ``linux_clock_gettime, ``linux_clock_gettime_stack, "rsi", .inr 16),
   (318, "getrandom", ``linux_getrandom, ``linux_getrandom_stack, "rdi", .inl "rsi")]

/-- Whether a call number is one that is typed as a step in a block. -/
private def isStepCall (nr : Nat) : Bool :=
  plainCalls.any (·.1 == nr) || bufferCalls.any (·.1 == nr)

/-- The names of the calls that can be typed, for messages. -/
private def typedCalls : String :=
  "`read` (0), `write` (1), `close` (3), `fstat` (5), `lseek` (8), `mmap` (9), `exit` (60), \
   `clock_gettime` (228), `exit_group` (231), `openat` (257) and `getrandom` (318)"

/-- The shape of a system call's rule: what it leaves to be found out. -/
private inductive SysShape
  /-- Nothing but the call number. -/
  | plain
  /-- A buffer in a memory block; `sized` if the count comes from a register. -/
  | block (sized : Bool)
  /-- A buffer on the stack. -/
  | stack (sized : Bool)

/-- Applies a system call's rule at the head of a block goal and returns the
goals it leaves: its premises, and the rest of the block. -/
private def applySysRule (goal : MVarId) (rule : Name) (shape : SysShape) :
    TacticM (List MVarId) := do
  let r := mkIdent rule
  let tac ← match shape with
    | .plain => `(tactic| refine BlockOk.sys (by ty_fetch) ($r ?_) ?_)
    | .block true =>
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (S := ?_) (off := ?_) (len := ?_) ?_ ?_ ?_ ?_ ?_) ?_)
    | .block false =>
      `(tactic| refine BlockOk.sys (by ty_fetch) ($r (S := ?_) (off := ?_) ?_ ?_ ?_ ?_) ?_)
    | .stack true =>
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (v := ?_) (d := ?_) (k := ?_) (i := ?_) (S := ?_) (len := ?_)
            ?_ ?_ ?_ ?_ ?_ ?_) ?_)
    | .stack false =>
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (v := ?_) (d := ?_) (k := ?_) (i := ?_) (S := ?_) ?_ ?_ ?_ ?_ ?_) ?_)
  try
    runOn goal (do evalTactic tac)
  catch _ => throwError "`syscall`: the operating system here is not the Linux model"

/-- An exactly known value is itself with nothing added: an address that is
the stack pointer's own is zero bytes above it. -/
theorem Ty.eq_add_zero (v : BitVec 64) : Ty.eq v = Ty.eq (v + 0) := by simp

/-- Types a call whose buffer is on the stack, at the head of a block goal.
Returns the rest of the block. -/
private def typeBufferStack (goal : MVarId) (rule : Name) (sized : Bool) : TacticM MVarId := do
  let gs ← applySysRule goal rule (.stack sized)
  -- what the registers hold first: that settles where the buffer is
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        discard <| runOn g (do evalTactic (← `(tactic| first | rfl | exact Ty.eq_add_zero _)))
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``StackAt then
      discard <| runOn g (do evalTactic (← `(tactic| ty_stack_at)))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if (← isProp t) then
      discard <| runOn g (do evalTactic (← `(tactic| ty_stack_in)))
  let some rest := rest? | throwError "unexpected goals"
  return rest

/-- Types a call whose buffer is in memory the program owns, at the head of a
block goal. Returns the rest of the block. -/
private def typeBufferOwned (goal : MVarId) (rule : Name) (sized : Bool) : TacticM MVarId := do
  let r := mkIdent rule
  let tac ← if sized then
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (k := ?_) (lo := ?_) (a := ?_) (v := ?_) (S := ?_) (len := ?_) ?_ ?_ ?_ ?_ ?_) ?_)
    else
      `(tactic| refine BlockOk.sys (by ty_fetch)
          ($r (k := ?_) (lo := ?_) (a := ?_) (v := ?_) (S := ?_) ?_ ?_ ?_ ?_) ?_)
  let gs ← runOn goal (do evalTactic tac)
  -- what the registers hold, then which block and field the buffer starts at
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        discard <| runOn g (do evalTactic (← `(tactic| rfl)))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``OwnedByte then
      discard <| deep <| runOn g (do evalTactic (← `(tactic| ty_owned_byte)))
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if (← isProp t) then
      discard <| deep <| runOn g (do evalTactic (← `(tactic| ty_inside)))
  let some rest := rest? | throwError "unexpected goals"
  return rest

/-- Types a system call that returns, at the head of a block goal, leaving
the rest of the block as the main goal. -/
private def typeSyscallStep (goal : MVarId) (nr : Nat) : TacticM Unit := do
  let ctx := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs[5]!
  if let some (_, _, rule) := plainCalls.find? (·.1 == nr) then
    let gs ← applySysRule goal rule .plain
    let mut rest? : Option MVarId := none
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``BlockOk then rest? := some g
      else discard <| runOn g (do evalTactic (← `(tactic| rfl)))
    let some rest := rest? | throwError "ty_block: unexpected goals at `syscall`"
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    return
  let some (_, name, rule, stackRule, bufReg, size) := bufferCalls.find? (·.1 == nr)
    | throwError "`syscall`: call number {nr} is not typed as a step"
  let sized := size.isLeft
  let saved ← saveState
  try
    let rest ← typeBufferStack goal stackRule sized
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    return
  catch _ => saved.restore
  try
    let rest ← typeBufferOwned goal (Name.mkStr rule.getPrefix (rule.getString! ++ "_owned")) sized
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    return
  catch _ => saved.restore
  let gs ← applySysRule goal rule (.block sized)
  let mut rest? : Option MVarId := none
  let mut left : List MVarId := []
  -- what the registers must hold first: that settles the buffer and the count
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else if let some (_, lhs, rhs) := t.eq? then
      unless lhs.isAppOf ``CtxOf.regs do continue
      try
        discard <| runOn g (do evalTactic (← `(tactic| rfl)))
      catch _ =>
        let reg := (regName? lhs.appArg!).getD "the register"
        let actual ← g.withContext do ppTy (← reduce (← mkAppM ``CtxOf.regs #[ctx, lhs.appArg!]))
        if rhs.isAppOf ``Ty.ptr then
          throwError "`{name}` needs `{reg}` to hold a writable pointer to the buffer, the \
            address of stack slots taken with `lea` once `rsp` has a name, or the address of \
            a byte of a block the context owns, but its type is `{actual}`"
        else
          throwError "`{name}` needs the count in `{reg}` to be exactly known, but its type is \
            `{actual}`"
  -- then that the bytes the buffer covers are inside the block and plain
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then continue
    unless ← isProp t do continue
    let after ← try
        runOn g (do evalTactic (← `(tactic| first
          | decide
          | exact rfl
          | ty_inside)))
      catch _ =>
        match size with
        | .inl cntReg =>
          throwError "`{name}` could overwrite something that is not plain bytes: the buffer \
            in `{bufReg}` does not have room for the count in `{cntReg}` in plain bytes of \
            its block"
        | .inr bytes =>
          throwError "`{name}` could overwrite something that is not plain bytes: the buffer \
            in `{bufReg}` does not have room in plain bytes of its block for the {bytes} \
            bytes the kernel stores"
    left := left ++ after
  let some rest := rest? | throwError "ty_block: unexpected goals at `syscall`"
  setGoals [rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left)

/-- Types the first instruction of a block goal if it is a straight-line
instruction, leaving the rest of the block as the main goal. -/
private partial def typeStep (named : Bool := false) : TacticM StepResult :=
    deep <| withMainContext do
  let goal ← getMainGoal
  let ty := (← instantiateMVars (← goal.getType)).consumeMData
  unless ty.isAppOf ``BlockOk do return .notABlock
  let saved ← saveState
  let others := (← getGoals).drop 1
  setGoals [goal]
  try
    evalTactic (← `(tactic| refine BlockOk.step (Γ' := ?_) (by ty_fetch) ?_ ?_))
  catch _ =>
    saved.restore
    throwError "there is no instruction at this address"
  let mut instrGoal? : Option MVarId := none
  let mut restGoal? : Option MVarId := none
  for g in ← getGoals do
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``Straight then instrGoal? := some g
    else if t.isAppOf ``BlockOk then restGoal? := some g
  let (some instrGoal, some restGoal) := (instrGoal?, restGoal?)
    | saved.restore; throwError "ty_step: unexpected goals after taking a step"
  let instrTy ← instantiateMVars (← instrGoal.getType)
  if let some instr ← knownInstr instrTy.getAppArgs[3]! then
    if instr.endsBlock then
      saved.restore
      -- A system call that returns is a step like any other.
      if let .syscall := instr then
        if let some nr ← syscallNumber ty.getAppArgs[5]! then
          if isStepCall nr then
            setGoals [goal]
            typeSyscallStep goal nr
            setGoals ((← getGoals) ++ others)
            return .stepped
      return .endOfBlock instr
    -- Registers the rules need to speak of, but which are only known to be
    -- integers, are given names first.
    unless named do
      let ctx := ty.getAppArgs[5]!
      let mut toName : List Reg := []
      for r in instr.wantsNamed.eraseDups do
        let regE := mkConst (Name.str ``Reg r.name64)
        let regTy ← whnf (← mkAppM ``CtxOf.regs #[ctx, regE])
        if regTy.isConstOf ``Ty.int then toName := toName ++ [r]
      unless toName.isEmpty do
        saved.restore
        setGoals [goal]
        for r in toName do
          nameRegister (mkIdent (Name.str ``Reg r.name64))
            (mkIdent (Name.mkSimple s!"{r.name64}₀"))
        setGoals ((← getGoals) ++ others)
        return ← typeStep (named := true)
  setGoals [instrGoal]
  let addr ← instantiateMVars ty.getAppArgs[4]!
  let at? ← if addr.hasExprMVar || addr.hasFVar then pure none
    else try pure (some (← evalAddr addr)) catch _ => pure none
  try
    typeStraight
  catch e =>
    match at? with
    | some n => throwError "at address {n}: {e.toMessageData}"
    | none => throw e
  setGoals [restGoal]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ others)
  return .stepped

/-- Types one straight-line instruction at the start of a block. -/
elab "ty_step" : tactic => do
  match ← typeStep with
  | .stepped => pure ()
  | .endOfBlock instr =>
    throwError "`{instr.toAsm}` can transfer control, so it ends the block and is not typed by `ty_step`"
  | .notABlock => throwError "ty_step: the goal is not a block"

/-- Types the straight-line instructions at the start of a block, stopping
at the first instruction that can transfer control and leaving it as the
goal. A straight-line instruction that cannot be typed is an error. -/
elab "ty_steps" : tactic => do
  repeat
    match ← typeStep with
    | .stepped => continue
    | _ => break

/-! ## Control transfers

For a labelled program the tactic can find where control goes: it looks for
the label at the target address, then for a context allowed at that label
which the current context is at least as strong as. Whatever it cannot
settle is left as a goal: typically a fact about values that the target's
context demands, such as a loop bound. -/

/-- The constructors of the inductive type a term's type belongs to. -/
private def ctorsOfType (ty : Expr) : MetaM (List Name) := do
  let ty ← whnf (← instantiateMVars ty)
  let some n := ty.getAppFn.constName? | return []
  match (← getEnv).find? n with
  | some (.inductInfo info) => return info.ctors
  | _ => return []

/-- Whether a proposition compares two values. -/
private def isComparison (t : Expr) : Bool :=
  t.isAppOf ``LT.lt || t.isAppOf ``LE.le || t.isAppOf ``GT.gt || t.isAppOf ``GE.ge ||
  t.isAppOf ``Eq || t.isAppOf ``Ne || t.isAppOf ``Not

/-- Proves `Φ a Δ` for a labelled program: finds the label whose address is
`a` and a context allowed there. `check` runs once the context is chosen and
should fail if it is the wrong one; another is then tried. Returns the goals
`check` left, then the premises of the chosen context that remain unproved. -/
private def proveAtLabel (g : MVarId) (check : TacticM (List MVarId)) :
    TacticM (List MVarId) := do
  let parts ← try
      runOn g (do evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩)))
    catch _ =>
      throwError "the code typing here is not given by labels; name the target context with \
        `ty_accept`"
  let mut label? : Option MVarId := none
  let mut addr? : Option MVarId := none
  let mut fact? : Option MVarId := none
  for p in parts do
    let t ← instantiateMVars (← p.getType)
    if !(← isProp t) then label? := some p
    else if t.isEq then addr? := some p
    else fact? := some p
  let (some label, some addr, some fact) := (label?, addr?, fact?)
    | throwError "the code typing here is not given by labels; name the target context with \
        `ty_accept`"
  for c in ← ctorsOfType (← label.getType) do
    let atLabel ← saveState
    let found ← try
        label.assign (mkConst c)
        discard <| runOn addr (do evalTactic (← `(tactic| rfl)))
        pure true
      catch _ =>
        atLabel.restore
        pure false
    unless found do continue
    let mut reasons : MessageData := m!""
    for k in ← ctorsOfType (← fact.getType) do
      let atCtx ← saveState
      -- A context for some other label is passed over without comment.
      let premises? ← try
          pure (some (← runOn fact (do evalTactic (← `(tactic| refine' $(mkIdent k) ..)))))
        catch _ =>
          atCtx.restore
          pure none
      let some premises := premises? | continue
      try
        -- Premises that are not comparisons, such as a caller's requirement,
        -- are looked for among the hypotheses first. That fixes the parameters
        -- they mention to the ones in scope, where comparing contexts could
        -- settle on something equal in effect but different in form.
        for p in premises do
          if ← p.isAssigned then continue
          let t ← instantiateMVars (← p.getType)
          unless ← isProp t do continue
          if isComparison t then continue
          try
            discard <| runOn p (do evalTactic (← `(tactic| assumption)))
          catch _ => pure ()
        let left ← check
        let mut rest := left
        for p in premises do
          if ← p.isAssigned then continue
          unless ← isProp (← p.getType) do continue
          let after ← try
              runOn p (do evalTactic (← `(tactic| first | assumption | omega | decide)))
            catch _ => pure [p]
          rest := rest ++ after
        -- Parameters nothing determined are left for the user to supply.
        for p in premises do
          if ← p.isAssigned then continue
          unless ← isProp (← p.getType) do rest := rest ++ [p]
        return rest
      catch e =>
        atCtx.restore
        reasons := reasons ++ m!"\n• {k.components.getLast!}: {e.toMessageData}"
    throwError "no context allowed at label `{c.components.getLast!}` accepts the current one{reasons}"
  throwError "there is no label at the target address"

/-- Fails if a register comparison left as a goal can never hold: the two
types are fully known and of different kinds. -/
private def rejectImpossible (gs : List MVarId) : TacticM Unit := do
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    unless t.isAppOfArity ``Sub 2 do continue
    let have_ ← g.withContext (reduce t.appFn!.appArg!)
    let want ← g.withContext (reduce t.appArg!)
    if have_.hasExprMVar || want.hasExprMVar then continue
    if have_.getAppFn.constName? != want.getAppFn.constName? then
      let reg := (← g.getTag).eraseMacroScopes.components.getLast!
      throwError "`{reg}` has type `{← ppTy have_}`, but `{← ppTy want}` is required"

/-- Proves `Accepts Φ a Γ` by finding the label at `a`. Returns what is left. -/
private def proveAccepts (g : MVarId) : TacticM (List MVarId) := do
  let parts ← runOn g (do evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩)))
  let mut here? : Option MVarId := none
  let mut sub? : Option MVarId := none
  for p in parts do
    let t ← instantiateMVars (← p.getType)
    if t.isAppOf ``CtxSub then sub? := some p
    else if ← isProp t then here? := some p
  let (some here, some sub) := (here?, sub?)
    | throwError "ty_label: the goal is not of the form `Accepts Φ a Γ`"
  proveAtLabel here (do
    let left ← try
        runOn sub (do evalTactic (← `(tactic| ctx_sub)))
      catch _ =>
        -- say so when what differs is the blocks owned
        let sameOwned ← sub.withContext do
          try
            let args := (← instantiateMVars (← sub.getType)).getAppArgs
            let here ← mkAppM ``CtxOf.owned #[args[0]!]
            let there ← mkAppM ``CtxOf.owned #[args[1]!]
            withoutModifyingState (isDefEq here there)
          catch _ => pure true
        unless sameOwned do
          throwError "the blocks owned do not match: a block taken here must be given back \
            or frozen before control goes there"
        throwError "the stack, the free room or the flags do not match"
    rejectImpossible left
    pure left)

/-- Proves `Accepts Φ a Γ` in a labelled program by finding the label at
address `a` and a context allowed there that `Γ` is at least as strong as.
Facts the target's context demands, and register types that do not
obviously match, are left as goals. -/
elab "ty_label" : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  let left ← proveAccepts goal
  setGoals (left ++ others)

/-- Introduces the flags hypotheses of one side of a conditional jump. When
the flags are known exactly they are substituted. The fact about which way
the condition went is named `hcond`. -/
private def introBranch : TacticM Unit := do
  let hcond := mkIdent `hcond
  -- `rfl` must be written without macro hygiene, or `rintro` takes it for a name.
  let subst := mkIdent `rfl
  evalTactic (← `(tactic| first
    | rintro f $subst:ident $hcond:ident
    | (intro f hflags $hcond:ident; try dsimp only at hflags)))
  -- What an unsigned comparison's outcome says about the two numbers is put
  -- among the hypotheses as `hlt` or `hge`, for bounds on an index.
  let hlt := mkIdent `hlt
  let hge := mkIdent `hge
  -- only where the flags are those of a comparison: matching the lemmas
  -- against flags of another kind would set about computing them
  let isCmp ← withMainContext do
    let some d := (← getLCtx).findFromUserName? `hcond | pure false
    let t ← instantiateMVars d.type
    pure (t.find? (·.isConstOf ``AluOp.cmp)).isSome
  if isCmp then try
    Tactic.withoutRecover do evalTactic (← `(tactic| first
      | (have $hlt := cmp_below $hcond
         try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at $hlt:ident)
      | (have $hlt := cmp_not_ae $hcond
         try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at $hlt:ident)
      | (have $hge := cmp_not_below $hcond
         try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at $hge:ident)
      | (have $hge := cmp_ae $hcond
         try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at $hge:ident)))
  catch _ => pure ()

/-- Closes a goal reached under an assumption about a condition that the
exactly known flags contradict. Returns whether it did. -/
private def closeIfImpossible (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    setGoals [g]
    Tactic.withoutRecover do
      evalTactic (← `(tactic| (refine absurd $(mkIdent `hcond) ?_; decide)))
    return (← getUnsolvedGoals).isEmpty
  catch _ =>
    saved.restore
    -- The flags may come from a value known only by a fact about it: an
    -- error number, or a byte that is not zero.
    let isErr ← g.withContext do
      (← getLCtx).anyM fun d => do
        let t ← instantiateMVars d.type
        return t.isAppOf ``SysErr || t.isAppOf ``Ne || t.isAppOf ``LT.lt
    unless isErr do return false
    try
      setGoals [g]
      Tactic.withoutRecover do
        evalTactic (← `(tactic| (
          refine absurd $(mkIdent `hcond) ?_
          try simp only [SysErr] at *
          simp only [Cond.eval, Flags.ofResult, AluOp.apply, subBorrow, bind, Option.bind, pure,
            Option.map, Option.some.injEq]
          try simp only [BitVec.and_self, BitVec.or_self]
          first
            | bv_omega
            | (simp only [BitVec.msb_eq_decide, beq_iff_eq, decide_eq_true_eq,
                 decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false, Nat.not_le,
                 Nat.not_lt]
               bv_omega))))
      return (← getUnsolvedGoals).isEmpty
    catch _ =>
      saved.restore
      return false

/-- Shows the flags decide a condition. -/
private def decideCond : TacticM Unit := do
  let subst := mkIdent `rfl
  evalTactic (← `(tactic| first
    | (rintro f $subst:ident; exact ⟨_, rfl⟩)
    | exact Cond.decided_of_known (fun _ h => h) _
    | (refine Cond.decided_of_defined _ ?_; decide)))

/-- The goal among `gs` that came from the placeholder `?name`. Goals are
found by name because the order in which `refine` returns them is not fixed. -/
private def goalNamed (gs : List MVarId) (name : Name) : TacticM MVarId := do
  for g in gs do
    let tag := (← g.getTag).eraseMacroScopes
    if !tag.isAnonymous && tag.components.getLast! == name then return g
  throwError "ty_block: internal error, no goal named {name}"

/-- `ty_step_with r` types one straight-line instruction with the rule `r`,
for a rule the tactics would not choose or could not finish: typically one
with a premise about values, such as a divisor not being zero. Premises that
are not routine are left as goals, after the rest of the block. -/
elab "ty_step_with " r:term : tactic => withMainContext do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  let gs ← try
      runOn goal (do evalTactic (← `(tactic| refine BlockOk.step (Γ' := ?_) (by ty_fetch) ?instr ?rest)))
    catch _ => throwError "ty_step_with: there is no instruction at this address"
  let instr ← goalNamed gs `instr
  let rest ← goalNamed gs `rest
  let premises ← try
      runOn instr (do evalTactic (← `(tactic| refine' $r ..)))
    catch e => throwError "ty_step_with: the rule does not fit this instruction\n{e.toMessageData}"
  let mut left : List MVarId := []
  for pass in [0, 1] do
    for p in premises do
      if ← p.isAssigned then continue
      unless ← isProp (← p.getType) do continue
      let after ← try
          runOn p (do evalTactic (← `(tactic| first | ty_side | assumption)))
        catch _ => pure [p]
      if pass == 1 then left := left ++ after
  setGoals [rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left ++ others)

/-- What ending a block did. -/
private inductive Finish
  /-- The block is finished; these goals are left. -/
  | done (left : List MVarId)
  /-- A conditional jump was typed and the block continues in `rest`. -/
  | continues (rest : MVarId) (left : List MVarId)
  /-- This instruction needs information the tactic does not have. -/
  | needsHelp (msg : MessageData)

/-- Types the control transfer at the head of a block goal. -/
private def finishBlock (goal : MVarId) (instr : Instr) : TacticM Finish := do
  match instr with
  | .jmp (.rel _) =>
    let gs ← runOn goal (do evalTactic (← `(tactic| refine BlockOk.last (by ty_fetch) (HasType.jmp ?_))))
    let [acc] := gs | throwError "ty_block: unexpected goals at `jmp`"
    return .done (← proveAccepts acc)
  | .syscall =>
    -- `write` and `read` are typed as steps; what reaches here is `exit`, or
    -- a call the type system has no rule for.
    let ctx := (← instantiateMVars (← goal.getType)).consumeMData.getAppArgs[5]!
    match ← syscallNumber ctx with
    | some 60 =>
      let gs ← try
          runOn goal (do evalTactic (← `(tactic|
            refine BlockOk.last (by ty_fetch) (HasType.syscallExit (linux_exit rfl)))))
        catch _ => throwError "`syscall`: the operating system here is not the Linux model"
      return .done gs
    | some 231 =>
      let gs ← try
          runOn goal (do evalTactic (← `(tactic|
            refine BlockOk.last (by ty_fetch) (HasType.syscallExit (linux_exit_group rfl)))))
        catch _ => throwError "`syscall`: the operating system here is not the Linux model"
      return .done gs
    | some 9 =>
      return .needsHelp m!"`syscall`: an `mmap` needs the layout of the new block; use \
        `ty_mmap <shape>` or `ty_mmap_kind <kind>`"
    | some nr =>
      throwError "`syscall`: call number {nr} has no rule. The calls that can be typed are \
        {typedCalls}"
    | none =>
      let actual ← goal.withContext do
        ppTy (← reduce (← mkAppM ``CtxOf.regs #[ctx, mkConst ``Reg.rax]))
      throwError "`syscall`: the call number in `rax` must be exactly known, but its type is \
        `{actual}`"
  | .ret =>
    let gs ← try
        runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last (by ty_fetch)
            (FnSig.ret_of (sig := ?_) (saved := ?_) ?caller ?regs ?sp rfl rfl ?own))))
      catch _ =>
        let family ← goal.withContext do
          try
            let t := (← instantiateMVars (← goal.getType)).consumeMData
            let stack ← whnf (← mkAppM ``CtxOf.stack #[t.appArg!])
            if stack.isAppOfArity ``List.cons 3 then
              pure ((← instantiateMVars stack.appFn!.appArg!).find?
                (·.isConstOf ``Ty.codeAll)).isSome
            else pure false
          catch _ => pure false
        if family then
          throwError "`ret`: the return address here is ready for a family of contexts, one \
            for each value the function may hand back; say which the function returns into \
            with `ty_return_as`"
        throwError "`ret` needs a return address on top of the stack, but the context does \
          not have one there"
    let mut left := []
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``FnSig.CallerOk then
        try
          discard <| runOn g (do evalTactic (← `(tactic| first
            | assumption
            | exact FnSigEx.CallerOk.each (by assumption) _)))
        catch _ =>
          throwError "`ret` needs the caller's requirement (`sig.CallerOk …`) among the hypotheses"
      else if t.isAppOf ``Sub then
        left := left ++ (← runOn g (do evalTactic (← `(tactic| ty_sub))))
      else if t.isAppOf ``Eq then
        try
          discard <| deep <| runOn g (do evalTactic (← `(tactic| first
            | rfl
            | exact FnSig.CallerOk.owned_back (by assumption) rfl
            | exact FnSigEx.CallerOk.owned_back (by assumption) _ rfl)))
        catch _ =>
          throwError "`ret`: the blocks owned here are not the ones the function gives back, \
            followed by the caller's own; a function must hand back what its signature says \
            and dispose of anything else it took"
      else if ← isProp t then
        left := left ++ (← runOn g (do evalTactic (← `(tactic| sub_regs))))
    return .done left
  | .jcc _ _ =>
    -- First try to end the block here, with the next instruction at a label.
    let before ← saveState
    try
      let gs ← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.last (by ty_fetch) (HasType.jcc ?dec ?taken ?fall))))
      let dec ← goalNamed gs `dec
      let taken ← goalNamed gs `taken
      let fall ← goalNamed gs `fall
      discard <| runOn dec decideCond
      let [takenAcc] ← runOn taken introBranch | throwError "unexpected goals"
      let leftTaken ← proveAccepts takenAcc
      let [fallAcc] ← runOn fall introBranch | throwError "unexpected goals"
      let leftFall ← proveAccepts fallAcc
      return .done (leftTaken ++ leftFall)
    catch _ =>
      before.restore
    -- Otherwise the block continues after the jump.
    let gs ← runOn goal (do evalTactic (← `(tactic| refine BlockOk.branch (by ty_fetch) ?dec ?taken ?rest)))
    let dec ← goalNamed gs `dec
    let taken ← goalNamed gs `taken
    let rest ← goalNamed gs `rest
    try
      discard <| runOn dec decideCond
    catch _ =>
      throwError "`{instr.toAsm}`: the flags known here do not decide the condition"
    let [takenAcc] ← runOn taken introBranch | throwError "unexpected goals"
    -- A side that the exactly known flags rule out needs nothing more.
    let leftTaken ← if ← closeIfImpossible takenAcc then pure [] else proveAccepts takenAcc
    let [rest'] ← runOn rest introBranch | throwError "unexpected goals"
    if ← closeIfImpossible rest' then return .done leftTaken
    let [rest''] ← runOn rest' (do evalTactic (← `(tactic| ty_normalize)))
      | throwError "unexpected goals"
    return .continues rest'' leftTaken
  | .jmp (.ind _) =>
    let before ← saveState
    -- a tail call through a function pointer, on behalf of this function's caller
    let tail? ← try
        let gs ← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last (by ty_fetch) (HasType.jmpFn (sig := ?_) (saved := ?_) (ret := ?_)
            (rest := ?_) (room := ?_) ?fn ?caller ?sub))))
        discard <| runOn (← goalNamed gs `fn) (do evalTactic (← `(tactic| ty_operand)))
        discard <| runOn (← goalNamed gs `caller) (do evalTactic (← `(tactic| assumption)))
        let left ← runOn (← goalNamed gs `sub) (do evalTactic (← `(tactic| ctx_sub)))
        pure (some left)
      catch _ =>
        before.restore
        pure none
    if let some left := tail? then return .done left
    let gs ← runOn goal (do evalTactic (← `(tactic|
      refine BlockOk.last (by ty_fetch) (HasType.jmpInd (Δ := ?_) ?code ?sub))))
    let code ← goalNamed gs `code
    let sub ← goalNamed gs `sub
    try
      discard <| runOn code (do evalTactic (← `(tactic| ty_operand)))
    catch _ =>
      throwError "`{instr.toAsm}`: the operand does not hold a pointer to code here. A register \
        holding the exact address of a label becomes one with `ty_fn_ptr` (a function) or \
        `ty_code_ptr` (any other label)"
    let left ← try
        runOn sub (do evalTactic (← `(tactic| ctx_sub)))
      catch _ =>
        throwError "`{instr.toAsm}`: the stack, the free room or the flags do not match what \
          the target expects"
    rejectImpossible left
    return .done left
  | .ud2 =>
    -- Reached only if no state matches the context; that is left to prove
    -- unless the flags predicate is plainly unsatisfiable.
    let hstate := mkIdent `hstate
    let gs ← runOn goal (do evalTactic (← `(tactic|
      (refine BlockOk.last (by ty_fetch) (HasType.unreachable ?_)
       intro _ _ _ _ _ $hstate:ident
       first | exact ($hstate).flags | skip))))
    return .done gs
  | .call _ =>
    return .needsHelp m!"`{instr.toAsm}`: a call needs the callee's signature; use `ty_call <signature>`"
  | _ =>
    return .needsHelp m!"`{instr.toAsm}` is not handled by `ty_block`"

/-- Types a conditional jump in the middle of a block. The side that jumps
is settled as `ty_block` would settle it; the side that carries on is left
as the goal, so that something can be said about it before going further. -/
elab "ty_branch" : tactic => do
  let others := (← getGoals).drop 1
  let saved ← saveState
  match ← typeStep with
  | .endOfBlock instr =>
    let goal ← getMainGoal
    match ← finishBlock goal instr with
    | .done l => setGoals (l ++ others)
    | .continues rest l => setGoals (rest :: l ++ others)
    | .needsHelp m => throwError m
  | .stepped =>
    saved.restore
    throwError "ty_branch: the instruction here does not transfer control; use `ty_step`"
  | .notABlock => throwError "ty_branch: the goal is not a block"

/-- Types a whole block of a labelled program: the straight-line
instructions, then the control transfer that ends it. Jump targets are found
by label. Conditional jumps in the middle of the block are followed.

Goals are left for whatever needs an argument: facts a target context
demands (with the branch condition available as `hcond`), and register types
that do not obviously match. The tactic stops at a `call`, which needs
`ty_call`. -/
elab "ty_block" : tactic => do
  let others := (← getGoals).drop 1
  let mut left : List MVarId := []
  repeat
    let mut endInstr? : Option Instr := none
    repeat
      match ← typeStep with
      | .stepped => continue
      | .endOfBlock instr => endInstr? := some instr; break
      | .notABlock => break
    let some instr := endInstr? | break
    let goal ← getMainGoal
    match ← finishBlock goal instr with
    | .done l =>
      left := left ++ l
      setGoals []
      break
    | .continues rest l =>
      left := left ++ l
      setGoals [rest]
    | .needsHelp _ => break
  setGoals ((← getGoals) ++ left ++ others)

/-- `ty_call sig` types a `call` that ends a block, to a function with
signature `sig`. The callee and the return point are found by label. Left as
goals: argument registers whose types do not obviously match what the
function expects, and register types after the return that do not obviously
match the return point's context. -/
elab "ty_call " sig:term : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  -- Find the instruction, to tell a direct call from an indirect one.
  let parts ← try
      runOn goal (do evalTactic (← `(tactic| refine BlockOk.last (by ty_fetch) ?typed)))
    catch _ => throwError "ty_call: the goal is not a block with an instruction at its address"
  let typed ← goalNamed parts `typed
  let typedTy ← instantiateMVars (← typed.getType)
  let instr? ← knownInstr typedTy.getAppArgs[6]!
  let ctx := typedTy.getAppArgs[5]!
  let noRoom (instr : Instr) : TacticM MessageData := do
    let room ← typed.withContext do ppClean (← reduce (← mkAppM ``CtxOf.room #[ctx]))
    return m!"`{instr.toAsm}`: there is no room on the stack for the return address: the \
      context has room for {room}"
  -- A call through an operand holding a function pointer is typed like a
  -- direct call to that function.
  let viaPointer? ← match instr? with
    | some (.call (.ind _)) =>
      let before ← saveState
      try
        let gs ← runOn typed (do evalTactic (← `(tactic|
          refine HasType.callFn (sig := $sig) (ret := ?_) ?callee rfl ?retpoint ?args ?sp ?back
            ?need ?gives ?own)))
        discard <| runOn (← goalNamed gs `callee) (do evalTactic (← `(tactic| ty_operand)))
        pure (some gs)
      catch _ =>
        before.restore
        pure none
    | _ => pure none
  match instr? with
  | some (.call (.rel _)) => pure ()
  | some (.call (.ind rm)) =>
    if viaPointer?.isNone then
      let instr := Instr.call (.ind rm)
      -- Otherwise the operand may hold a pointer to code expecting one context.
      let gs ← try
          runOn typed (do evalTactic (← `(tactic|
            refine FnSig.callInd_ok (sig := $sig) (saved := ?_) (ret := ?_) (rest := ?_)
              ?callee rfl ?retpoint ?args ?sp ?stack ?own)))
        catch _ => throwError (← noRoom instr)
      let callee ← goalNamed gs `callee
      try
        discard <| runOn callee (do evalTactic (← `(tactic| ty_operand)))
      catch _ =>
        throwError "`{instr.toAsm}`: the operand does not hold a pointer to a function with this \
          signature, or there is no room on the stack for the return address. A register \
          holding the exact address of a function becomes a pointer to it with `ty_fn_ptr`"
      let mut left : List MVarId := []
      left := left ++ (← proveAtLabel (← goalNamed gs `retpoint) (pure []))
      left := left ++ (← runOn (← goalNamed gs `args) (do evalTactic (← `(tactic| sub_regs))))
      left := left ++ (← runOn (← goalNamed gs `sp) (do evalTactic (← `(tactic| ty_sub))))
      let stack ← goalNamed gs `stack
      let stackLeft ← try
          runOn stack (do evalTactic (← `(tactic| ty_stack)))
        catch _ => pure [stack]
      unless stackLeft.isEmpty do
        throwError "`{instr.toAsm}`: the stack here does not match the one the function pointer \
          expects"
      try
        discard <| runOn (← goalNamed gs `own) (do evalTactic (← `(tactic| rfl)))
      catch _ =>
        throwError "ty_call: the blocks owned here are not the ones owned at the return point"
      setGoals (left ++ others)
      return
  | some instr => throwError "ty_call: the instruction here is `{instr.toAsm}`, not a call"
  | none => throwError "ty_call: the instruction at this address is not known"
  let gs ← match viaPointer? with
    | some gs => pure gs
    | none =>
      try
        runOn typed (do evalTactic (← `(tactic|
          refine FnSig.call_ok (sig := $sig) (ret := ?_) ?callee rfl ?retpoint ?args ?sp ?back
            ?need ?gives ?own)))
      catch _ => throwError (← noRoom (instr?.getD .nop))
  let mut left : List MVarId := []
  -- the callee first: it involves no unknowns
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``FnSig.At then
      let [entry] ← runOn g (do evalTactic (← `(tactic| intro _ _ _ _ hK)))
        | throwError "ty_call: unexpected goals"
      left := left ++ (← proveAtLabel entry (pure []))
  -- then the return point, which fixes the context after the call
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if !(← isProp t) then continue
    if t.isAppOf ``FnSig.At || t.isAppOf ``CtxSub || t.isForall || t.isAppOf ``LE.le ||
        t.isAppOf ``Sub || t.isAppOf ``Eq then continue
    left := left ++ (← proveAtLabel g (pure []))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``CtxSub then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| ctx_sub))))
    else if t.isAppOf ``Eq then
      try
        discard <| deep <| runOn g (do evalTactic (← `(tactic| rfl)))
      catch _ =>
        throwError "ty_call: the blocks owned do not match. Those owned here must be the \
          ones the function takes, in its order, then any others; and the return point must \
          own the ones the function gives, then those others"
    else if t.isForall then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| sub_regs))))
    else if t.isAppOf ``Sub then
      left := left ++ (← runOn g (do evalTactic (← `(tactic| ty_sub))))
    else if t.isAppOf ``LE.le then
      -- The stack the function needs is a field of its signature: the
      -- signature is unfolded so that arithmetic can see the number.
      let sigName? := (t.appFn!.appArg!.getAppArgs.back?.bind (·.getAppFn.constName?))
      let after ← try
          runOn g (do evalTactic (← `(tactic| first | decide | omega)))
        catch e =>
          match sigName? with
          | some c =>
            try
              runOn g (do evalTactic (← `(tactic|
                (unfold $(mkIdent c); dsimp only; first | decide | omega))))
            catch _ => throw e
          | none => throw e
      left := left ++ after
  setGoals (left ++ others)

/-- `ty_call sig returning ret` types a `call` that ends a block, direct or
through a pointer, to
a function whose signature `sig : FnSigEx` has results that depend on a
value the function chooses as it returns: typically the address of a block
it made. `ret` gives the context at the instruction after the call for each
such value, and the label there must allow all of them. -/
elab "ty_call " sig:term " returning " ret:term : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  -- directly, or through an operand that holds a pointer to the function
  let (gs, direct) ← try
      pure (← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.last (by ty_fetch)
          (FnSigEx.call_ok (sig := $sig) (ret := $ret) (frame := ?_) ?callee rfl ?retpoint ?args
            ?sp ?back ?need ?own ?gives ?frame)))), true)
    catch _ =>
      try
        pure (← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.last (by ty_fetch)
            (HasType.callFnAll (sig := $sig) (ret := $ret) (frame := ?_) ?callee rfl ?retpoint
              ?args ?sp ?back ?need ?gives ?frame ?own)))), false)
      catch _ =>
        throwError "ty_call: the instruction here must be a call, with room on the stack for \
          the return address"
  let mut left : List MVarId := []
  if direct then
    let [entry] ← runOn (← goalNamed gs `callee) (do evalTactic (← `(tactic| intro _ _ _ _ _ hK)))
      | throwError "ty_call: unexpected goals"
    left := left ++ (← proveAtLabel entry (pure []))
  else
    try
      discard <| runOn (← goalNamed gs `callee) (do evalTactic (← `(tactic| ty_operand)))
    catch _ =>
      throwError "ty_call: the operand does not hold a pointer to a function with this \
        signature. A register holding the exact address of a function becomes a pointer to \
        it with `ty_fn_ptr`"
  let [back] ← runOn (← goalNamed gs `retpoint) (do evalTactic (← `(tactic| intro x)))
    | throwError "ty_call: unexpected goals"
  left := left ++ (← proveAtLabel back (pure []))
  left := left ++ (← runOn (← goalNamed gs `args) (do evalTactic (← `(tactic| sub_regs))))
  left := left ++ (← runOn (← goalNamed gs `sp) (do evalTactic (← `(tactic| ty_sub))))
  try
    discard <| deep <| runOn (← goalNamed gs `own) (do evalTactic (← `(tactic| rfl)))
    discard <| deep <| runOn (← goalNamed gs `gives) (do evalTactic (← `(tactic| (intro x; rfl))))
    discard <| deep <| runOn (← goalNamed gs `frame) (do evalTactic (← `(tactic| (intro x; rfl))))
  catch _ =>
    throwError "ty_call: the blocks owned do not match. Those owned here must be the ones \
      the function takes, in its order, then any others; and whatever value the function \
      chooses, the return point must own the ones the function gives, then those others"
  left := left ++ (← runOn (← goalNamed gs `back) (do evalTactic (← `(tactic| (intro x; ctx_sub)))))
  left := left ++ (← runOn (← goalNamed gs `need) (do evalTactic (← `(tactic| first | decide | omega))))
  setGoals (left ++ others)

/-- `ty_return_as x`: the function's return address is ready for a family of
contexts, and the function has decided it returns into the one for `x`. From
here on the return address is typed as code for that context alone, which is
what `ret` needs. -/
elab "ty_return_as " x:term : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  for i in [0:16] do
    let saved ← saveState
    try
      setGoals [goal]
      let iq := Syntax.mkNumLit (toString i)
      Tactic.withoutRecover do
        evalTactic (← `(tactic| refine BlockOk.chooseRet (i := $iq) $x rfl ?_))
      evalTactic (← `(tactic| ty_normalize))
      setGoals ((← getGoals) ++ others)
      return
    catch _ => saved.restore
  throwError "ty_return_as: there is no return address ready for a family of contexts on the \
    stack here"

/-- `ty_code_ptr r to Δ`: register `r` holds exactly the address of a label
that allows context `Δ`; from here on it is a pointer to code expecting `Δ`,
which can be stored, jumped through or called through. What the label
demands of `Δ`, such as a function's requirement on its caller, is proved
where it is routine and otherwise left as goals. -/
elab "ty_code_ptr " r:term " to " Δ:term : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  let gs ← try
      runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.codePtr (r := $r) (Δ := $Δ) ?ne rfl ?here ?rest)))
    catch _ =>
      throwError "ty_code_ptr: the register does not hold an exactly known address here"
  discard <| runOn (← goalNamed gs `ne) (do evalTactic (← `(tactic| decide)))
  let mut left : List MVarId := []
  for g in ← proveAtLabel (← goalNamed gs `here) (pure []) do
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``FnSig.CallerOk then
      let parts ← runOn g (do evalTactic (← `(tactic| refine FnSig.CallerOk.mk ?gives ?ret ?room)))
      for p in parts do
        let after ← try
            runOn p (do evalTactic (← `(tactic| first | rfl | ctx_sub | decide | omega)))
          catch _ => pure [p]
        left := left ++ after
    else left := left ++ [g]
  setGoals [← goalNamed gs `rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left ++ others)

/-- `ty_fn_ptr r to sig`: register `r` holds exactly the address of a
function with signature `sig`; from here on it is a pointer to that function,
which can be stored, passed on, and called by any caller. -/
elab "ty_fn_ptr " r:term " to " sig:term : tactic => do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  -- a signature of either kind: plain, or with results chosen at the return
  let (gs, chosen) ← try
      pure (← runOn goal (do evalTactic (← `(tactic|
        refine BlockOk.fnPtr (r := $r) (sig := $sig) ?ne rfl ?here ?rest))), false)
    catch _ =>
      try
        pure (← runOn goal (do evalTactic (← `(tactic|
          refine BlockOk.fnPtrAll (r := $r) (sig := $sig) ?ne rfl ?here ?rest))), true)
      catch _ =>
        throwError "ty_fn_ptr: the register does not hold an exactly known address here"
  discard <| runOn (← goalNamed gs `ne) (do evalTactic (← `(tactic| decide)))
  let [entry] ← runOn (← goalNamed gs `here) (do
      if chosen then evalTactic (← `(tactic| intro _ _ _ _ _ hK))
      else evalTactic (← `(tactic| intro _ _ _ _ hK)))
    | throwError "ty_fn_ptr: unexpected goals"
  let left ← try
      proveAtLabel entry (pure [])
    catch e =>
      throwError "ty_fn_ptr: the address is not that of a function with this signature\n\
        {e.toMessageData}"
  setGoals [← goalNamed gs `rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ left ++ others)

/-- Types an `mmap` at the head of a block goal with the given lemma applied
to the layout asked for, and proves what it needs of the registers. -/
private def typeMmap (rule : TSyntax `term) : TacticM Unit := do
  let goal ← getMainGoal
  let others := (← getGoals).drop 1
  setGoals [goal]
  try
    evalTactic (← `(tactic| refine BlockOk.sys (by ty_fetch) $rule ?_))
  catch _ =>
    throwError "`mmap` is system call 9 of the Linux model: `rax` must hold exactly 9"
  let gs ← getGoals
  -- what the registers hold and what the kind is first: that settles the
  -- length and the fields
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        setGoals [g]
        try
          Tactic.withoutRecover do evalTactic (← `(tactic| rfl))
        catch _ =>
          let reg := (regName? (← whnf lhs.appArg!)).getD "the register"
          let actual ← g.withContext do
            let regTy ← whnf lhs
            let shown? ← if regTy.isAppOfArity ``Ty.eq 1 then
                try
                  let n ← evalAddr (← instantiateMVars regTy.appArg!)
                  pure (some s!"exactly 0x{String.ofList (Nat.toDigits 16 n)}")
                catch _ => pure none
              else pure none
            match shown? with
            | some shown => pure shown
            | none => ppTy (← reduce lhs)
          if reg == "rsi" then
            throwError "`mmap` needs the length in `rsi` to be exactly known, but its type is \
              `{actual}`"
          else if reg == "rdx" then
            throwError "`mmap` is typed only for memory to read and write: `rdx` must hold \
              exactly 3, but its type is `{actual}`"
          else
            throwError "`mmap` is typed only for private memory that is not a file: `{reg}` \
              must hold exactly 0x22, but its type is `{actual}`"
      else if lhs.isAppOf ``MemTy.kinds then
        setGoals [g]
        try
          Tactic.withoutRecover do evalTactic (← `(tactic| rfl))
        catch _ =>
          throwError "`mmap`: the memory typing declares no kind {lhs.appArg!}"
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else
      setGoals [g]
      try
        Tactic.withoutRecover do
          evalTactic (← `(tactic| first
            | decide
            | rfl
            | (refine ShapeOf.fits_rep ?_ _; first | exact rfl | decide)
            | (simp only [ShapeOf.raw, ShapeOf.rep_size, List.length_cons, List.length_nil,
                List.length_replicate]; omega)
            | (simp; done)))
      catch _ =>
        if t.isAppOf ``LE.le then
          throwError "`mmap`: the block does not fit in the length in `rsi`"
        else if t.isAppOf ``LT.lt then
          throwError "`mmap`: a block needs at least one byte"
        else if t.isAppOf ``Eq && t.appFn!.appArg!.isAppOf ``ShapeOf.fits then
          throwError "`mmap`: a typed value of the new block does not lie inside it"
        else
          throwError "`mmap`: every typed value of the new block must admit zero, since \
            that is what fresh memory holds: a value that may be null"
  let some rest := rest? | throwError "ty_mmap: unexpected goals"
  setGoals [rest]
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ others)

/-- `ty_mmap shape`: the `syscall` here is an `mmap` for fresh memory, to be
used as a block of this shape. Afterwards `rax` holds an error number or a
writable pointer to the new block; `ty_err` tells them apart. -/
elab_rules : tactic
  | `(tactic| ty_mmap $shape) => do
    typeMmap (← `(linux_mmap (S := $shape) (len := ?_) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_))

/-- `ty_mmap_kind tag`: as `ty_mmap`, for a block of the declared kind
`tag`. Afterwards `rax` holds an error number or a writable pointer to a
block of that kind. -/
elab_rules : tactic
  | `(tactic| ty_mmap_kind $tag) => do
    typeMmap (← `(linux_mmap_kind (tag := $tag) (S := ?_) (len := ?_) rfl ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_))

/-- `ty_byte as b`: the instruction here loads the byte of text a register
points at. Two goals follow: the rest of the block with the byte exactly
zero, then with the byte exactly some `b` that is not zero, where the
pointer is known not to be at the end of its text and may be stepped forward
with `add r, 1`. A test of the byte then decides in each which way it goes. -/
elab_rules : tactic
  | `(tactic| ty_byte as $b) => do
    let goal ← getMainGoal
    let others := (← getGoals).drop 1
    setGoals [goal]
    try
      evalTactic (← `(tactic| refine BlockOk.strByte (by ty_fetch) ?_ ?_ ?_ rfl ?_ ?_))
    catch _ =>
      throwError "ty_byte: the instruction here must be `movzx r, byte ptr [p]` with `p` a \
        pointer into text"
    let mut blocks : List MVarId := []
    for g in ← getGoals do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      setGoals [g]
      if t.isAppOf ``BlockOk then
        evalTactic (← `(tactic| ty_normalize))
        blocks := blocks ++ (← getGoals)
      else if t.isForall then
        evalTactic (← `(tactic| (intro $b:ident hbyte hsmall; ty_normalize)))
        blocks := blocks ++ (← getGoals)
      else
        try
          evalTactic (← `(tactic| decide))
        catch _ =>
          throwError "ty_byte: the byte must go into a register other than the pointer's, \
            and neither may be `rsp`"
    setGoals (blocks ++ others)

/-- `ty_mmap_own as p`: the `syscall` here is an `mmap` for fresh memory that
the program is to own. Two goals follow: the rest of the block with an error
number in `rax`, then with `rax` holding exactly an address `p` and the
context owning the pages at `p` as a block of integers. `hpage` says `p` is
the start of a page, and `hlow` that it is not an error number. -/
elab_rules : tactic
  | `(tactic| ty_mmap_own as $p) => do
    let goal ← getMainGoal
    let others := (← getGoals).drop 1
    setGoals [goal]
    try
      evalTactic (← `(tactic|
        refine BlockOk.mmapOwn (len := ?_) (size := ?_) (by ty_fetch) rfl ?_ ?_ ?_ ?_ ?_ ?_))
    catch _ =>
      throwError "`mmap` is system call 9 of the Linux model: `rax` must hold exactly 9"
    let gs ← getGoals
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if let some (_, lhs, _) := t.eq? then
        if lhs.isAppOf ``CtxOf.regs then
          setGoals [g]
          try
            Tactic.withoutRecover do evalTactic (← `(tactic| rfl))
          catch _ =>
            throwError "`mmap` needs an exactly known length in `rsi`, 3 in `rdx` (read and \
              write) and 0x22 in `r10` (private memory, not a file)"
    -- how many fields the pages make, worked out as a number
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if let some (_, lhs, rhs) := t.eq? then
        if lhs.isMVar then
          let v ← g.withContext do reduce (← instantiateMVars rhs)
          lhs.mvarId!.assign v
          g.assign (← mkEqRefl v)
    let mut blocks : List MVarId := []
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isForall then
        setGoals [g]
        if t.bindingBody!.bindingDomain!.isAppOf ``SysErr then
          evalTactic (← `(tactic| (intro e herr; ty_normalize)))
        else
          evalTactic (← `(tactic| (intro $p:ident hpage hlow; ty_normalize)))
        blocks := blocks ++ (← getGoals)
    setGoals (blocks ++ others)

/-- Among the goals a rule about an owned block leaves, settles by
computation those that say what a register holds, then those that look the
block up. The order matters: the first fix the address the second look for. -/
private def closeLookups (gs : List MVarId) : TacticM Unit := do
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``CtxOf.regs then
        setGoals [g]
        Tactic.withoutRecover do evalTactic (← `(tactic| rfl))
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if let some (_, lhs, _) := t.eq? then
      if lhs.isAppOf ``GetElem?.getElem? || lhs.isAppOf ``MemTy.kinds then
        setGoals [g]
        Tactic.withoutRecover do evalTactic (← `(tactic| rfl))

/-- How many blocks a list of owned blocks has, as far as it is written out. -/
private def ownedCount (owned : Expr) : MetaM Nat := do
  let mut e ← whnf owned
  let mut n := 0
  while e.isAppOfArity ``List.cons 3 do
    n := n + 1
    e ← whnf e.appArg!
  return n

/-- How many blocks the context of the block goal owns. -/
private def ownedCountHere : TacticM Nat := withMainContext do
  let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless t.isAppOfArity ``BlockOk 6 do return 0
  ownedCount (← mkAppM ``CtxOf.owned #[t.appArg!])

/-- Closes the goal with the tactic made for one of the places `0` to
`count - 1`, the first that works. -/
private def tryPlaces (count : Nat) (mk : Nat → TacticM (TSyntax `tactic)) : TacticM Unit :=
  deep do
  let goal ← getMainGoal
  for k in [0:count] do
    let saved ← saveState
    try
      setGoals [goal]
      Tactic.withoutRecover do evalTactic (← mk k)
      if (← getGoals).isEmpty then return
      saved.restore
    catch _ => saved.restore
  throwError "no owned block fits"

/-- The list of owned blocks a goal about one of them is stated for: its
first explicit argument. -/
private def ownedOfGoal : TacticM Expr := withMainContext do
  let t ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  let some owned := t.getAppArgs[0]? | throwError "not a goal about an owned block"
  return owned

elab_rules : tactic
  | `(tactic| ty_owned_at) => do
    tryPlaces (← ownedCount (← ownedOfGoal)) fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine' OwnedAt.of_inside (k := $kq) ?entry ?addr ?inside
          case entry => rfl
          case addr =>
            -- matched as written: comparing two addresses by working them out
            -- is slow, and settles nothing when one is not known
            with_reducible first
            | rfl
            | exact BitVec.add_assoc _ _ _
            | exact OwnedAt.addr_sub _ _ _
            | exact OwnedAt.addr_sub' _ _ _ _
          case inside => ty_inside))
  | `(tactic| ty_owned_byte) => do
    tryPlaces (← ownedCount (← ownedOfGoal)) fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine' OwnedByte.mk (k := $kq) ?entry ?addr ?fit
          case entry => rfl
          case addr =>
            first
            | exact owned_addrScaled _ _ _ _ (by decide)
            | exact owned_addr0 _
            | exact owned_addrOff _ _
          case fit => ty_inside))

/-- A list with its spine written out as far as it can be worked out. -/
private partial def spineOf (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  if e'.isAppOfArity ``List.cons 3 then
    return mkApp3 e'.appFn!.appFn!.appFn! e'.appFn!.appFn!.appArg! e'.appFn!.appArg!
      (← spineOf e'.appArg!)
  if e'.isAppOfArity ``List.nil 1 then return e'
  return e

/-- How many pieces of a stack are written out. -/
private def stackCount (σ : Expr) : MetaM Nat := do
  return (← consElems σ).1.size

elab_rules : tactic
  | `(tactic| ty_stack_at) => withMainContext do
    let t := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
    unless t.isAppOfArity ``StackAt 5 do throwError "not a goal about the stack"
    -- the stack written out piece by piece, where a definition stood in for it
    let σ ← spineOf t.getAppArgs[0]!
    replaceMainGoal [← (← getMainGoal).replaceTargetDefEq (mkAppN t.getAppFn (t.getAppArgs.set! 0 σ))]
    tryPlaces (← stackCount σ) fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine' StackAt.of_inside (k := $kq) ?entry ?off ?inside
          case entry => exact rfl
          case off =>
            first
            | (refine stackAt_idx8 ?_ ?_ <;> ty_stack_in)
            | (refine stackAt_bytes ?_; ty_stack_in)
            | (refine stackAt_lit ?_; ty_stack_in)
          case inside => ty_stack_in))

/-- `ty_name_slot d as v`: from here on, the eight bytes `d` bytes above the
stack pointer are typed as exactly the value they hold, which is called `v`. -/
elab_rules : tactic
  | `(tactic| ty_name_slot $d as $v) => withMainContext do
    let others := (← getGoals).drop 1
    setGoals [← getMainGoal]
    evalTactic (← `(tactic| ty_normalize))
    let goal ← getMainGoal
    let t := (← instantiateMVars (← goal.getType)).consumeMData
    unless t.isAppOfArity ``BlockOk 6 do throwError "ty_name_slot: the goal is not a block"
    let n ← stackCount (← mkAppM ``CtxOf.stack #[t.appArg!])
    for k in [0:n] do
      let saved ← saveState
      try
        setGoals [goal]
        let kq := Syntax.mkNumLit (toString k)
        Tactic.withoutRecover do
          evalTactic (← `(tactic| (
            refine BlockOk.nameSlotAt (k := $kq) (d := $d) rfl ?lo ?le ?rest
            case lo => ty_stack_in
            case le => ty_stack_in)))
        evalTactic (← `(tactic| (intro $v:ident; ty_normalize)))
        setGoals ((← getGoals) ++ others)
        return
      catch _ => saved.restore
    throwError "ty_name_slot: there are not eight bytes of one piece of the stack there"

/-- Applies to the block goal the first of the tactics made for the pieces
of its stack that works, leaving the rest of the block. -/
private def atStackPiece (name : String) (mk : Nat → TacticM (TSyntax `tactic))
    (failure : MessageData) : TacticM Unit := withMainContext do
  let others := (← getGoals).drop 1
  setGoals [← getMainGoal]
  evalTactic (← `(tactic| ty_normalize))
  let goal ← getMainGoal
  let t := (← instantiateMVars (← goal.getType)).consumeMData
  unless t.isAppOfArity ``BlockOk 6 do throwError "{name}: the goal is not a block"
  let n ← stackCount (← mkAppM ``CtxOf.stack #[t.appArg!])
  for k in [0:n] do
    let saved ← saveState
    try
      setGoals [goal]
      Tactic.withoutRecover do evalTactic (← mk k)
      evalTactic (← `(tactic| ty_normalize))
      setGoals ((← getGoals) ++ others)
      return
    catch _ => saved.restore
  throwError failure

/-- `ty_stack_split at d`: the piece of the stack that the byte `d` bytes
above the stack pointer is in is from here on two pieces, meeting there. An
access has to keep to one piece, so this is how part of a frame is kept to
exactly the bytes meant for it. -/
elab_rules : tactic
  | `(tactic| ty_stack_split at $d) =>
    atStackPiece "ty_stack_split" (fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine BlockOk.splitStackAt (k := $kq) (d := $d) rfl ?lo ?le ?rest
          case lo => ty_stack_in
          case le => ty_stack_in)))
      m!"ty_stack_split: no piece of the stack has that byte inside it"

/-- `ty_stack_join at d`: the two pieces of the stack that meet `d` bytes
above the stack pointer are from here on one piece. -/
elab_rules : tactic
  | `(tactic| ty_stack_join at $d) =>
    atStackPiece "ty_stack_join" (fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| (
          refine BlockOk.joinStackAt (k := $kq) (d := $d) rfl rfl ?meet ?rest
          case meet => ty_stack_in)))
      m!"ty_stack_join: no two pieces of the stack meet there"

/-- Applies a rule about the owned block at one of the places in the
context's list, whichever fits, and returns the goals it leaves. -/
private def withOwnedPlace (mk : Nat → TacticM (TSyntax `tactic)) (failure : MessageData)
    (places? : Option (List Nat) := none) : TacticM (List MVarId) := deep do
  let goal ← getMainGoal
  let places ← match places? with
    | some ps => pure ps
    | none => pure (List.range (← ownedCountHere))
  for k in places do
    let saved ← saveState
    try
      setGoals [goal]
      Tactic.withoutRecover do evalTactic (← mk k)
      let gs ← getGoals
      closeLookups gs
      return gs
    catch _ => saved.restore
  throwError failure

/-- `ty_munmap`: the `syscall` here is a `munmap` of a block the context
owns, whose address is in `rdi` and whose whole size is in `rsi`. Afterwards
the context no longer owns it. -/
elab_rules : tactic
  | `(tactic| ty_munmap) => do
    let others := (← getGoals).drop 1
    let gs ← withOwnedPlace (fun k => do
        let kq := Syntax.mkNumLit (toString k)
        `(tactic| refine BlockOk.sys (by ty_fetch)
            (linux_munmap (k := $kq) (a := ?_) (len := ?_) (S := ?_) ?_ ?_ ?_ ?_ ?_) ?_))
      m!"`munmap` is typed for a block the context owns: `rax` must hold exactly 11, `rdi` \
        exactly the address of an owned block, and `rsi` an exactly known length"
    let mut rest? : Option MVarId := none
    for g in gs do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if t.isAppOf ``BlockOk then rest? := some g
      else
        setGoals [g]
        try
          deep <| Tactic.withoutRecover do
            evalTactic (← `(tactic| first
              | (simp only [List.length_replicate, List.length_set, List.length_cons,
                  List.length_nil]; decide)
              | decide
              | (simp; done)))
        catch _ =>
          throwError "`munmap`: the length in `rsi` must cover exactly the owned block; a \
            block that was split must be joined again first, or its parts given back one by one"
    let some rest := rest? | throwError "ty_munmap: unexpected goals"
    setGoals [rest]
    evalTactic (← `(tactic| ty_normalize))
    setGoals ((← getGoals) ++ others)

/-- Freezes the owned block whose address is in a register, with the rule given. -/
private def freezeWith (mk : Nat → TacticM (TSyntax `tactic)) (name : String := "ty_freeze")
    (after : TacticM Unit := pure ()) (places : Option (List Nat) := none)
    (failure : MessageData :=
      m!"{name}: the register must hold exactly the address of a block the context owns") :
    TacticM Unit := do
  let others := (← getGoals).drop 1
  let gs ← withOwnedPlace mk failure places
  let mut rest? : Option MVarId := none
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if t.isAppOf ``BlockOk then rest? := some g
    else
      setGoals [g]
      try
        deep <| Tactic.withoutRecover do
          evalTactic (← `(tactic| first
            | decide
            | exact List.cons_ne_nil _ _
            | exact rfl
            | (simp only [ShapeOf.raw, ShapeOf.clear, ShapeOf.set, ShapeOf.take, ShapeOf.drop,
                ShapeOf.append, List.length_replicate, List.length_set, List.length_cons,
                List.length_nil, List.length_take, List.length_drop, List.length_append]
               first | decide | omega)
            | (simp; done)))
      catch _ =>
        -- a bound against a block's size is shown with the size worked out
        let t ← if t.isAppOfArity ``LE.le 4 then
            pure (mkApp (mkApp t.appFn!.appFn! (← reduce t.appFn!.appArg!)) (← reduce t.appArg!))
          else pure t
        throwError "{name}: could not show{indentExpr t}"
  let some rest := rest? | throwError "{name}: unexpected goals"
  setGoals [rest]
  after
  evalTactic (← `(tactic| ty_normalize))
  setGoals ((← getGoals) ++ others)

/-- `ty_freeze r`: register `r` holds exactly the address of a block the
context owns. From here on the block is an ordinary one that anything may
point to, of the shape it has now, and `r` is a writable pointer to it. It
can no longer be given back, nor its typed values change type. -/
elab_rules : tactic
  | `(tactic| ty_freeze $r) => do
    freezeWith fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| refine BlockOk.freeze (r := $r) (k := $kq) (w := true) (base := ?_) (S := ?_)
          ?_ ?_ ?_ ?_ ?_)

/-- `ty_freeze_kind r as tag`: as `ty_freeze`, but the block joins the
declared kind `tag`, whose shape it must have, and `r` becomes a pointer to
a block of that kind. -/
elab_rules : tactic
  | `(tactic| ty_freeze_kind $r as $tag) => do
    freezeWith fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| refine BlockOk.freezeKind (r := $r) (k := $kq) (tag := $tag) (w := true)
          (base := ?_) (S := ?_) ?_ ?_ ?_ ?_ ?_ ?_)

/-- `ty_split r at m`: register `r` holds exactly the address of a block the
context owns, of at least `m` bytes. From here on the context owns two
blocks in its place: the first `m` bytes where the block was, and the rest
`m` bytes on. Each can be stored to, frozen or given back on its own. -/
elab_rules : tactic
  | `(tactic| ty_split $r at $m) => do
    freezeWith (name := "ty_split") fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| refine BlockOk.splitOwned (r := $r) (k := $kq) (m := $m) (base := ?_) (S := ?_)
          ?_ ?_ ?_ ?_)

/-- `ty_join r`: register `r` holds exactly the address of a block the
context owns, and the context also owns the block that starts where that one
ends. From here on it owns one block in their place, with the bytes of the
first followed by those of the second. -/
elab_rules : tactic
  | `(tactic| ty_join $r) => do
    let n ← ownedCountHere
    freezeWith (name := "ty_join")
      (places := some ((List.range (n * n)).filter fun c => c / n ≠ c % n))
      (failure := m!"ty_join: the register must hold exactly the address of a block the \
        context owns, and the context must own the block that starts where that one ends")
      (fun c => do
        let k₁ := Syntax.mkNumLit (toString (c / n))
        let k₂ := Syntax.mkNumLit (toString (c % n))
        `(tactic| refine BlockOk.joinOwned (r := $r) (k₁ := $k₁) (k₂ := $k₂) (base := ?_)
            (S₁ := ?_) (S₂ := ?_) ?_ ?_ ?_ ?_ ?_ ?_))
      (do evalTactic (← `(tactic| try simp only [Nat.max_def, Nat.min_def, Nat.reduceLeDiff,
            ↓reduceIte])))

/-- `ty_loaded` proves that a starting state meets an entry contract, when
the state is one with the program loaded and `rip` set to the entry,
perhaps given a stack with arguments first: the form the simulator's
starting states have. What is left to show is settled by computing: that
each of the program's bytes is where it should be, and arithmetic about
where things are. -/
elab "ty_loaded" : tactic => withMainContext do
  let g ← getMainGoal
  let others := (← getGoals).drop 1
  let t ← whnfR (← instantiateMVars (← g.getType))
  let tac ←
    if t.isAppOf ``TypedAsm.Entry then
      `(tactic| refine Entry.ofLoad ?_ ?_ ?_ ?_ ?_ ?_)
    else if t.isAppOf ``TypedAsm.EntryArgs then
      `(tactic| refine EntryArgs.ofLoad _ ?_ ?_ ?_ ?_ ?_ ?_)
    else if t.isAppOf ``TypedAsm.EntryTexts then
      `(tactic| refine EntryTexts.ofLoad _ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    else throwError "ty_loaded: the goal is not an entry contract"
  let gs ← try runOn g (do evalTactic tac)
    catch _ =>
      throwError "ty_loaded: the state must be one with the program loaded and `rip` set to \
        its entry"
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    try
      -- that the program is in memory: each byte is looked at, by the
      -- kernel; anything else: by the kernel too
      discard <| runOn g (do evalTactic (← `(tactic|
        first
          | exact State.holds_of_check (by decide +kernel)
          | decide +kernel)))
    catch _ =>
      throwError "ty_loaded: the starting state does not meet the entry contract; this does \
        not hold:{indentExpr t}"
  setGoals others

/-- `ty_own_first r`: register `r` holds exactly the address of a block the
context owns. From here on that block is listed first among the owned ones.
The order means nothing, but a call hands a function the blocks its
signature takes from the front of the list, in the signature's order. -/
elab_rules : tactic
  | `(tactic| ty_own_first $r) => do
    freezeWith (name := "ty_own_first") fun k => do
      let kq := Syntax.mkNumLit (toString k)
      `(tactic| refine BlockOk.frontOwned (r := $r) (k := $kq) (base := ?_) (S := ?_) ?_ ?_ ?_)

/-- `ty_into h` types the instruction here and ends the block with it. Use it
when the next instruction is at a label and the block should hand over to
that label's context instead of typing the label's code a second time; `h`
is the fact that the label allows some context, as for `ty_accept`. -/
macro_rules
  | `(tactic| ty_into $h) =>
    `(tactic| (refine BlockOk.last (by ty_fetch) (HasType.straight (Γ' := ?_) ?st ?acc)
               case' st => ty_straight
               case' acc => ty_accept $h))

end TypedAsm
