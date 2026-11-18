import TypedAsm.U.Step
import TypedAsm.U.SysStep
import TypedAsm.U.Guard
import TypedAsm.U.Learn
import TypedAsm.U.PublishS
import TypedAsm.U.Laws
import TypedAsm.U.JoinS

/-!
# A block walked

The checker's step, taken instruction after instruction for as long as the
address control goes to is one written out. What comes of it is a tree of
what is left to be shown: at each instruction, that it does not fault for a
reason of its own; and where the walk stops, that the code there is typed
in the context reached, or that control arrives at a value.

A walk whose leaves hold types the block it started at.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- A point of a program at which the region a register holds the address
of becomes a block others may point into: of a shape, and of a kind if one
is given. It is so before the instruction there is run. -/
structure Pub where
  addr : BitVec 64
  base : Reg
  shape : ShapeS
  tag : Option Nat := none

/-- A program, as the checker is given it: its instructions, each with its
address and the address after it; and the shape of each kind of block its
pointers by kind refer to; and where it publishes regions. -/
structure Prog where
  code : List (BitVec 64 × Instr × BitVec 64)
  kinds : Nat → Option ShapeS := fun _ => none
  /-- The points at which a region held becomes a block others may point
  into. -/
  pubs : List Pub := []
  /-- What is always so of its static data: of addresses written out, that
  they point into blocks of given shapes, or to text. -/
  statics : List (Val × TyS) := []
  /-- Whether a context reached at a system call is seen to meet what the
  system asks for the call to be let through. A system that lets every call
  through asks nothing. -/
  pre : CtxS → Bool := fun _ => true
  /-- The functions its author defines, by number: what each gives of two
  values. -/
  fns : Nat → BitVec 64 → BitVec 64 → BitVec 64 := fun _ _ _ => 0
  /-- What its author has proved of them: terms that are the same value. -/
  laws : List LawS := []

instance : Coe (List (BitVec 64 × Instr × BitVec 64)) Prog := ⟨fun c => { code := c }⟩

/-- What a walk through a block leaves to be shown. -/
inductive Walk
  /-- The walk stopped at an address, in a context: the code there is to be
  typed in it. -/
  | stop (a : BitVec 64) (Γ : CtxS)
  /-- Control goes to a value, in a context: it is to arrive there. -/
  | arrive (t : Val) (Γ : CtxS)
  /-- An instruction was stepped over, from a context, the name `k` standing
  for whatever it read that the context did not say: it does not fault of
  itself, and the rest holds whatever `k` stands for. -/
  | step (i : Instr) (Γ : CtxS) (next : BitVec 64) (k : Nat) (rest : Walk)
  /-- A system call that returns was stepped over, the name `k` standing for
  what it hands back: the rest holds whatever that is. -/
  | sys (k : Nat) (rest : Walk)
  /-- A system call that returns in one of two ways was stepped over, the
  name `k` standing for what it hands back: each way holds, whatever that
  is. Each way's context says what range the value handed back lies in, so
  that a program's own test of it tells the two apart. -/
  | sys2 (k : Nat) (a b : Walk)
  /-- A system call ends the program: nothing is left. -/
  | ends
  /-- Control goes one of two ways, as a condition on some flags is: the
  flags decide the condition, and each way holds where they send control
  that way. -/
  | branch (c : Cond) (fl : FlagsT) (taken fall : Walk)
  /-- The context reached is one no state matches: nothing is left. -/
  | vacuous

/-- What a walk leaves to be shown, of what its terms stand for: `P` of
where it stopped, `A` of where control goes to a value. -/
def Walk.holds (P A : BitVec 64 → Ctx → Prop) : Walk → Env → Prop
  | .stop a Γ, ρ => P a (Γ.den ρ)
  | .arrive t Γ, ρ => A (t.den ρ) (Γ.den ρ)
  | .step _ _ _ k rest, ρ => ∀ x, rest.holds P A (ρ.setVal k x)
  | .sys k rest, ρ => ∀ x y, rest.holds P A (ρ.setSys k x y)
  | .sys2 k a b, ρ => ∀ x y, a.holds P A (ρ.setSys k x y) ∧ b.holds P A (ρ.setSys k x y)
  | .ends, _ => True
  | .branch c fl taken fall, ρ =>
    (∃ b, c.eval (fl.den ρ) = some b) ∧
    (c.eval (fl.den ρ) = some true → taken.holds P A ρ) ∧
    (c.eval (fl.den ρ) = some false → fall.holds P A ρ)
  | .vacuous, _ => True

/-- Whether the walk got anywhere: it stepped over an instruction or a call,
or the program ended. -/
def Walk.moved : Walk → Bool
  | .step .. | .sys .. | .sys2 .. | .ends | .branch .. | .vacuous => true
  | _ => false

/-- `PreSound D pre`: wherever `pre` says a context meets what the system
asks, every state matching it does. -/
def PreSound (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (D : SysDesc) (pre : CtxS → Bool) : Prop :=
  ∀ (Γ : CtxS) (ρ : Env), pre Γ = true → PreAt fetch sys Ψ D (Γ.den ρ)

/-- A system that lets every call through is met by any context. -/
theorem PreSound.all {D : SysDesc} (h : ∀ s, D.pre s) (pre : CtxS → Bool) :
    PreSound fetch sys Ψ D pre := fun _ _ _ _ _ _ _ s _ => h s

/-- A context may be regarded as itself after nothing is published. -/
theorem Publishes.refl (Γ : Ctx) : Publishes fetch sys Ψ Γ Γ :=
  fun _ Ψ' _ hwf _ hw => ⟨Ψ', MemTy.Ext.refl Ψ', hwf, hw⟩

theorem Publishes.trans {Γ Δ Θ : Ctx} (h₁ : Publishes fetch sys Ψ Γ Δ)
    (h₂ : ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Publishes fetch sys Ψ' Δ Θ) : Publishes fetch sys Ψ Γ Θ :=
  fun k Ψ' he hwf s hw => by
    obtain ⟨Ψ₂, he₂, hwf₂, hw₂⟩ := h₁ k Ψ' he hwf s hw
    obtain ⟨Ψ₃, he₃, hwf₃, hw₃⟩ := h₂ Ψ₂ (he.trans he₂) k Ψ₂ (MemTy.Ext.refl _) hwf₂ s hw₂
    exact ⟨Ψ₃, he₂.trans he₃, hwf₃, hw₃⟩

/-- A context regarded as another is that other with the memory typing as
it is. -/
theorem Publishes.of_regards {Γ Δ : Ctx} (h : Regards fetch sys Ψ Γ Δ) :
    Publishes fetch sys Ψ Γ Δ :=
  fun k Ψ' he hwf s hw => ⟨Ψ', MemTy.Ext.refl Ψ', hwf, h k Ψ' he hwf s hw⟩

/-- The context at an address once what the program publishes there is
published: as it was, where it publishes nothing there. Nothing where the
region is not as the program says. -/
def pubOnly (pg : Prog) (k : Nat) (a : BitVec 64) (Γ : CtxS) : Option CtxS :=
  match pg.pubs.find? fun p => p.addr = a with
  | none => some Γ
  | some p =>
    match publishS pg.kinds Γ (Γ.regs.get p.base) p.shape p.tag with
    | some Γ' => if Γ'.under k then some Γ' else none
    | none => none

theorem pubOnly_sound {ρ : Env} {pg : Prog} (hk : KindsOk Ψ pg.kinds) {k : Nat} {a : BitVec 64}
    {Γ Γ' : CtxS} (h : pubOnly pg k a Γ = some Γ') (hu : Γ.under k = true) :
    Γ'.under k = true ∧ Publishes fetch sys Ψ (Γ.den ρ) (Γ'.den ρ) := by
  unfold pubOnly at h
  split at h
  · cases h; exact ⟨hu, Publishes.refl _⟩
  · split at h
    · next Γp hp =>
      split at h
      · next hup => cases h; exact ⟨hup, publishS_sound hk hp⟩
      · cases h
    · cases h

/-- A context about to give memory back, with the region the memory is of
taken as its parts: what comes before the memory, the memory, and what
comes after. Nothing where the call is not one that gives memory back, or
no region held has the memory in it. -/
def splitCand (Γ : CtxS) : Option CtxS :=
  match Γ.regs.rax.lit?, Γ.regs.rsi.lit? with
  | some nr, some len =>
    match linuxKind nr with
    | some .unmap =>
      match hostExtent Γ.known Γ.regs.rdi (litNat (pages len)) Γ.held with
      | some (j, o, G) =>
        match Γ.held[j]? with
        | some g =>
          some { Γ with held := Γ.held.eraseIdx j ++
            ([(.lit 0, o), (o, litNat (pages len)),
              (o.plus (litNat (pages len)), offTerm G.size (o.plus (litNat (pages len))))].filter
              fun x => !x.2.same (.lit 0)).map (stretch Γ.known g) }
        | none => none
      | none => none
    | _ => none
  | _, _ => none

/-- The same, where the context may be regarded so; else the context. -/
def splitFor (Γ : CtxS) (k : Nat) : CtxS :=
  match splitCand Γ with
  | some Γ' => if Γ'.under k && regardS noEnt Γ Γ' then Γ' else Γ
  | none => Γ

theorem splitFor_sound (ρ : Env) (Γ : CtxS) {k : Nat} (hu : Γ.under k = true) :
    (splitFor Γ k).under k = true ∧
      Regards fetch sys Ψ (Γ.den ρ) ((splitFor Γ k).den ρ) := by
  unfold splitFor
  split
  · split
    · next h =>
      rw [Bool.and_eq_true] at h
      exact ⟨h.1, regardS_sound noEnt_sound ρ h.2⟩
    · exact ⟨hu, Regards.refl _⟩
  · exact ⟨hu, Regards.refl _⟩

/-- **The context made ready at an address**: what the program publishes
there published; and, at a system call, a region that memory is to be
given back out of taken as its parts. -/
def pubAt (pg : Prog) (k : Nat) (a : BitVec 64) (Γ : CtxS) : Option CtxS :=
  match pubOnly pg k a Γ with
  | some Γ' =>
    match pg.code.find? fun e => e.1 = a with
    | some e => if e.2.1 = .syscall then some (splitFor Γ' k) else some Γ'
    | none => some Γ'
  | none => none

/-- A table from numbers to numbers, by the bits of the number asked for,
the lowest first. -/
inductive Trie
  | nil
  | node (v : Option Nat) (zero one : Trie)

/-- What is at a number, in at most so many bits. -/
def Trie.find : Trie → Nat → Nat → Option Nat
  | .nil, _, _ => none
  | .node v _ _, 0, _ => v
  | .node v zero one, f + 1, k =>
    if k = 0 then v else if k % 2 = 0 then zero.find f (k / 2) else one.find f (k / 2)

/-- The table with a number put at another, unless something is there. -/
def Trie.put : Trie → Nat → Nat → Nat → Trie
  | .nil, 0, _, x => .node (some x) .nil .nil
  | .node v zero one, 0, _, x => .node (v.or (some x)) zero one
  | t, f + 1, k, x =>
    match t with
    | .nil =>
      if k = 0 then .node (some x) .nil .nil
      else if k % 2 = 0 then .node none (Trie.put .nil f (k / 2) x) .nil
      else .node none .nil (Trie.put .nil f (k / 2) x)
    | .node v zero one =>
      if k = 0 then .node (v.or (some x)) zero one
      else if k % 2 = 0 then .node v (zero.put f (k / 2) x) one
      else .node v zero (one.put f (k / 2) x)

/-- A table of each of some addresses, with how far along the list it is. -/
def Trie.ofAddrs : List (BitVec 64) → Nat → Trie → Trie
  | [], _, t => t
  | a :: rest, i, t => Trie.ofAddrs rest (i + 1) (t.put 64 a.toNat i)

/-- Whether an address is one of a table's. -/
def Trie.has (t : Trie) (a : BitVec 64) : Bool := (t.find 64 a.toNat).isSome

/-- **A program's instructions, to be found quickly**: in order, each to be
had by how far along it is; and a table from an address to how far along
the first instruction there is. It is made once for a program. -/
structure Index where
  arr : Array (BitVec 64 × Instr × BitVec 64)
  byAddr : Trie

/-- The index of a program's instructions. -/
def Prog.index (pg : Prog) : Index :=
  ⟨pg.code.toArray, Trie.ofAddrs (pg.code.map (·.1)) 0 .nil⟩

/-- **The instruction at an address, and how far along the next is**: the
one at `hint` where that is it, which it is where one instruction follows
another; else found by the table. Either way it is looked at, and taken
only if it is at the address. -/
def seek (ix : Index) (hint : Nat) (a : BitVec 64) :
    Option ((BitVec 64 × Instr × BitVec 64) × Nat) :=
  match (match ix.arr[hint]? with
    | some e => if e.1 = a then some (e, hint + 1) else none
    | none => none) with
  | some r => some r
  | none =>
    match ix.byAddr.find 64 a.toNat with
    | some i =>
      match ix.arr[i]? with
      | some e => if e.1 = a then some (e, i + 1) else none
      | none => none
    | none => none

theorem seek_spec {ix : Index} {hint : Nat} {a : BitVec 64}
    {e : BitVec 64 × Instr × BitVec 64} {h' : Nat} (h : seek ix hint a = some (e, h')) :
    e ∈ ix.arr ∧ e.1 = a := by
  unfold seek at h
  split at h
  · next r hr =>
    cases h
    split at hr
    · next e₀ he₀ =>
      split at hr
      · next hea => cases hr; exact ⟨Array.mem_of_getElem? he₀, hea⟩
      · cases hr
    · cases hr
  · split at h
    · next i _ =>
      split at h
      · next e₀ he₀ =>
        split at h
        · next hea => cases h; exact ⟨Array.mem_of_getElem? he₀, hea⟩
        · cases h
      · cases h
    · cases h

/-- An index of a program has only the program's instructions. -/
theorem Prog.index_mem (pg : Prog) : ∀ e ∈ pg.index.arr, e ∈ pg.code :=
  fun _ he => List.mem_toArray.mp he

/-! ## Sums of the low halves

An addition or subtraction of the low halves of two values gives the low
half of the sum, with nothing above it. Where what is known shows the sum
of the whole values has nothing above its low half, that is the sum. -/

theorem add32_small (f : Flags) (a b : BitVec 64) (h : (a + b).toNat < 4294967296) :
    FOp.eval (.alu .add .w32) f a b = a + b := by
  show BitVec.setWidth 64 (addCarry (BitVec.setWidth 32 a) (BitVec.setWidth 32 b) false).1 = _
  rw [add_res32]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth] at h ⊢
  omega

theorem sub32_small (f : Flags) (a b : BitVec 64) (h : (a - b).toNat < 4294967296) :
    FOp.eval (.alu .sub .w32) f a b = a - b := by
  show BitVec.setWidth 64 (subBorrow (BitVec.setWidth 32 a) (BitVec.setWidth 32 b) false).1 = _
  rw [sub_res32]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_setWidth] at h ⊢
  omega

/-- Whether two terms are the same value: as they are written; or the one
is a sum or difference of low halves and the other the sum or difference
itself, which what is known shows to have nothing above its low half. -/
def same32 (K : List (Val × TyS)) (a b : Val) : Bool :=
  a.same b ||
    match a with
    | .fop (.alu .add .w32) _ x y =>
      b.same (.add x y) && rangeHolds K (.add x y) 0 0xFFFFFFFF
    | .fop (.alu .sub .w32) _ x y =>
      b.same (x.less y) && rangeHolds K (x.less y) 0 0xFFFFFFFF
    | _ => false

theorem same32_den {ρ : Env} {K : List (Val × TyS)} {Ψ' : MemTy} {n : Nat}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) {a b : Val}
    (h : same32 K a b = true) : a.den ρ = b.den ρ := by
  unfold same32 at h
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · exact Val.same_den ρ h
  · split at h
    · next fl x y h =>
      rw [Bool.and_eq_true] at h
      have hr := rangeHolds_has h.2 hg
      rw [Val.same_den ρ h.1]
      show FOp.eval (.alu .add .w32) (fl.den ρ) (x.den ρ) (y.den ρ) = x.den ρ + y.den ρ
      refine add32_small _ _ _ ?_
      have hle : x.den ρ + y.den ρ - 0 ≤ (0xFFFFFFFF : BitVec 64) - 0 := hr
      rw [show x.den ρ + y.den ρ - 0 = x.den ρ + y.den ρ by simp, BitVec.le_def] at hle
      have : ((0xFFFFFFFF : BitVec 64) - 0).toNat = 4294967295 := by decide
      omega
    · next fl x y h =>
      rw [Bool.and_eq_true] at h
      have hr := rangeHolds_has h.2 hg
      rw [Val.same_den ρ h.1, Val.less_den]
      show FOp.eval (.alu .sub .w32) (fl.den ρ) (x.den ρ) (y.den ρ) = x.den ρ - y.den ρ
      refine sub32_small _ _ _ ?_
      have hle : (x.less y).den ρ - 0 ≤ (0xFFFFFFFF : BitVec 64) - 0 := hr
      rw [Val.less_den, show x.den ρ - y.den ρ - 0 = x.den ρ - y.den ρ by simp,
        BitVec.le_def] at hle
      have : ((0xFFFFFFFF : BitVec 64) - 0).toNat = 4294967295 := by decide
      omega
    · cases h

/-- A sum or difference of low halves, as the sum or difference itself. -/
def Val.whole : Val → Val
  | .fop (.alu .add .w32) _ x y => .add x y
  | .fop (.alu .sub .w32) _ x y => x.less y
  | v => v

/-- The same, where what is known shows it to be the sum; else the term. -/
def Val.wholeIf (K : List (Val × TyS)) (v : Val) : Val :=
  if same32 K v v.whole then v.whole else v

/-- A choice between two values on a condition, as the one chosen: where
the condition is so, or is not. Any other term, itself. -/
def Val.chosen (c : Cond) (fl : FlagsT) (b : Bool) : Val → Val
  | .fop (.cmov c' w) fl' x y =>
    if c' = c ∧ fl' = fl then
      match w with
      | .w64 => if b then y else x
      | .w32 => mkUn (.trunc .w32) (if b then y else x)
    else .fop (.cmov c' w) fl' x y
  | v => v

theorem Val.chosen_den {ρ : Env} {c : Cond} {fl : FlagsT} {b : Bool}
    (h : c.eval (fl.den ρ) = some b) : (v : Val) → (v.chosen c fl b).den ρ = v.den ρ := by
  intro v
  unfold Val.chosen
  split
  · next c' w fl' x y =>
    split
    · next he =>
      obtain ⟨rfl, rfl⟩ := he
      cases w with
      | w64 =>
        show Val.den ρ (if b then y else x) = FOp.eval (.cmov c' .w64) (fl'.den ρ) (x.den ρ) (y.den ρ)
        rw [cmov64, h]
        cases b <;> rfl
      | w32 =>
        show (mkUn (.trunc .w32) (if b then y else x)).den ρ
          = wide (w := .w32) (if (c'.eval (fl'.den ρ)).getD false then (y.den ρ).setWidth 32
              else (x.den ρ).setWidth 32)
        rw [mkUn_den, h]
        cases b <;> rfl
    · rfl
  · rfl

/-- The first choice on a condition a register holds, where the flags it
is on say how the condition comes out: the condition and the flags. -/
def CtxS.choice (Γ : CtxS) : Option (Cond × FlagsT) :=
  allRegs.findSome? fun r =>
    match Γ.regs.get r with
    | .fop (.cmov c _) fl _ _ => if fl.decides c then some (c, fl) else none
    | _ => none

/-- A context with each such choice made, the condition being so or not. -/
def CtxS.chose (Γ : CtxS) (c : Cond) (fl : FlagsT) (b : Bool) : CtxS :=
  { Γ with regs := Γ.regs.map (Val.chosen c fl b) }

theorem CtxS.chose_den {ρ : Env} (Γ : CtxS) {c : Cond} {fl : FlagsT} {b : Bool}
    (h : c.eval (fl.den ρ) = some b) : (Γ.chose c fl b).den ρ = Γ.den ρ :=
  ctx_ext (funext fun r => by
    show ((Γ.regs.map (Val.chosen c fl b)).get r).den ρ = (Γ.regs.get r).den ρ
    rw [Regs.get_map, Val.chosen_den h]) rfl rfl rfl

/-- **A context with each register's sum of low halves taken as the sum**,
where the context may be regarded so: where what is known shows the sum to
have nothing above its low half. Else the context. -/
def narrowFor (Γ : CtxS) (k : Nat) : CtxS :=
  if Γ.regs.map (Val.wholeIf Γ.known) == Γ.regs then Γ
  else if ({ Γ with regs := Γ.regs.map (Val.wholeIf Γ.known) } : CtxS).under k &&
      regardWith same32 noEnt Γ { Γ with regs := Γ.regs.map (Val.wholeIf Γ.known) } then
    { Γ with regs := Γ.regs.map (Val.wholeIf Γ.known) }
  else Γ

theorem narrowFor_sound (ρ : Env) (Γ : CtxS) {k : Nat} (hu : Γ.under k = true) :
    (narrowFor Γ k).under k = true ∧
      Regards fetch sys Ψ (Γ.den ρ) ((narrowFor Γ k).den ρ) := by
  unfold narrowFor
  split
  · exact ⟨hu, Regards.refl _⟩
  · split
    · next h =>
      rw [Bool.and_eq_true] at h
      exact ⟨h.1, regardWith_sound noEnt_sound ρ (fun _ _ hg _ _ hs => same32_den hg hs) h.2⟩
    · exact ⟨hu, Regards.refl _⟩

theorem narrowFor_regards (ρ : Env) (Γ : CtxS) (k : Nat) :
    Regards fetch sys Ψ (Γ.den ρ) ((narrowFor Γ k).den ρ) := by
  unfold narrowFor
  split
  · exact Regards.refl _
  · split
    · next h =>
      rw [Bool.and_eq_true] at h
      exact regardWith_sound noEnt_sound ρ (fun _ _ hg _ _ hs => same32_den hg hs) h.2
    · exact Regards.refl _

/-- A context with its regions that lie end to end taken as one, so that
bytes held are found whichever of them they are in: as a buffer is, part of
which was lent and given back. Not at a system call, where a region may
have just been taken as its parts to be given back. -/
def joinFor (Γ : CtxS) (k : Nat) (isSys : Bool) : CtxS :=
  if !isSys && (joinAll Γ.held.length Γ).under k then joinAll Γ.held.length Γ else Γ

theorem joinFor_sound (ρ : Env) (Γ : CtxS) {k : Nat} (isSys : Bool) (hu : Γ.under k = true) :
    (joinFor Γ k isSys).under k = true ∧
      Regards fetch sys Ψ (Γ.den ρ) ((joinFor Γ k isSys).den ρ) := by
  unfold joinFor
  split
  · next h =>
    rw [Bool.and_eq_true] at h
    exact ⟨h.2, joinAll_regards ρ _ Γ⟩
  · exact ⟨hu, Regards.refl _⟩

/-- A way a context is regarded before an instruction, `k` being a name
no term of it mentions. -/
abbrev Prep := CtxS → Nat → CtxS

/-- That a context may be regarded so, and then mentions no more names. -/
def Prep.Sound (fetch : Fetch) (sys : Syscall) (p : Prep) : Prop :=
  ∀ (Ψ : MemTy) (ρ : Env) (Γ : CtxS) (k : Nat), Γ.under k = true →
    (p Γ k).under k = true ∧ Regards fetch sys Ψ (Γ.den ρ) ((p Γ k).den ρ)

/-- A context regarded in each of some ways, one after another. -/
def prepAll (ps : List Prep) (Γ : CtxS) (k : Nat) : CtxS := ps.foldl (fun Γ p => p Γ k) Γ

theorem prepAll_sound : (ps : List Prep) → (∀ p ∈ ps, Prep.Sound fetch sys p) →
    Prep.Sound fetch sys (prepAll ps)
  | [], _ => fun _ _ _ _ hu => ⟨hu, Regards.refl _⟩
  | p :: ps, h => fun Ψ ρ Γ k hu => by
    obtain ⟨hu1, hr1⟩ := h p List.mem_cons_self Ψ ρ Γ k hu
    obtain ⟨hu2, hr2⟩ :=
      prepAll_sound ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) Ψ ρ (p Γ k) k hu1
    exact ⟨hu2, hr1.trans hr2⟩

/-- A context with what it says of rows let go, before a system call that
stores in memory or hands back fresh memory: such a call would not keep
it. A store keeps what it can, and other calls leave memory as it was. -/
def dropRowsFor (isSys : Bool) : Prep := fun Γ _ =>
  if isSys && !Γ.rows.isEmpty &&
      (match Γ.regs.rax.lit? with
       | some nr =>
         (match linuxKind nr with
          | some (.fills _ _ _) => true
          | some .map => true
          | _ => false)
       | none => false) then { Γ with rows := [] }
  else Γ

/-- **The ways a context is made ready before an instruction**, in order:
what it says of rows let go where the instruction would not keep it; at a
system call, a region that memory is to be given back out of taken as its
parts; regions that lie end to end taken as one; and each sum of low halves
that is seen to be the sum, taken as it. Each is the context regarded as
another, and one more such way is one more entry here. -/
def preps (isSys : Bool) : List Prep :=
  [dropRowsFor isSys, fun Γ k => if isSys then splitFor Γ k else Γ,
    fun Γ k => joinFor Γ k isSys, narrowFor]

theorem preps_sound (isSys : Bool) : ∀ p ∈ preps isSys, Prep.Sound fetch sys p := by
  intro p hp Ψ ρ Γ k hu
  simp only [preps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · have drop : (({ Γ with rows := [] } : CtxS)).under k = true ∧
        Regards fetch sys Ψ (Γ.den ρ) (CtxS.den ρ { Γ with rows := [] }) := by
      refine ⟨?_, fun k' Ψ' he hwf s hw => hw.dropRows⟩
      simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu ⊢
      exact ⟨hu.1, fun _ hr => nomatch hr⟩
    unfold dropRowsFor
    repeat' split
    all_goals first | exact drop | exact ⟨hu, Regards.refl _⟩
  · show (if isSys then splitFor Γ k else Γ).under k = true ∧ _
    split
    · exact splitFor_sound ρ Γ hu
    · exact ⟨hu, Regards.refl _⟩
  · exact joinFor_sound ρ Γ isSys hu
  · exact narrowFor_sound ρ Γ hu

/-- **The context made ready at an address**: what the program publishes
there published, and then regarded in each of the ways an instruction
wants. -/
def pubAtI (pg : Prog) (k : Nat) (isSys : Bool) (a : BitVec 64) (Γ : CtxS) : Option CtxS :=
  (pubOnly pg k a Γ).map fun Γ' => prepAll (preps isSys) Γ' k

theorem pubAtI_sound {ρ : Env} {pg : Prog} (hk : KindsOk Ψ pg.kinds) {k : Nat} {a : BitVec 64}
    {isSys : Bool} {Γ Γ' : CtxS} (h : pubAtI pg k isSys a Γ = some Γ') (hu : Γ.under k = true) :
    Γ'.under k = true ∧ Publishes fetch sys Ψ (Γ.den ρ) (Γ'.den ρ) := by
  obtain ⟨Γ₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hu₁, hp₁⟩ := pubOnly_sound (fetch := fetch) (sys := sys) (ρ := ρ) hk h₁ hu
  have hs := prepAll_sound (fetch := fetch) (sys := sys) (preps isSys) (preps_sound isSys)
  exact ⟨(hs Ψ ρ Γ₁ k hu₁).1, hp₁.trans fun Ψ' _ =>
    Publishes.of_regards (hs Ψ' ρ Γ₁ k hu₁).2⟩

theorem pubAt_sound {ρ : Env} {pg : Prog} (hk : KindsOk Ψ pg.kinds) {k : Nat} {a : BitVec 64}
    {Γ Γ' : CtxS} (h : pubAt pg k a Γ = some Γ') (hu : Γ.under k = true) :
    Γ'.under k = true ∧ Publishes fetch sys Ψ (Γ.den ρ) (Γ'.den ρ) := by
  unfold pubAt at h
  split at h
  · next Γp hp =>
    obtain ⟨hup, hpub⟩ := pubOnly_sound (fetch := fetch) (sys := sys) (ρ := ρ) hk hp hu
    split at h
    · split at h
      · cases h
        exact ⟨(splitFor_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) ρ Γp hup).1,
          hpub.trans fun Ψ' _ => Publishes.of_regards (splitFor_sound ρ Γp hup).2⟩
      · cases h; exact ⟨hup, hpub⟩
    · cases h; exact ⟨hup, hpub⟩
  · cases h

/-- **The checker walked from an address**, for at most so many
instructions, `k` being a name no term yet mentions. It stops where `stops`
says, unless that is where it starts: at the labels of a program, which are
typed each by a walk of its own. A context no state matches leaves nothing
to walk, wherever it is reached: at a label too. -/
def walkFrom (pg : Prog) (ix : Index) (stops : BitVec 64 → Bool) :
    Nat → Bool → Nat → Nat → BitVec 64 → CtxS → Walk
  | _, _, 0, _, a, Γ => .stop a Γ
  | rest, start, fuel + 1, k, a, Γ₀ =>
    if Γ₀.impossible then .vacuous else
    if !start && stops a then .stop a Γ₀ else
    match pubAtI pg k
      (match seek ix rest a with
       | some ((_, i, _), _) => decide (i = .syscall)
       | none => false) a Γ₀ with
    | none => .stop a Γ₀
    | some Γ =>
    if Γ.impossible then .vacuous else
    match seek ix rest a with
    | none => .stop a Γ
    | some ((_, i, len), tl) =>
      if i = .syscall then
        if !pg.pre Γ then .stop a Γ else
        if sysEnds Γ then .ends
        else
          match sysWorld Γ k (a + len) with
          | some Γ' =>
            if (Γ'.addKnown [(.var k, ansTy Γ)]).sharpen.under (k + 2) then
              .sys k (walkFrom pg ix stops tl false fuel (k + 2) (a + len)
                (Γ'.addKnown [(.var k, ansTy Γ)]).sharpen)
            else .stop a Γ
          | none =>
            match sysMap Γ k (a + len) with
            | some (Γe, Γo, sz) =>
              if (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen.under (k + 2) &&
                  (Γo.addKnown [(.var k, .range 1 (BitVec.ofNat 64 (addrTop - sz)))]).sharpen.under (k + 2)
                  && decide (sz ≤ addrTop) then
                .sys2 k
                  (walkFrom pg ix stops tl false fuel (k + 2) (a + len)
                    (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen)
                  (walkFrom pg ix stops tl false fuel (k + 2) (a + len)
                    (Γo.addKnown [(.var k, .range 1 (BitVec.ofNat 64 (addrTop - sz)))]).sharpen)
              else .stop a Γ
            | none =>
              match sysUnmap Γ k (a + len) with
              | some (Γe, Γo) =>
                if (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen.under (k + 2) &&
                    Γo.under (k + 2) then
                  .sys2 k
                    (walkFrom pg ix stops tl false fuel (k + 2) (a + len)
                      (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen)
                    (walkFrom pg ix stops tl false fuel (k + 2) (a + len) Γo)
                else .stop a Γ
              | none =>
                match sysReads Γ k (a + len) with
                | some (Γe, Γh) =>
                  if Γe.sharpen.under (k + 2) &&
                      (Γh.addKnown [(.var k, ansTy Γ)]).sharpen.under (k + 2) then
                    .sys2 k
                      (walkFrom pg ix stops tl false fuel (k + 2) (a + len) Γe.sharpen)
                      (walkFrom pg ix stops tl false fuel (k + 2) (a + len)
                        (Γh.addKnown [(.var k, ansTy Γ)]).sharpen)
                  else .stop a Γ
                | none =>
                  match sysFills pg.kinds Γ k (a + len) with
                  | some (Γe, Γh) =>
                    if (Γh.addKnown [(.var k, ansTy Γ)]).sharpen.under (k + 2) &&
                        regardS noEnt Γe Γh then
                      .sys k (walkFrom pg ix stops tl false fuel (k + 2) (a + len)
                        (Γh.addKnown [(.var k, ansTy Γ)]).sharpen)
                    else .stop a Γ
                  | none => .stop a Γ
      else
        match stepHeld pg.kinds Γ k (a + len) i with
        | none => .stop a Γ
        | some (Γ', t) =>
          if Γ'.under (k + 1) then
            match t with
            | .lit t' =>
              match Γ'.choice with
              | some (c, fl) =>
                if ((Γ'.chose c fl true).side fl c true).under (k + 1) &&
                    ((Γ'.chose c fl false).side fl c false).under (k + 1) then
                  .step i Γ (a + len) k
                    (.branch c fl
                      (walkFrom pg ix stops tl false fuel (k + 1) t'
                        ((Γ'.chose c fl true).side fl c true))
                      (walkFrom pg ix stops tl false fuel (k + 1) t'
                        ((Γ'.chose c fl false).side fl c false)))
                else .step i Γ (a + len) k (walkFrom pg ix stops tl false fuel (k + 1) t' Γ')
              | none => .step i Γ (a + len) k (walkFrom pg ix stops tl false fuel (k + 1) t' Γ')
            | .fop (.cmov c .w64) fl (.lit n) (.lit tk) =>
              if (Γ'.side fl c true).under (k + 1) && (Γ'.side fl c false).under (k + 1) then
                .step i Γ (a + len) k
                  (.branch c fl (walkFrom pg ix stops tl false fuel (k + 1) tk (Γ'.side fl c true))
                    (walkFrom pg ix stops tl false fuel (k + 1) n (Γ'.side fl c false)))
              else .stop a Γ
            | t => .step i Γ (a + len) k (.arrive t Γ')
          else .stop a Γ

theorem Ok.zero (a : BitVec 64) (Γ : Ctx) : Ok fetch sys Ψ 0 a Γ := by
  intro k hk Ψ' _ _ s _ _
  have hk0 : k = 0 := Nat.le_zero.mp hk
  subst hk0
  trivial

theorem Arrives.mono {n m : Nat} {t : BitVec 64} {Γ : Ctx} (h : Arrives fetch sys Ψ n t Γ)
    (hle : m ≤ n) : Arrives fetch sys Ψ m t Γ :=
  fun k hk => h k (Nat.le_trans hk hle)

/-- **The checker walked from an address**, for at most so many
instructions, `k` being a name no term yet mentions: `walkFrom`, with no
instruction yet at hand. -/
def walk (pg : Prog) (stops : BitVec 64 → Bool) (start : Bool) (fuel k : Nat) (a : BitVec 64)
    (Γ : CtxS) : Walk :=
  walkFrom pg pg.index stops 0 start fuel k a Γ

/-- **A walk whose leaves hold types the block it started at**, for as many
steps as the code where it stopped is typed for; and for one step more
where the walk got anywhere, which is what a program's labels are typed by,
each for one step more than all are assumed typed for. -/
theorem walkFrom_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {n : Nat} (pg : Prog) (hpre : PreSound fetch sys Ψ D pg.pre)
    (stops : BitVec 64 → Bool)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (ix : Index) (hix : ∀ e ∈ ix.arr, e ∈ pg.code) :
    (rest : Nat) →
    (start : Bool) → (fuel k : Nat) → (a : BitVec 64) → (Γ : CtxS) → (ρ : Env) → Γ.under k = true →
    (walkFrom pg ix stops rest start fuel k a Γ).holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ →
    Ok fetch sys Ψ n a (Γ.den ρ) ∧
      ((walkFrom pg ix stops rest start fuel k a Γ).moved = true →
        Ok fetch sys Ψ (n + 1) a (Γ.den ρ))
  | _, _, 0, _, _, _, _, _, h => ⟨h, fun hm => nomatch hm⟩
  | rest, start, fuel + 1, k, a, Γ₀, ρ, hu₀, h => by
    generalize hW : walkFrom pg ix stops rest start (fuel + 1) k a Γ₀ = W at h ⊢
    unfold walkFrom at hW
    split at hW
    · next himp₀ =>
      subst hW
      exact ⟨fun k _ Ψ' _ _ s _ hw => absurd hw (CtxS.impossible_sound himp₀ Ψ' k s),
        fun _ k _ Ψ' _ _ s _ hw => absurd hw (CtxS.impossible_sound himp₀ Ψ' k s)⟩
    split at hW
    · subst hW; exact ⟨h, fun hm => nomatch hm⟩
    split at hW
    · subst hW; exact ⟨h, fun hm => nomatch hm⟩
    rename_i Γ hpub
    obtain ⟨hu, hP⟩ := pubAtI_sound (fetch := fetch) (sys := sys) (ρ := ρ) hk hpub hu₀
    suffices hs : Ok fetch sys Ψ n a (Γ.den ρ) ∧
        (W.moved = true → Ok fetch sys Ψ (n + 1) a (Γ.den ρ)) from
      ⟨Ok.publish hP hs.1, fun hm => Ok.publish hP (hs.2 hm)⟩
    split at hW
    · next himp =>
      subst hW
      exact ⟨fun k _ Ψ' _ _ s _ hw => absurd hw (CtxS.impossible_sound himp Ψ' k s),
        fun _ k _ Ψ' _ _ s _ hw => absurd hw (CtxS.impossible_sound himp Ψ' k s)⟩
    split at hW
    · subst hW; exact ⟨h, fun hm => nomatch hm⟩
    · next e i len tl hfind =>
      obtain ⟨hmem, ha⟩ := seek_spec hfind
      have hmem := hix _ hmem
      have ha : e = a := ha
      subst ha
      have hf : fetch e = some (i, len) := hcode _ hmem
      -- an instruction or a call typed, with the machine arriving where it is left
      have both : (∀ m, m ≤ n → Ok fetch sys Ψ (m + 1) e (Γ.den ρ)) →
          Ok fetch sys Ψ n e (Γ.den ρ) ∧ Ok fetch sys Ψ (n + 1) e (Γ.den ρ) := fun hall =>
        ⟨by
          cases n with
          | zero => exact Ok.zero _ _
          | succ m => exact hall m (Nat.le_succ m), hall n (Nat.le_refl n)⟩
      split at hW
      · next hsys =>
        subst hsys
        split at hW
        · subst hW; exact ⟨h, fun hm => nomatch hm⟩
        rename_i hreq
        have hpreΓ : PreAt fetch sys Ψ D (Γ.den ρ) := hpre Γ ρ (by simpa using hreq)
        split at hW
        · next hends =>
          exact ⟨sysEnds_sound hD hkind hends hf hpreΓ n, fun _ =>
            sysEnds_sound hD hkind hends hf hpreΓ (n + 1)⟩
        · split at hW
          · next Γ' hw =>
            split at hW
            · next hu' =>
              subst hW
              have ih := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel (k + 2)
                  (e + len) _ (ρ.setSys k x y) hu' (h x y)).1
              have hb := both fun m hm => by
                refine Ok.step hf (sysWorld_sound hD hkind hw hu hpreΓ) ?_
                rintro t Δ ⟨x, y, rfl, rfl, hans⟩
                refine Arrives.learn [((Val.var k).den (ρ.setSys k x y),
                  (ansTy Γ).den (ρ.setSys k x y))] ?_ (((ih x y).mono hm).arrives)
                intro f hf' k' _ Ψ' _ _
                rw [List.mem_singleton.mp hf']
                show HasTy fetch sys Ψ' k' _ ((ρ.setSys k x y).val k)
                rw [Env.setSys_k]
                exact hans Ψ' k'
              exact ⟨hb.1, fun _ => hb.2⟩
            · subst hW; exact ⟨h, fun hm => nomatch hm⟩
          · split at hW
            · next Γe Γo sz hmap =>
              split at hW
              · next hchk =>
                subst hW
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
                obtain ⟨⟨hue, huo⟩, hsz⟩ := hchk
                have ihe := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                  (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel (k + 2)
                    (e + len) _ (ρ.setSys k x y) hue (h x y).1).1
                have iho := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                  (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel (k + 2)
                    (e + len) _ (ρ.setSys k x y) huo (h x y).2).1
                have hb := both fun m hm => by
                  refine Ok.step hf (sysMap_sound hD hkind hmap hu hpreΓ) ?_
                  rintro t Δ ⟨x, y, rfl, ⟨hx, rfl⟩ | ⟨hpos, hfit, rfl⟩⟩
                  · refine Arrives.learn [((Val.var k).den (ρ.setSys k x y), Ty.range (-4095) (-1))]
                      ?_ (((ihe x y).mono hm).arrives)
                    intro f hf' k' _ Ψ' _ _
                    rw [List.mem_singleton.mp hf']
                    refine hasTy_range.mpr ?_
                    show (ρ.setSys k x y).val k - (-4095) ≤ (-1 : BitVec 64) - (-4095)
                    rw [Env.setSys_k]
                    unfold SysErr at hx
                    bv_omega
                  · refine Arrives.learn [((Val.var k).den (ρ.setSys k x y),
                        Ty.range 1 (BitVec.ofNat 64 (addrTop - sz)))] ?_ (((iho x y).mono hm).arrives)
                    intro f hf' k' _ Ψ' _ _
                    rw [List.mem_singleton.mp hf']
                    refine hasTy_range.mpr ?_
                    show (ρ.setSys k x y).val k - 1 ≤ BitVec.ofNat 64 (addrTop - sz) - 1
                    rw [Env.setSys_k]
                    have hT : addrTop = 0x7ffffffff000 := rfl
                    bv_omega
                exact ⟨hb.1, fun _ => hb.2⟩
              · subst hW; exact ⟨h, fun hm => nomatch hm⟩
            · split at hW
              · next Γe Γo hun =>
                split at hW
                · next hchk =>
                  subst hW
                  simp only [Bool.and_eq_true] at hchk
                  obtain ⟨hue, huo⟩ := hchk
                  have ihe := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                    (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel (k + 2)
                      (e + len) _ (ρ.setSys k x y) hue (h x y).1).1
                  have iho := fun x y => (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel
                    (k + 2) (e + len) _ (ρ.setSys k x y) huo (h x y).2).1
                  have hb := both fun m hm => by
                    refine Ok.step hf (sysUnmap_sound hD hkind hun hu hpreΓ) ?_
                    rintro t Δ ⟨rfl, ⟨x, y, hx, rfl⟩ | ⟨x, y, rfl⟩⟩
                    · refine Arrives.learn [((Val.var k).den (ρ.setSys k x y), Ty.range (-4095) (-1))]
                        ?_ (((ihe x y).mono hm).arrives)
                      intro f hf' k' _ Ψ' _ _
                      rw [List.mem_singleton.mp hf']
                      refine hasTy_range.mpr ?_
                      show (ρ.setSys k x y).val k - (-4095) ≤ (-1 : BitVec 64) - (-4095)
                      rw [Env.setSys_k]
                      unfold SysErr at hx
                      bv_omega
                    · exact ((iho x y).mono hm).arrives
                  exact ⟨hb.1, fun _ => hb.2⟩
                · subst hW; exact ⟨h, fun hm => nomatch hm⟩
              · split at hW
                · next Γe Γh hrd =>
                  split at hW
                  · next hchk =>
                    subst hW
                    rw [Bool.and_eq_true] at hchk
                    have ihe := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                      (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel
                        (k + 2) (e + len) _ (ρ.setSys k x y) hchk.1 (h x y).1).1
                    have iho := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                      (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel
                        (k + 2) (e + len) _ (ρ.setSys k x y) hchk.2 (h x y).2).1
                    have hb := both fun m hm => by
                      refine Ok.step hf (sysReads_sound hD hkind hrd hu hpreΓ) ?_
                      rintro t Δ ⟨x, y, rfl, hcase, hans⟩
                      rcases hcase with rfl | rfl
                      · exact ((ihe x y).mono hm).arrives
                      · refine Arrives.learn [((Val.var k).den (ρ.setSys k x y),
                          (ansTy Γ).den (ρ.setSys k x y))] ?_ (((iho x y).mono hm).arrives)
                        intro f hf' k' _ Ψ' _ _
                        rw [List.mem_singleton.mp hf']
                        show HasTy fetch sys Ψ' k' _ ((ρ.setSys k x y).val k)
                        rw [Env.setSys_k]
                        exact hans Ψ' k'
                    exact ⟨hb.1, fun _ => hb.2⟩
                  · subst hW; exact ⟨h, fun hm => nomatch hm⟩
                · split at hW
                  · next Γe Γh hfill =>
                    split at hW
                    · next hchk =>
                      subst hW
                      rw [Bool.and_eq_true] at hchk
                      have ih := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                        (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel
                          (k + 2) (e + len) _ (ρ.setSys k x y) hchk.1 (h x y)).1
                      have hb := both fun m hm => by
                        refine Ok.step hf (sysFills_sound hD hkind hk hfill hu hpreΓ) ?_
                        rintro t Δ ⟨x, y, rfl, hcase, hans⟩
                        have hl : Arrives fetch sys Ψ m (e + len) (Γh.den (ρ.setSys k x y)) := by
                          refine Arrives.learn [((Val.var k).den (ρ.setSys k x y),
                            (ansTy Γ).den (ρ.setSys k x y))] ?_ (((ih x y).mono hm).arrives)
                          intro f hf' k' _ Ψ' _ _
                          rw [List.mem_singleton.mp hf']
                          show HasTy fetch sys Ψ' k' _ ((ρ.setSys k x y).val k)
                          rw [Env.setSys_k]
                          exact hans Ψ' k'
                        rcases hcase with rfl | rfl
                        · exact Arrives.regard (regardS_sound noEnt_sound (ρ.setSys k x y) hchk.2) hl
                        · exact hl
                      exact ⟨hb.1, fun _ => hb.2⟩
                    · subst hW; exact ⟨h, fun hm => nomatch hm⟩
                  · subst hW; exact ⟨h, fun hm => nomatch hm⟩
      · split at hW
        · subst hW; exact ⟨h, fun hm => nomatch hm⟩
        · next Γ' t hstep =>
          split at hW
          · next hu' =>
            have key : ∀ (rest : Walk),
                (∀ x, rest.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) (ρ.setVal k x)) →
                (∀ x, rest.holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) (ρ.setVal k x) →
                  Arrives fetch sys Ψ n (t.den (ρ.setVal k x)) (Γ'.den (ρ.setVal k x))) →
                Ok fetch sys Ψ n e (Γ.den ρ) ∧ Ok fetch sys Ψ (n + 1) e (Γ.den ρ) := by
              intro rest hrest harr
              refine both fun m hm => ?_
              refine Ok.step hf (stepHeld_sound hk hstep hu) ?_
              rintro t' Δ ⟨x, rfl, rfl⟩
              exact (harr x (hrest x)).mono hm
            split at hW
            · next t' =>
              have plain : ∀ (h : (Walk.step i Γ (e + len) k
                    (walkFrom pg ix stops tl false fuel (k + 1) t' Γ')).holds
                    (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ),
                  Ok fetch sys Ψ n e (Γ.den ρ) ∧ Ok fetch sys Ψ (n + 1) e (Γ.den ρ) :=
                fun h => key _ h (fun x hx =>
                  (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel (k + 1) t' Γ'
                    (ρ.setVal k x) hu' hx).1.arrives)
              split at hW
              · next c fl hch =>
                split at hW
                · next hus =>
                  subst hW
                  rw [Bool.and_eq_true] at hus
                  have hb := key _ h (fun x ⟨⟨b, hc⟩, htk, hfl⟩ => by
                    show Arrives fetch sys Ψ n t' (Γ'.den (ρ.setVal k x))
                    rw [← Γ'.chose_den hc]
                    cases b
                    · exact (Ok.regard ((Γ'.chose c fl false).side_regards hc)
                        (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel (k + 1)
                          t' _ (ρ.setVal k x) hus.2 (hfl hc)).1).arrives
                    · exact (Ok.regard ((Γ'.chose c fl true).side_regards hc)
                        (walkFrom_sound hD hkind pg hpre stops hcode hk ix hix tl false fuel (k + 1)
                          t' _ (ρ.setVal k x) hus.1 (htk hc)).1).arrives)
                  exact ⟨hb.1, fun _ => hb.2⟩
                · subst hW
                  have hb := plain h
                  exact ⟨hb.1, fun _ => hb.2⟩
              · subst hW
                have hb := plain h
                exact ⟨hb.1, fun _ => hb.2⟩
            · next c fl nx tk =>
              split at hW
              · next hus =>
                subst hW
                rw [Bool.and_eq_true] at hus
                have hb := key _ h (fun x ⟨⟨b, hc⟩, htk, hfl⟩ => by
                  show Arrives fetch sys Ψ n
                    (FOp.eval (.cmov c .w64) (fl.den (ρ.setVal k x)) nx tk) _
                  rw [cmov64, hc]
                  cases b
                  · exact (Ok.regard (Γ'.side_regards hc) (walkFrom_sound hD hkind pg hpre stops
                      hcode hk ix hix tl false fuel (k + 1) nx _ (ρ.setVal k x) hus.2 (hfl hc)).1).arrives
                  · exact (Ok.regard (Γ'.side_regards hc) (walkFrom_sound hD hkind pg hpre stops
                      hcode hk ix hix tl false fuel (k + 1) tk _ (ρ.setVal k x) hus.1 (htk hc)).1).arrives)
                exact ⟨hb.1, fun _ => hb.2⟩
              · subst hW; exact ⟨h, fun hm => nomatch hm⟩
            · subst hW
              have hb := key _ h (fun x hx => hx)
              exact ⟨hb.1, fun _ => hb.2⟩
          · subst hW; exact ⟨h, fun hm => nomatch hm⟩

/-- **A walk that leaves nothing to be shown types the address it started
at.** -/
theorem walk_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {n : Nat} (pg : Prog) (hpre : PreSound fetch sys Ψ D pg.pre)
    (stops : BitVec 64 → Bool)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (start : Bool) (fuel k : Nat) (a : BitVec 64) (Γ : CtxS) (ρ : Env) (hu : Γ.under k = true)
    (h : (walk pg stops start fuel k a Γ).holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ) :
    Ok fetch sys Ψ n a (Γ.den ρ) ∧
      ((walk pg stops start fuel k a Γ).moved = true → Ok fetch sys Ψ (n + 1) a (Γ.den ρ)) :=
  walkFrom_sound hD hkind pg hpre stops hcode hk pg.index pg.index_mem 0 start fuel k a Γ ρ hu h

end TypedAsm.U
