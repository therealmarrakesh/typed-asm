import TypedAsm.U.Step
import TypedAsm.U.SysStep
import TypedAsm.U.Guard
import TypedAsm.U.Learn
import TypedAsm.U.PublishS
import TypedAsm.U.Laws

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

/-- The same, told whether the instruction there is a system call. -/
def pubAtI (pg : Prog) (k : Nat) (isSys : Bool) (a : BitVec 64) (Γ : CtxS) : Option CtxS :=
  match pubOnly pg k a Γ with
  | some Γ' => if isSys then some (splitFor Γ' k) else some Γ'
  | none => none

/-- The instruction at an address in a list of them, and those after it. -/
def seekAll (a : BitVec 64) : List (BitVec 64 × Instr × BitVec 64) →
    Option ((BitVec 64 × Instr × BitVec 64) × List (BitVec 64 × Instr × BitVec 64))
  | [] => none
  | e :: tl => if e.1 = a then some (e, tl) else seekAll a tl

/-- **The instruction at an address, and those after it in the program**:
the first of `rest` where that is it, which it is where one instruction
follows another; else looked for through the program. -/
def seek (code rest : List (BitVec 64 × Instr × BitVec 64)) (a : BitVec 64) :
    Option ((BitVec 64 × Instr × BitVec 64) × List (BitVec 64 × Instr × BitVec 64)) :=
  match rest with
  | e :: tl => if e.1 = a then some (e, tl) else seekAll a code
  | [] => seekAll a code

theorem seekAll_spec {a : BitVec 64} : {code : List (BitVec 64 × Instr × BitVec 64)} →
    {e : BitVec 64 × Instr × BitVec 64} → {tl : List (BitVec 64 × Instr × BitVec 64)} →
    seekAll a code = some (e, tl) → e ∈ code ∧ e.1 = a ∧ ∀ x ∈ tl, x ∈ code
  | [], _, _, h => nomatch h
  | e₀ :: rest, e, tl, h => by
    unfold seekAll at h
    split at h
    · next he =>
      cases h
      exact ⟨List.mem_cons_self, he, fun x hx => List.mem_cons_of_mem _ hx⟩
    · obtain ⟨h1, h2, h3⟩ := seekAll_spec h
      exact ⟨List.mem_cons_of_mem _ h1, h2, fun x hx => List.mem_cons_of_mem _ (h3 x hx)⟩

theorem seek_spec {code rest : List (BitVec 64 × Instr × BitVec 64)} {a : BitVec 64}
    {e : BitVec 64 × Instr × BitVec 64} {tl : List (BitVec 64 × Instr × BitVec 64)}
    (hrest : ∀ x ∈ rest, x ∈ code) (h : seek code rest a = some (e, tl)) :
    e ∈ code ∧ e.1 = a ∧ ∀ x ∈ tl, x ∈ code := by
  unfold seek at h
  split at h
  · next e₀ tl₀ =>
    split at h
    · next he =>
      cases h
      exact ⟨hrest _ List.mem_cons_self, he, fun x hx => hrest x (List.mem_cons_of_mem _ hx)⟩
    · exact seekAll_spec h
  · exact seekAll_spec h

theorem pubAtI_sound {ρ : Env} {pg : Prog} (hk : KindsOk Ψ pg.kinds) {k : Nat} {a : BitVec 64}
    {isSys : Bool} {Γ Γ' : CtxS} (h : pubAtI pg k isSys a Γ = some Γ') (hu : Γ.under k = true) :
    Γ'.under k = true ∧ Publishes fetch sys Ψ (Γ.den ρ) (Γ'.den ρ) := by
  unfold pubAtI at h
  split at h
  · next Γp hp =>
    obtain ⟨hup, hpub⟩ := pubOnly_sound (fetch := fetch) (sys := sys) (ρ := ρ) hk hp hu
    split at h
    · cases h
      exact ⟨(splitFor_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) ρ Γp hup).1,
        hpub.trans fun Ψ' _ => Publishes.of_regards (splitFor_sound ρ Γp hup).2⟩
    · cases h; exact ⟨hup, hpub⟩
  · cases h

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
def walkFrom (pg : Prog) (stops : BitVec 64 → Bool) :
    List (BitVec 64 × Instr × BitVec 64) → Bool → Nat → Nat → BitVec 64 → CtxS → Walk
  | _, _, 0, _, a, Γ => .stop a Γ
  | rest, start, fuel + 1, k, a, Γ₀ =>
    if Γ₀.impossible then .vacuous else
    if !start && stops a then .stop a Γ₀ else
    match pubAtI pg k
      (match seek pg.code rest a with
       | some ((_, i, _), _) => decide (i = .syscall)
       | none => false) a Γ₀ with
    | none => .stop a Γ₀
    | some Γ =>
    if Γ.impossible then .vacuous else
    match seek pg.code rest a with
    | none => .stop a Γ
    | some ((_, i, len), tl) =>
      if i = .syscall then
        if !pg.pre Γ then .stop a Γ else
        if sysEnds Γ then .ends
        else
          match sysWorld Γ k (a + len) with
          | some Γ' =>
            if Γ'.under (k + 2) then .sys k (walkFrom pg stops tl false fuel (k + 2) (a + len) Γ')
            else .stop a Γ
          | none =>
            match sysMap Γ k (a + len) with
            | some (Γe, Γo, sz) =>
              if (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen.under (k + 2) &&
                  (Γo.addKnown [(.var k, .range 0 (BitVec.ofNat 64 (addrTop - sz)))]).sharpen.under (k + 2)
                  && decide (sz ≤ addrTop) then
                .sys2 k
                  (walkFrom pg stops tl false fuel (k + 2) (a + len)
                    (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen)
                  (walkFrom pg stops tl false fuel (k + 2) (a + len)
                    (Γo.addKnown [(.var k, .range 0 (BitVec.ofNat 64 (addrTop - sz)))]).sharpen)
              else .stop a Γ
            | none =>
              match sysUnmap Γ k (a + len) with
              | some (Γe, Γo) =>
                if (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen.under (k + 2) &&
                    Γo.under (k + 2) then
                  .sys2 k
                    (walkFrom pg stops tl false fuel (k + 2) (a + len)
                      (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen)
                    (walkFrom pg stops tl false fuel (k + 2) (a + len) Γo)
                else .stop a Γ
              | none =>
                match sysFills pg.kinds Γ k (a + len) with
                | some (Γe, Γh) =>
                  if (Γh.addKnown [(.var k, ansTy Γ)]).sharpen.under (k + 2) &&
                      regardS noEnt Γe Γh then
                    .sys k (walkFrom pg stops tl false fuel (k + 2) (a + len)
                      (Γh.addKnown [(.var k, ansTy Γ)]).sharpen)
                  else .stop a Γ
                | none => .stop a Γ
      else
        match stepHeld pg.kinds Γ k (a + len) i with
        | none => .stop a Γ
        | some (Γ', t) =>
          if Γ'.under (k + 1) then
            match t with
            | .lit t' => .step i Γ (a + len) k (walkFrom pg stops tl false fuel (k + 1) t' Γ')
            | .fop (.cmov c .w64) fl (.lit n) (.lit tk) =>
              if (Γ'.side fl c true).under (k + 1) && (Γ'.side fl c false).under (k + 1) then
                .step i Γ (a + len) k
                  (.branch c fl (walkFrom pg stops tl false fuel (k + 1) tk (Γ'.side fl c true))
                    (walkFrom pg stops tl false fuel (k + 1) n (Γ'.side fl c false)))
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
  walkFrom pg stops [] start fuel k a Γ

/-- **A walk whose leaves hold types the block it started at**, for as many
steps as the code where it stopped is typed for; and for one step more
where the walk got anywhere, which is what a program's labels are typed by,
each for one step more than all are assumed typed for. -/
theorem walkFrom_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {n : Nat} (pg : Prog) (hpre : PreSound fetch sys Ψ D pg.pre)
    (stops : BitVec 64 → Bool)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds) :
    (rest : List (BitVec 64 × Instr × BitVec 64)) → (∀ x ∈ rest, x ∈ pg.code) →
    (start : Bool) → (fuel k : Nat) → (a : BitVec 64) → (Γ : CtxS) → (ρ : Env) → Γ.under k = true →
    (walkFrom pg stops rest start fuel k a Γ).holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ →
    Ok fetch sys Ψ n a (Γ.den ρ) ∧
      ((walkFrom pg stops rest start fuel k a Γ).moved = true →
        Ok fetch sys Ψ (n + 1) a (Γ.den ρ))
  | _, _, _, 0, _, _, _, _, _, h => ⟨h, fun hm => nomatch hm⟩
  | rest, hrest, start, fuel + 1, k, a, Γ₀, ρ, hu₀, h => by
    generalize hW : walkFrom pg stops rest start (fuel + 1) k a Γ₀ = W at h ⊢
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
      obtain ⟨hmem, ha, htl⟩ := seek_spec hrest hfind
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
              have ih := fun x y => (walkFrom_sound hD hkind pg hpre stops hcode hk tl htl false fuel (k + 2)
                (e + len) Γ' (ρ.setSys k x y) hu' (h x y)).1
              have hb := both fun m hm => by
                refine Ok.step hf (sysWorld_sound hD hkind hw hu hpreΓ) ?_
                rintro t Δ ⟨x, y, rfl, rfl⟩
                exact ((ih x y).mono hm).arrives
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
                  (walkFrom_sound hD hkind pg hpre stops hcode hk tl htl false fuel (k + 2)
                    (e + len) _ (ρ.setSys k x y) hue (h x y).1).1
                have iho := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                  (walkFrom_sound hD hkind pg hpre stops hcode hk tl htl false fuel (k + 2)
                    (e + len) _ (ρ.setSys k x y) huo (h x y).2).1
                have hb := both fun m hm => by
                  refine Ok.step hf (sysMap_sound hD hkind hmap hu hpreΓ) ?_
                  rintro t Δ ⟨x, y, rfl, ⟨hx, rfl⟩ | ⟨hfit, rfl⟩⟩
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
                        Ty.range 0 (BitVec.ofNat 64 (addrTop - sz)))] ?_ (((iho x y).mono hm).arrives)
                    intro f hf' k' _ Ψ' _ _
                    rw [List.mem_singleton.mp hf']
                    refine hasTy_range.mpr ?_
                    show (ρ.setSys k x y).val k - 0 ≤ BitVec.ofNat 64 (addrTop - sz) - 0
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
                    (walkFrom_sound hD hkind pg hpre stops hcode hk tl htl false fuel (k + 2)
                      (e + len) _ (ρ.setSys k x y) hue (h x y).1).1
                  have iho := fun x y => (walkFrom_sound hD hkind pg hpre stops hcode hk tl htl false fuel
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
                · next Γe Γh hfill =>
                  split at hW
                  · next hchk =>
                    subst hW
                    rw [Bool.and_eq_true] at hchk
                    have ih := fun x y => Ok.regard (CtxS.sharpen_regards (ρ.setSys k x y) _)
                      (walkFrom_sound hD hkind pg hpre stops hcode hk tl htl false fuel
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
              subst hW
              have hb := key _ h (fun x hx =>
                (walkFrom_sound hD hkind pg hpre stops hcode hk tl htl false fuel (k + 1) t' Γ' (ρ.setVal k x) hu'
                  hx).1.arrives)
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
                      hcode hk tl htl false fuel (k + 1) nx _ (ρ.setVal k x) hus.2 (hfl hc)).1).arrives
                  · exact (Ok.regard (Γ'.side_regards hc) (walkFrom_sound hD hkind pg hpre stops
                      hcode hk tl htl false fuel (k + 1) tk _ (ρ.setVal k x) hus.1 (htk hc)).1).arrives)
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
  walkFrom_sound hD hkind pg hpre stops hcode hk [] (fun _ hx => nomatch hx) start fuel k a Γ ρ hu h

end TypedAsm.U
