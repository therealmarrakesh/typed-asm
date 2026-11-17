import TypedAsm.U.Step
import TypedAsm.U.SysStep
import TypedAsm.U.Guard
import TypedAsm.U.Learn
import TypedAsm.U.PublishS

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
  | .sys k rest, ρ => ∀ x, rest.holds P A (ρ.setVal k x)
  | .sys2 k a b, ρ => ∀ x, a.holds P A (ρ.setVal k x) ∧ b.holds P A (ρ.setVal k x)
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

/-- A context may be regarded as itself after nothing is published. -/
theorem Publishes.refl (Γ : Ctx) : Publishes fetch sys Ψ Γ Γ :=
  fun _ Ψ' _ hwf _ hw => ⟨Ψ', MemTy.Ext.refl Ψ', hwf, hw⟩

/-- The context at an address once what the program publishes there is
published: as it was, where it publishes nothing there. Nothing where the
region is not as the program says. -/
def pubAt (pg : Prog) (k : Nat) (a : BitVec 64) (Γ : CtxS) : Option CtxS :=
  match pg.pubs.find? fun p => p.addr = a with
  | none => some Γ
  | some p =>
    match publishS pg.kinds Γ (Γ.regs.get p.base) p.shape p.tag with
    | some Γ' => if Γ'.under k then some Γ' else none
    | none => none

theorem pubAt_sound {ρ : Env} {pg : Prog} (hk : KindsOk Ψ pg.kinds) {k : Nat} {a : BitVec 64}
    {Γ Γ' : CtxS} (h : pubAt pg k a Γ = some Γ') (hu : Γ.under k = true) :
    Γ'.under k = true ∧ Publishes fetch sys Ψ (Γ.den ρ) (Γ'.den ρ) := by
  unfold pubAt at h
  split at h
  · cases h; exact ⟨hu, Publishes.refl _⟩
  · split at h
    · next Γp hp =>
      split at h
      · next hup => cases h; exact ⟨hup, publishS_sound hk hp⟩
      · cases h
    · cases h

/-- **The checker walked from an address**, for at most so many
instructions, `k` being a name no term yet mentions. It stops where `stops`
says, unless that is where it starts: at the labels of a program, which are
typed each by a walk of its own. -/
def walk (pg : Prog) (stops : BitVec 64 → Bool) :
    Bool → Nat → Nat → BitVec 64 → CtxS → Walk
  | _, 0, _, a, Γ => .stop a Γ
  | start, fuel + 1, k, a, Γ₀ =>
    if !start && stops a then .stop a Γ₀ else
    match pubAt pg k a Γ₀ with
    | none => .stop a Γ₀
    | some Γ =>
    if Γ.impossible then .vacuous else
    match pg.code.find? fun e => e.1 = a with
    | none => .stop a Γ
    | some (_, i, len) =>
      if i = .syscall then
        if sysEnds Γ then .ends
        else
          match sysWorld Γ k (a + len) with
          | some Γ' =>
            if Γ'.under (k + 1) then .sys k (walk pg stops false fuel (k + 1) (a + len) Γ') else .stop a Γ
          | none =>
            match sysMap Γ k (a + len) with
            | some (Γe, Γo, sz) =>
              if (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen.under (k + 1) &&
                  (Γo.addKnown [(.var k, .range 0 (BitVec.ofNat 64 (addrTop - sz)))]).sharpen.under (k + 1)
                  && decide (sz ≤ addrTop) then
                .sys2 k
                  (walk pg stops false fuel (k + 1) (a + len)
                    (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen)
                  (walk pg stops false fuel (k + 1) (a + len)
                    (Γo.addKnown [(.var k, .range 0 (BitVec.ofNat 64 (addrTop - sz)))]).sharpen)
              else .stop a Γ
            | none =>
              match sysUnmap Γ k (a + len) with
              | some (Γe, Γo) =>
                if (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen.under (k + 1) && Γo.under k &&
                    Γo.under (k + 1) then
                  .sys2 k
                    (walk pg stops false fuel (k + 1) (a + len)
                      (Γe.addKnown [(.var k, .range (-4095) (-1))]).sharpen)
                    (walk pg stops false fuel (k + 1) (a + len) Γo)
                else .stop a Γ
              | none =>
                match sysFills pg.kinds Γ k (a + len) with
                | some (Γe, Γh) =>
                  if Γh.under (k + 1) && regardS noEnt Γe Γh then
                    .sys k (walk pg stops false fuel (k + 1) (a + len) Γh)
                  else .stop a Γ
                | none => .stop a Γ
      else
        match stepHeld pg.kinds Γ k (a + len) i with
        | none => .stop a Γ
        | some (Γ', t) =>
          if Γ'.under (k + 1) then
            match t with
            | .lit t' => .step i Γ (a + len) k (walk pg stops false fuel (k + 1) t' Γ')
            | .fop (.cmov c .w64) fl (.lit n) (.lit tk) =>
              if (Γ'.side fl c true).under (k + 1) && (Γ'.side fl c false).under (k + 1) then
                .step i Γ (a + len) k
                  (.branch c fl (walk pg stops false fuel (k + 1) tk (Γ'.side fl c true))
                    (walk pg stops false fuel (k + 1) n (Γ'.side fl c false)))
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

/-- **A walk whose leaves hold types the block it started at**, for as many
steps as the code where it stopped is typed for; and for one step more
where the walk got anywhere, which is what a program's labels are typed by,
each for one step more than all are assumed typed for. -/
theorem walk_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {n : Nat} (pg : Prog)
    (stops : BitVec 64 → Bool)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds) :
    (start : Bool) → (fuel k : Nat) → (a : BitVec 64) → (Γ : CtxS) → (ρ : Env) → Γ.under k = true →
    (walk pg stops start fuel k a Γ).holds (Ok fetch sys Ψ n) (Arrives fetch sys Ψ n) ρ →
    Ok fetch sys Ψ n a (Γ.den ρ) ∧
      ((walk pg stops start fuel k a Γ).moved = true → Ok fetch sys Ψ (n + 1) a (Γ.den ρ))
  | _, 0, _, _, _, _, _, h => ⟨h, fun hm => nomatch hm⟩
  | start, fuel + 1, k, a, Γ₀, ρ, hu₀, h => by
    generalize hW : walk pg stops start (fuel + 1) k a Γ₀ = W at h ⊢
    unfold walk at hW
    split at hW
    · subst hW; exact ⟨h, fun hm => nomatch hm⟩
    split at hW
    · subst hW; exact ⟨h, fun hm => nomatch hm⟩
    rename_i Γ hpub
    obtain ⟨hu, hP⟩ := pubAt_sound (fetch := fetch) (sys := sys) (ρ := ρ) hk hpub hu₀
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
    · next e i len hfind =>
      have hmem := List.mem_of_find?_eq_some hfind
      have ha : e = a := by simpa using List.find?_some hfind
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
        · next hends =>
          exact ⟨sysEnds_sound hD hkind hpre hends hf n, fun _ =>
            sysEnds_sound hD hkind hpre hends hf (n + 1)⟩
        · split at hW
          · next Γ' hw =>
            split at hW
            · next hu' =>
              subst hW
              have ih := fun x => (walk_sound hD hkind hpre pg stops hcode hk false fuel (k + 1) (e + len) Γ'
                (ρ.setVal k x) hu' (h x)).1
              have hb := both fun m hm => by
                refine Ok.step hf (sysWorld_sound hD hkind hpre hw hu) ?_
                rintro t Δ ⟨x, rfl, rfl⟩
                exact ((ih x).mono hm).arrives
              exact ⟨hb.1, fun _ => hb.2⟩
            · subst hW; exact ⟨h, fun hm => nomatch hm⟩
          · split at hW
            · next Γe Γo sz hmap =>
              split at hW
              · next hchk =>
                subst hW
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
                obtain ⟨⟨hue, huo⟩, hsz⟩ := hchk
                have ihe := fun x => Ok.regard (CtxS.sharpen_regards (ρ.setVal k x) _)
                  (walk_sound hD hkind hpre pg stops hcode hk false fuel (k + 1)
                    (e + len) _ (ρ.setVal k x) hue (h x).1).1
                have iho := fun x => Ok.regard (CtxS.sharpen_regards (ρ.setVal k x) _)
                  (walk_sound hD hkind hpre pg stops hcode hk false fuel (k + 1)
                    (e + len) _ (ρ.setVal k x) huo (h x).2).1
                have hb := both fun m hm => by
                  refine Ok.step hf (sysMap_sound hD hkind hpre hmap hu) ?_
                  rintro t Δ ⟨x, rfl, ⟨hx, rfl⟩ | ⟨hfit, rfl⟩⟩
                  · refine Arrives.learn [((Val.var k).den (ρ.setVal k x), Ty.range (-4095) (-1))]
                      ?_ (((ihe x).mono hm).arrives)
                    intro f hf' k' _ Ψ' _ _
                    rw [List.mem_singleton.mp hf']
                    refine hasTy_range.mpr ?_
                    show (ρ.setVal k x).val k - (-4095) ≤ (-1 : BitVec 64) - (-4095)
                    rw [Env.setVal_get_self]
                    unfold SysErr at hx
                    bv_omega
                  · refine Arrives.learn [((Val.var k).den (ρ.setVal k x),
                        Ty.range 0 (BitVec.ofNat 64 (addrTop - sz)))] ?_ (((iho x).mono hm).arrives)
                    intro f hf' k' _ Ψ' _ _
                    rw [List.mem_singleton.mp hf']
                    refine hasTy_range.mpr ?_
                    show (ρ.setVal k x).val k - 0 ≤ BitVec.ofNat 64 (addrTop - sz) - 0
                    rw [Env.setVal_get_self]
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
                  obtain ⟨⟨hue, huo⟩, huo'⟩ := hchk
                  have ihe := fun x => Ok.regard (CtxS.sharpen_regards (ρ.setVal k x) _)
                    (walk_sound hD hkind hpre pg stops hcode hk false fuel (k + 1)
                      (e + len) _ (ρ.setVal k x) hue (h x).1).1
                  have iho := (walk_sound hD hkind hpre pg stops hcode hk false fuel (k + 1)
                    (e + len) _ (ρ.setVal k 0) huo' (h 0).2).1
                  rw [CtxS.den_setVal ρ k 0 Γo huo] at iho
                  have hb := both fun m hm => by
                    refine Ok.step hf (sysUnmap_sound hD hkind hpre hun hu) ?_
                    rintro t Δ ⟨rfl, ⟨x, hx, rfl⟩ | rfl⟩
                    · refine Arrives.learn [((Val.var k).den (ρ.setVal k x), Ty.range (-4095) (-1))]
                        ?_ (((ihe x).mono hm).arrives)
                      intro f hf' k' _ Ψ' _ _
                      rw [List.mem_singleton.mp hf']
                      refine hasTy_range.mpr ?_
                      show (ρ.setVal k x).val k - (-4095) ≤ (-1 : BitVec 64) - (-4095)
                      rw [Env.setVal_get_self]
                      unfold SysErr at hx
                      bv_omega
                    · exact (iho.mono hm).arrives
                  exact ⟨hb.1, fun _ => hb.2⟩
                · subst hW; exact ⟨h, fun hm => nomatch hm⟩
              · split at hW
                · next Γe Γh hfill =>
                  split at hW
                  · next hchk =>
                    subst hW
                    rw [Bool.and_eq_true] at hchk
                    have ih := fun x => (walk_sound hD hkind hpre pg stops hcode hk false fuel
                      (k + 1) (e + len) Γh (ρ.setVal k x) hchk.1 (h x)).1
                    have hb := both fun m hm => by
                      refine Ok.step hf (sysFills_sound hD hkind hpre hk hfill hu) ?_
                      rintro t Δ ⟨x, rfl, rfl | rfl⟩
                      · exact Arrives.regard (regardS_sound noEnt_sound (ρ.setVal k x) hchk.2)
                          ((ih x).mono hm).arrives
                      · exact ((ih x).mono hm).arrives
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
                (walk_sound hD hkind hpre pg stops hcode hk false fuel (k + 1) t' Γ' (ρ.setVal k x) hu'
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
                  · exact (Ok.regard (Γ'.side_regards hc) (walk_sound hD hkind hpre pg stops
                      hcode hk false fuel (k + 1) nx _ (ρ.setVal k x) hus.2 (hfl hc)).1).arrives
                  · exact (Ok.regard (Γ'.side_regards hc) (walk_sound hD hkind hpre pg stops
                      hcode hk false fuel (k + 1) tk _ (ρ.setVal k x) hus.1 (htk hc)).1).arrives)
                exact ⟨hb.1, fun _ => hb.2⟩
              · subst hW; exact ⟨h, fun hm => nomatch hm⟩
            · subst hW
              have hb := key _ h (fun x hx => hx)
              exact ⟨hb.1, fun _ => hb.2⟩
          · subst hW; exact ⟨h, fun hm => nomatch hm⟩

end TypedAsm.U
