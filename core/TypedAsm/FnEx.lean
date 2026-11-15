import TypedAsm.Fn
import TypedAsm.Program

/-!
# Functions that hand back something they made

A function that makes a block and hands it to its caller cannot say in its
signature where the block is: the address is not known until the function
has run. `FnSigEx` is a signature whose results, and the blocks it gives,
depend on a value `x` that the function chooses when it returns. The place
it returns to must be ready for any `x`; so the return address is typed as
code for a family of contexts (`Ty.codeAll`), and before returning the
function says which one it returns into.
-/

namespace TypedAsm

/-- A function signature whose results depend on a value chosen at the
return: typically the address of something the function made. -/
structure FnSigEx where
  /-- The types expected in the registers on entry. -/
  args : Reg → Ty
  /-- The registers whose types are the same on return as on entry. -/
  preserved : Reg → Bool
  /-- The number of stack slots the function uses below its return address. -/
  need : Nat
  /-- The blocks the function is handed to own. -/
  takes : List (BitVec 64 × List Ty) := []
  /-- The types left in the registers on return, for the value chosen. -/
  results : BitVec 64 → Reg → Ty
  /-- The blocks the function hands back, for the value chosen. -/
  gives : BitVec 64 → List (BitVec 64 × List Ty)

namespace FnSigEx

/-- The ordinary signature the function meets once the value is chosen. -/
def pick (sig : FnSigEx) (x : BitVec 64) : FnSig :=
  ⟨sig.args, sig.results x, sig.preserved, sig.need, sig.takes, sig.gives x⟩

/-- Register types on entry, when the preserved registers have types `saved`. -/
def regsIn (sig : FnSigEx) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if sig.preserved r then saved r else sig.args r

/-- The context at the function's first instruction, for a caller that
expects `ret x` on return, whichever `x` the function chooses, has `rest` on
its stack and owns `frame` besides what the function takes. -/
def entry (sig : FnSigEx) (saved : Reg → Ty) (ret : BitVec 64 → Ctx) (rest : List Ty)
    (room : Nat) (frame : List (BitVec 64 × List Ty)) : Ctx :=
  ⟨sig.regsIn saved, .codeAll ret :: rest, room, Flags.Any, sig.takes ++ frame⟩

/-- What the function needs of its caller: what an ordinary function with
each of the signatures would need, and that what the caller owns besides is
the same whichever value is chosen. -/
structure CallerOk (sig : FnSigEx) (saved : Reg → Ty) (ret : BitVec 64 → Ctx) (rest : List Ty)
    (room : Nat) (frame : List (BitVec 64 × List Ty)) : Prop where
  each : ∀ x, (sig.pick x).CallerOk saved (ret x) rest room
  frame : ∀ x, (ret x).owned.drop (sig.gives x).length = frame

/-- `sig.At Φ a`: the code typing lets address `a` be entered as a function
with signature `sig`, by any caller. -/
def At (sig : FnSigEx) (Φ : CodeTy) (a : BitVec 64) : Prop :=
  ∀ saved ret rest room frame, sig.CallerOk saved ret rest room frame →
    Φ a (sig.entry saved ret rest room frame)

/-- At its return into `ret x`, a function that owns the blocks it gives for
`x` and after them what the caller owned besides owns what `ret x` expects. -/
theorem CallerOk.owned_back {sig : FnSigEx} {saved : Reg → Ty} {ret : BitVec 64 → Ctx}
    {rest : List Ty} {room : Nat} {frame owned : List (BitVec 64 × List Ty)}
    (h : sig.CallerOk saved ret rest room frame) (x : BitVec 64)
    (ho : owned = sig.gives x ++ frame) : owned = (ret x).owned :=
  (h.each x).owned_back (by
    rw [ho]
    show sig.gives x ++ frame = sig.gives x ++ List.drop (sig.gives x).length (ret x).owned
    rw [h.frame x])

/-- Calling such a function is well typed if there is room for the return
address and the function's stack use, the argument registers hold what the
function expects, the caller owns what the function takes and then `frame`,
and whatever value the function chooses, what it returns is acceptable at
the instruction after the call. -/
theorem call_ok {sig : FnSigEx} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {Γ : Ctx} {ret : BitVec 64 → Ctx} {d : BitVec 32} {m : Nat}
    {frame : List (BitVec 64 × List Ty)}
    (hf : sig.At Φ (next + d.signExtend 64)) (hroom : Γ.room = m + 1)
    (hret : ∀ x, Φ next (ret x))
    (hargs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsIn (Γ.moveSp (-8)).regs r))
    (hsp : Sub ((Γ.regs .rsp).shift (-8)) (sig.regsIn (Γ.moveSp (-8)).regs .rsp))
    (hback : ∀ x,
      CtxSub ((sig.pick x).returned (Γ.moveSp (-8)).regs Γ.stack m (ret x).owned) (ret x))
    (hneed : sig.need ≤ m) (hown : Γ.owned = sig.takes ++ frame)
    (hgives : ∀ x, (ret x).owned.take (sig.gives x).length = sig.gives x)
    (hframe : ∀ x, (ret x).owned.drop (sig.gives x).length = frame) :
    HasType Φ fetch sys Ψ next Γ (.call (.rel d)) :=
  .callAll hroom hret
    ⟨sig.entry (Γ.moveSp (-8)).regs ret Γ.stack m frame,
      hf _ _ _ _ _ ⟨fun x => ⟨hgives x, hback x, hneed⟩, hframe⟩,
      .ofMoved hargs (.refl _) rfl (fun _ _ => trivial) hsp hown⟩

end FnSigEx

/-- A stack with one slot's type weakened is a weakening of the stack. -/
theorem SubList.set {σ : List Ty} {i : Nat} {τ υ : Ty} (hi : σ[i]? = some τ) (h : Sub τ υ) :
    SubList σ (σ.set i υ) := by
  induction σ generalizing i with
  | nil => cases hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact .cons h (.refl _)
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      exact .cons (.refl _) (ih hi)

variable {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- **Choosing where to return.** A return address ready for a family of
contexts may be treated, from here on, as ready for the one of them the
function has decided on. -/
theorem BlockOk.chooseRet {a : BitVec 64} {Γ : Ctx} {i : Nat} {ret : BitVec 64 → Ctx}
    (x : BitVec 64) (hslot : Γ.stack[i]? = some (.codeAll ret))
    (hrest : BlockOk Φ fetch sys Ψ a { Γ with stack := Γ.stack.set i (.code (ret x)) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ _ _ _ _ h =>
    h.sub (Δ := { Γ with stack := Γ.stack.set i (.code (ret x)) })
      ⟨fun _ _ => .refl _, SubList.set hslot (.codeAll ret x), rfl, fun _ hf => hf, .refl _,
        rfl⟩) hrest

/-- A label that allows the entry context for every caller is a function
with that signature. -/
theorem FnSigEx.at_label {L : Type} [DecidableEq L] {prog : List (Asm L)} {base : BitVec 64}
    {T : L → Ctx → Prop} {sig : FnSigEx} {l : L}
    (h : ∀ saved ret rest room frame, sig.CallerOk saved ret rest room frame →
      T l (sig.entry saved ret rest room frame)) :
    sig.At (CodeTy.ofLabels prog base T) (Asm.addr prog base l) :=
  fun saved ret rest room frame hK => .intro (h saved ret rest room frame hK)

end TypedAsm
