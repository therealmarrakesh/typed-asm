import TypedAsm.Fn
import TypedAsm.Program

/-!
# Functions that hand back something they made

A function that makes a block and hands it to its caller cannot say in its
signature where the block is: the address is not known until the function
has run. `FnSigEx ι` (in `Types.lean`) is a signature whose results, and the
blocks it gives, depend on a value `x : ι` that the function chooses when it
returns: one address, a pair of them, anything that can be written as a
sequence of 64-bit values (`Chosen`). The place
it returns to must be ready for any `x`; so the return address is typed as
code for a family of contexts (`Ty.codeAll`), and before returning the
function says which one it returns into.
-/

namespace TypedAsm

namespace FnSigEx

variable {ι : Type} [Chosen ι]

omit [Chosen ι] in
/-- At its return into `ret x`, a function that owns the blocks it gives for
`x` and after them what the caller owned besides owns what `ret x` expects. -/
theorem CallerOk.owned_back {sig : FnSigEx ι} {saved : Reg → Ty} {ret : ι → Ctx}
    {rest : List Shape} {room : Nat} {frame owned : List (BitVec 64 × Shape)}
    (h : sig.CallerOk saved ret rest room frame above) (x : ι)
    (ho : owned = sig.gives x ++ frame) : owned = (ret x).owned :=
  (h.each x).owned_back (by
    rw [ho]
    show sig.gives x ++ frame = sig.gives x ++ List.drop (sig.gives x).length (ret x).owned
    rw [h.frame x])

omit [Chosen ι] in
/-- **What the function returns with, at the value it chose, stands for the
context it returns into**: stated with the blocks owned written out, the ones
it gives for that value and then what its caller owned besides, and with
what is detached from the stack as it was on entry. -/
theorem CallerOk.retAt {sig : FnSigEx ι} {saved : Reg → Ty} {ret : ι → Ctx}
    {rest : List Shape} {room : Nat} {frame : List (BitVec 64 × Shape)}
    (h : sig.CallerOk saved ret rest room frame above) (x : ι) :
    CtxSub ((sig.pick x).returned saved rest room (sig.gives x ++ frame) above) (ret x) := by
  have ho := h.owned_back x rfl
  have ha := h.detached x
  have := (h.each x).ret
  rw [← ho, ha] at this
  exact this

/-- The caller left room for the function's own stack use, and possibly more. -/
theorem CallerOk.room_split {sig : FnSigEx ι} {saved : Reg → Ty} {ret : ι → Ctx}
    {rest : List Shape} {room : Nat} {frame : List (BitVec 64 × Shape)}
    (h : sig.CallerOk saved ret rest room frame above) : ∃ m, room = m + sig.need :=
  ⟨room - sig.need, by
    have := (h.each (Chosen.dec fun _ => 0)).room
    have e : (sig.pick (Chosen.dec fun _ => 0)).need = sig.need := rfl
    omega⟩

/-- Calling such a function is well typed if there is room for the return
address and the function's stack use, the argument registers hold what the
function expects, the caller owns what the function takes and then `frame`,
and whatever value the function chooses, what it returns is acceptable at
the instruction after the call. -/
theorem call_ok {sig : FnSigEx ι} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {Γ : Ctx} {ret : ι → Ctx} {d : BitVec 32} {m : Nat}
    {frame : List (BitVec 64 × Shape)}
    (hf : sig.At Φ (next + d.signExtend 64)) (hroom : Γ.room = m + 8)
    (hret : ∀ x, Φ next (ret x))
    (hargs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsIn (Γ.moveSp (-8)).regs r))
    (hsp : Sub ((Γ.regs .rsp).shift (-8)) (sig.regsIn (Γ.moveSp (-8)).regs .rsp))
    (hback : ∀ x,
      CtxSub ((sig.pick x).returned (Γ.moveSp (-8)).regs Γ.stack m (ret x).owned Γ.above) (ret x))
    (hneed : sig.need ≤ m) (hown : Γ.owned = sig.takes ++ frame)
    (hgives : ∀ x, (ret x).owned.take (sig.gives x).length = sig.gives x)
    (hframe : ∀ x, (ret x).owned.drop (sig.gives x).length = frame) :
    HasType Φ fetch sys Ψ next Γ (.call (.rel d)) :=
  .callAll hroom (fun s => hret (Chosen.dec s))
    ⟨sig.entry (Γ.moveSp (-8)).regs ret Γ.stack m frame Γ.above,
      hf _ _ _ _ _ _ ⟨fun x => .ofBack (hgives x) (hback x) hneed, hframe,
        fun x => (hback x).above.symm⟩,
      .ofMoved hargs (.refl _) rfl (fun _ _ => trivial) hsp hown⟩

end FnSigEx

/-- A stack with one piece weakened is a weakening of the stack. -/
theorem SubList.set {σ : List Shape} {i : Nat} {S T : Shape} (hi : σ[i]? = some S)
    (h : SubShape S T) : SubList σ (σ.set i T) := by
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
theorem BlockOk.chooseRet {ι : Type} [Chosen ι] {a : BitVec 64} {Γ : Ctx} {i : Nat}
    {ret : ι → Ctx} (x : ι)
    (hslot : Γ.stack[i]? = some (.slot (.codeAll fun s => ret (Chosen.dec s))))
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.set i (.slot (.code (ret x))) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .weaken (fun _ _ _ _ _ h =>
    h.sub (Δ := { Γ with stack := Γ.stack.set i (.slot (.code (ret x))) })
      ⟨fun _ _ => .refl _,
        SubList.set hslot (.slot (by
          have := Sub.codeAll (fun s => ret (Chosen.dec s)) (Chosen.enc x)
          rwa [Chosen.dec_enc] at this)),
        rfl, fun _ hf => hf, .refl _, rfl, rfl⟩) hrest

/-- Code ready for a family of contexts given by the value a function
chooses is ready for the context at any one value. -/
theorem Sub.codeAll_at {ι : Type} [Chosen ι] (ret : ι → Ctx) (x : ι) :
    Sub (.codeAll fun s => ret (Chosen.dec s)) (.code (ret x)) := by
  have := Sub.codeAll (fun s => ret (Chosen.dec s)) (Chosen.enc x)
  rwa [Chosen.dec_enc] at this

end TypedAsm
