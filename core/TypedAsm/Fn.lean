import TypedAsm.Typing

/-!
# Function types

The standard shape of a function's typing: what it expects in the registers,
what it leaves in them, which registers it preserves, and how much stack it
uses. A function with a signature is typed once, for every caller: every
return context, every caller stack, and every choice of types for the
preserved registers.
-/

namespace TypedAsm

/-- A function signature. -/
structure FnSig where
  /-- The types expected in the registers on entry. -/
  args : Reg → Ty
  /-- The types left in the registers on return. -/
  results : Reg → Ty
  /-- The registers whose types are the same on return as on entry, whatever
  they were. `args` and `results` are ignored for these. -/
  preserved : Reg → Bool
  /-- The number of stack slots the function uses below its return address. -/
  need : Nat

/-- The registers a function must preserve under the System V calling convention. -/
def calleeSaved : Reg → Bool
  | .rbx | .rbp | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

namespace FnSig

/-- Register types on entry, when the preserved registers have types `saved`. -/
def regsIn (sig : FnSig) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if sig.preserved r then saved r else sig.args r

/-- Register types on return, when the preserved registers have types `saved`. -/
def regsOut (sig : FnSig) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if sig.preserved r then saved r else sig.results r

/-- The context at the function's first instruction, for a caller that
expects `ret` on return and has `rest` on its stack. -/
def entry (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) : Ctx :=
  ⟨sig.regsIn saved, .code ret :: rest, room, Flags.Any⟩

/-- The context at the function's `ret` instruction. -/
def exit (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) : Ctx :=
  ⟨sig.regsOut saved, .code ret :: rest, room, Flags.Any⟩

/-- The context the caller is in once the function has returned. -/
def returned (sig : FnSig) (saved : Reg → Ty) (rest : List Ty) (room : Nat) : Ctx :=
  ⟨sig.regsOut saved, rest, room + 1, Flags.Any⟩

/-- What a function needs of its caller: the state it returns must be
acceptable where it returns to, and there must be enough stack. -/
structure CallerOk (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    Prop where
  ret : CtxSub (sig.returned saved rest room) ret
  room : sig.need ≤ room

/-- The caller left room for the function's own stack use, and possibly more. -/
theorem CallerOk.room_split {sig : FnSig} {saved : Reg → Ty} {ret : Ctx} {rest : List Ty}
    {room : Nat} (h : sig.CallerOk saved ret rest room) : ∃ m, room = m + sig.need :=
  ⟨room - sig.need, by have := h.room; omega⟩

/-- `sig.At Φ a`: the code typing lets address `a` be entered as a function
with signature `sig`, by any caller. -/
def At (sig : FnSig) (Φ : CodeTy) (a : BitVec 64) : Prop :=
  ∀ saved ret rest room, sig.CallerOk saved ret rest room → Φ a (sig.entry saved ret rest room)

/-- Returning from a function is well typed. -/
theorem ret_ok {sig : FnSig} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {saved : Reg → Ty} {ret : Ctx}
    {rest : List Ty} {room : Nat} (hK : sig.CallerOk saved ret rest room) :
    HasType Φ fetch sys Ψ next (sig.exit saved ret rest room) .ret :=
  .ret rfl hK.ret

/-- Returning is well typed from any context at least as strong as the
function's exit context. -/
theorem ret_of {sig : FnSig} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {saved : Reg → Ty} {Γ ret : Ctx}
    {rest : List Ty} {room : Nat} (hK : sig.CallerOk saved ret rest room)
    (hregs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsOut saved r))
    (hstack : Γ.stack = .code ret :: rest) (hroom : Γ.room = room) :
    HasType Φ fetch sys Ψ next Γ .ret :=
  .ret hstack
    ⟨fun r hr => (hregs r hr).trans (hK.ret.regs r hr), hK.ret.stack,
      by rw [hroom]; exact hK.ret.room, fun f _ => hK.ret.flags f trivial⟩

/-- Calling a function is well typed if there is room for the return address
and the function's stack use, the argument registers hold what the function
expects, and what the function returns is acceptable after the call. The
preserved registers keep the types the caller has for them. -/
theorem call_ok {sig : FnSig} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {Γ ret : Ctx} {d : BitVec 32}
    {m : Nat} (hf : sig.At Φ (next + d.signExtend 64)) (hroom : Γ.room = m + 1)
    (hret : Φ next ret) (hargs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsIn Γ.regs r))
    (hback : CtxSub (sig.returned Γ.regs Γ.stack m) ret) (hneed : sig.need ≤ m) :
    HasType Φ fetch sys Ψ next Γ (.call (.rel d)) :=
  .call hroom hret
    ⟨sig.entry Γ.regs ret Γ.stack m, hf _ _ _ _ ⟨hback, hneed⟩,
      ⟨hargs, .refl _, rfl, fun _ _ => trivial⟩⟩

end FnSig

end TypedAsm
