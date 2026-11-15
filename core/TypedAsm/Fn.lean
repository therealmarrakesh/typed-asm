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

/-- The registers a function must preserve under the System V calling convention. -/
def calleeSaved : Reg → Bool
  | .rbx | .rbp | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

namespace FnSig

/-- The caller left room for the function's own stack use, and possibly more. -/
theorem CallerOk.room_split {sig : FnSig} {saved : Reg → Ty} {ret : Ctx} {rest : List Ty}
    {room : Nat} (h : sig.CallerOk saved ret rest room) : ∃ m, room = m + sig.need :=
  ⟨room - sig.need, by have := h.room; omega⟩

/-- Returning from a function is well typed. -/
theorem ret_ok {sig : FnSig} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {saved : Reg → Ty} {ret : Ctx}
    {rest : List Ty} {room : Nat} (hK : sig.CallerOk saved ret rest room) :
    HasType Φ fetch sys Ψ next (sig.exit saved ret rest room) .ret :=
  .ret rfl (.ofMoved (fun r hr => by have := hK.ret.regs r hr; rwa [returned_regs hr] at this)
    hK.ret.stack hK.ret.room hK.ret.flags (by have := hK.ret.sp; rwa [returned_sp] at this) rfl)

/-- Returning is well typed from any context at least as strong as the
function's exit context. -/
theorem ret_of {sig : FnSig} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {saved : Reg → Ty} {Γ ret : Ctx}
    {rest : List Ty} {room : Nat} (hK : sig.CallerOk saved ret rest room)
    (hregs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsOut saved r))
    (hsp : Sub ((Γ.regs .rsp).shift 8) ((sig.regsOut saved .rsp).shift 8))
    (hstack : Γ.stack = .code ret :: rest) (hroom : Γ.room = room)
    (hown : Γ.owned = ret.owned) :
    HasType Φ fetch sys Ψ next Γ .ret :=
  .ret hstack
    (.ofMoved
      (fun r hr => (hregs r hr).trans (by have := hK.ret.regs r hr; rwa [returned_regs hr] at this))
      hK.ret.stack (by rw [hroom]; exact hK.ret.room) (fun f _ => hK.ret.flags f trivial)
      (hsp.trans (by have := hK.ret.sp; rwa [returned_sp] at this)) hown)

/-- Calling a function is well typed if there is room for the return address
and the function's stack use, the argument registers hold what the function
expects, and what the function returns is acceptable after the call. The
preserved registers keep the types the caller has for them. The blocks the
caller owns must be the ones the function takes, then any others, which it
still owns afterwards behind the ones the function gives back. -/
theorem call_ok {sig : FnSig} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {Γ ret : Ctx} {d : BitVec 32}
    {m : Nat} (hf : sig.At Φ (next + d.signExtend 64)) (hroom : Γ.room = m + 1)
    (hret : Φ next ret)
    (hargs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsIn (Γ.moveSp (-8)).regs r))
    (hsp : Sub ((Γ.regs .rsp).shift (-8)) (sig.regsIn (Γ.moveSp (-8)).regs .rsp))
    (hback : CtxSub (sig.returned (Γ.moveSp (-8)).regs Γ.stack m ret.owned) ret)
    (hneed : sig.need ≤ m) (hgives : ret.owned.take sig.gives.length = sig.gives)
    (hown : Γ.owned = sig.takes ++ ret.owned.drop sig.gives.length) :
    HasType Φ fetch sys Ψ next Γ (.call (.rel d)) :=
  .call hroom hret
    ⟨sig.entry (Γ.moveSp (-8)).regs ret Γ.stack m, hf _ _ _ _ ⟨hgives, hback, hneed⟩,
      .ofMoved hargs (.refl _) rfl (fun _ _ => trivial) hsp hown⟩

/-- Calling a function through a register, field or stack slot that holds a
pointer to it. The pointer's type fixes the types `saved` the function is
entered with for its preserved registers, and the stack `rest` it sees
below the return address; the caller's own must be at least as strong. -/
theorem callInd_ok {sig : FnSig} {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {next : BitVec 64} {Γ ret : Ctx} {rm : RM} {saved : Reg → Ty} {rest : List Ty} {m : Nat}
    (hf : Holds Ψ next Γ rm (.code (sig.entry saved ret rest m))) (hroom : Γ.room = m + 1)
    (hret : Φ next ret) (hargs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (sig.regsIn saved r))
    (hsp : Sub ((Γ.regs .rsp).shift (-8)) (sig.regsIn saved .rsp))
    (hstack : SubList Γ.stack rest)
    (hown : Γ.owned = sig.takes ++ ret.owned.drop sig.gives.length) :
    HasType Φ fetch sys Ψ next Γ (.call (.ind rm)) :=
  .callInd hf hroom hret
    (.ofMoved hargs (.cons (.refl _) hstack) rfl (fun _ _ => trivial) hsp hown)

end FnSig

end TypedAsm
