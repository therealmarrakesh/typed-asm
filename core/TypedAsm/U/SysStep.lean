import TypedAsm.U.Fresh
import TypedAsm.U.Unmap

/-!
# System calls, as steps on terms

Where the call number is a number written out, what the call does is read
from the system's description, and the context it returns in is given: one
function for each of the few things a call may do, none for any one call.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- The context a call returns in, as terms: `rax` holds the term for what
was handed back, `rcx` the address after the call, `r11` zero; and the flags
are undefined. -/
def CtxS.afterSys (Γ : CtxS) (v : Val) (next : BitVec 64) : CtxS :=
  { Γ with
    regs := ((Γ.regs.set .rax v).set .rcx (.lit next)).set .r11 (.lit 0)
    flags := .lit Flags.unknown }

theorem CtxS.afterSys_den (ρ : Env) (Γ : CtxS) (v : Val) (next : BitVec 64) :
    (Γ.afterSys v next).den ρ = (Γ.den ρ).afterSys (v.den ρ) next := by
  refine ctx_ext ?_ rfl rfl rfl
  funext r
  cases r <;> rfl

/-- **A call that does nothing to the program, as a step on terms**: where
the call number is written out and is such a call's, the context it returns
in, with the name `k` for what it hands back. -/
def sysWorld (Γ : CtxS) (k : Nat) (next : BitVec 64) : Option CtxS :=
  match Γ.regs.rax.lit? with
  | some nr =>
    match linuxKind nr with
    | some .world => some (Γ.afterSys (.var k) next)
    | _ => none
  | none => none

theorem sysWorld_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {ρ : Env} {Γ Γ' : CtxS} {k : Nat} {next : BitVec 64}
    (h : sysWorld Γ k next = some Γ') (hu : Γ.under k = true) :
    Steps fetch sys Ψ .syscall next (Γ.den ρ) fun t Δ =>
      ∃ x, t = next ∧ Δ = Γ'.den (ρ.setVal k x) := by
  unfold sysWorld at h
  split at h
  · next nr hnr =>
    split at h
    · next hk =>
      cases h
      have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
      refine Steps.mono (Steps.world hD (by rw [hkind, hrax]; exact hk)
        (fun _ _ _ _ s _ _ => hpre s)) ?_
      rintro t Δ ⟨rfl, x, rfl⟩
      refine ⟨x, rfl, ?_⟩
      rw [CtxS.afterSys_den, CtxS.den_setVal ρ k x Γ hu]
      show _ = CtxOf.afterSys (Γ.den ρ) ((ρ.setVal k x).val k) t
      rw [Env.setVal_get_self]
    · cases h
  · cases h

/-- Whether the call is one that ends the program: its number written out,
and such a call's. -/
def sysEnds (Γ : CtxS) : Bool :=
  match Γ.regs.rax.lit? with
  | some nr =>
    match linuxKind nr with
    | some .ends => true
    | _ => false
  | none => false

theorem sysEnds_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {ρ : Env} {Γ : CtxS} (h : sysEnds Γ = true) {a len : BitVec 64}
    (hf : fetch a = some (.syscall, len)) (n : Nat) : Ok fetch sys Ψ n a (Γ.den ρ) := by
  unfold sysEnds at h
  split at h
  · next nr hnr =>
    split at h
    · next hk =>
      have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
      exact Ok.ends hD hf (by rw [hkind, hrax]; exact hk) (fun _ _ _ _ s _ _ => hpre s)
    · cases h
  · cases h

end TypedAsm.U
