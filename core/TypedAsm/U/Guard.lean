import TypedAsm.Divide
import TypedAsm.U.FlagsS
import TypedAsm.U.Bridge
import TypedAsm.U.Learn

/-!
# What an instruction needs so as not to fault of itself

Most instructions fault only if memory they touch may not be touched. A
few can fault for a reason of their own: an operation that takes a flag in,
where the flag is undefined; a divide, by its divisor. An instruction's
description says which, as data. Here is whether it holds, as far as the
term for the flags shows, and that an instruction of which it holds does
not fault of itself.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall}

/-- The divisors an unsigned divide does not fault on, its high half being
nought: all but nought. -/
def _root_.TypedAsm.Width.nonZero : Width → Range
  | .w32 => ⟨1, 0xffffffff⟩
  | .w64 => ⟨1, -1⟩

/-- The divisors a signed divide does not fault on, its high half being the
sign of its low: all but nought and minus one. -/
def _root_.TypedAsm.Width.divisor : Width → Range
  | .w32 => ⟨1, 0xfffffffe⟩
  | .w64 => ⟨1, -2⟩

theorem Width.nonZero_low {w : Width} {x : BitVec 64} (h : w.nonZero.has x) :
    x.setWidth w.bits ≠ 0 := by
  cases w with
  | w32 =>
    intro h0
    have h0 : BitVec.setWidth 32 x = 0#32 := h0
    simp only [Range.has, Width.nonZero] at h
    bv_omega
  | w64 =>
    intro h0
    have h0 : BitVec.setWidth 64 x = 0#64 := h0
    simp only [Range.has, Width.nonZero] at h
    bv_omega

theorem Width.divisor_low {w : Width} {x : BitVec 64} (h : w.divisor.has x) :
    x.setWidth w.bits ≠ 0 ∧ x.setWidth w.bits ≠ -1 := by
  cases w with
  | w32 =>
    simp only [Range.has, Width.divisor] at h
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have h0 : BitVec.setWidth 32 x = 0#32 := h0
      bv_omega
    · have h0 : BitVec.setWidth 32 x = -1#32 := h0
      bv_omega
  | w64 =>
    simp only [Range.has, Width.divisor] at h
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have h0 : BitVec.setWidth 64 x = 0#64 := h0
      bv_omega
    · have h0 : BitVec.setWidth 64 x = -1#64 := h0
      bv_omega

/-- **Whether what an instruction needs so as not to fault of itself
holds**, as far as the context shows: of the flags by their term, of a
divisor by the range it is known to lie in. -/
def GuardE.okS (Γ : CtxS) : GuardE → FlagsT → Val → Val → Val → Bool
  | .none, _, _, _, _ => true
  | .cond c, fl, _, _, _ => fl.decides c
  | .alu op _, fl, _, _, _ => if op.carryIn then fl.defined .cf else true
  | .mul .mul _, _, _, _, _ | .mul .imul _, _, _, _, _ => true
  | .mul .div w, _, hi, _, src => Γ.fits hi ⟨0, 0⟩ && Γ.fits src w.nonZero
  | .mul .idiv w, _, hi, lo, src => hi == .un (.signFill w) lo && Γ.fits src w.divisor

theorem GuardE.okS_den {ρ : Env} {Γ : CtxS} {g : GuardE} {fl : FlagsT} {hi lo src : Val}
    (h : g.okS Γ fl hi lo src = true) {Ψ' : MemTy} {n : Nat}
    (hk : ∀ f ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n f.2 f.1) :
    g.eval (fl.den ρ) (hi.den ρ) (lo.den ρ) (src.den ρ) = true := by
  cases g with
  | none => rfl
  | cond cnd =>
    obtain ⟨v, hv⟩ := FlagsT.decides_den ρ fl cnd h
    show (cnd.eval (fl.den ρ)).isSome = true
    rw [hv]; rfl
  | alu op w =>
    cases op <;> first
      | rfl
      | (obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (FlagsT.defined_den ρ fl .cf h)
         have hv : (fl.den ρ).cf = some v := hv
         show (AluOp.eval _ (fl.den ρ).cf _ _).isSome = true
         rw [hv]; rfl)
  | mul op w =>
    cases op with
    | mul => rfl
    | imul => rfl
    | div =>
      simp only [GuardE.okS, Bool.and_eq_true] at h
      have h0 := CtxS.fits_has h.1 hk
      have hs := CtxS.fits_has h.2 hk
      have hhi : hi.den ρ = 0 := by
        simp only [Range.has] at h0
        bv_omega
      show (match MulDivOp.eval .div ((hi.den ρ).setWidth w.bits) ((lo.den ρ).setWidth w.bits)
          ((src.den ρ).setWidth w.bits) with
        | .next _ => true
        | _ => false) = true
      have hb := Width.nonZero_low hs
      rw [hhi, show BitVec.setWidth w.bits (0 : BitVec 64) = 0 by cases w <;> rfl,
        MulDivOp.eval_div _ _ hb]
    | idiv =>
      simp only [GuardE.okS, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hs⟩ := h
      have hs := CtxS.fits_has hs hk
      show (match MulDivOp.eval .idiv
          ((wide (signFill ((lo.den ρ).setWidth w.bits))).setWidth w.bits)
          ((lo.den ρ).setWidth w.bits) ((src.den ρ).setWidth w.bits) with
        | .next _ => true
        | _ => false) = true
      have hb := Width.divisor_low hs
      rw [wide_low, MulDivOp.eval_idiv _ _ hb.1 (.inr hb.2)]

end TypedAsm.U
