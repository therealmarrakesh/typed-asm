import FactProgram
import TypedAsm.U.Checked

/-!
# Fact: typing, safety, and what it computes

The program is in `FactProgram.lean`. This file says what its labels want
and checks it: one check, run as compiled code, that the code is typed and
that the state the kernel loads the program into starts as its entry asks.

The function has a label of its own, so it is typed once, for every
argument and every caller. The label says three things the checker could
not find for itself:

* how much stack a call needs: sixteen bytes for each unit of its argument,
  the argument and a return address pushed at each level;
* that the argument is small enough for that to be a number of bytes;
* what the function returns: the factorial of its argument.

The factorial is a function defined here, in Lean. The checker does not
look into it. It is told two laws of it, which are proved below as any
theorem is: the factorial of nought is one; and the factorial of a number
that is not nought is that number times the factorial of one less. Where
the function returns, the checker finds that what the machine computed is
what the label says by matching a law.

With that, the program is proved to end with 120: at the one call the
program makes, the argument is five, and the check computes the
factorial of five.

It is kept separate so that running the program does not link the checker.
-/

open TypedAsm TypedAsm.U

namespace Fact

/-! ## The factorial, and what is proved of it -/

/-- The factorial of a number. -/
def facNat : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * facNat n

/-- The functions of this program: one, the factorial, as 64-bit values. -/
def fns : Nat → BitVec 64 → BitVec 64 → BitVec 64 :=
  fun _ a _ => BitVec.ofNat 64 (facNat a.toNat)

/-- The factorial of a term. -/
def fac (x : Val) : Val := .app 0 x 0

/-- The laws: of a value `x` that is nought, `fac x` is one; of one that is
not, `fac (x - 1)` times `x`, as the machine multiplies, is `fac x`. -/
def laws : List LawS :=
  [⟨[(.named 0, 0, 0)], fac (.named 0), 1⟩,
   ⟨[(.named 0, 1, -1)],
     .bin (.imul .w64) (fac (.add (.named 0) (.lit (-1)))) (.named 0), fac (.named 0)⟩]

/-- **The laws are so.** -/
theorem lawsHold : LawsHold fns laws := by
  intro l hl ρ hfn hpre
  simp only [laws, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · have hx : Range.has ⟨0, 0⟩ ((Val.named 0).den ρ) := hpre (.named 0, 0, 0) List.mem_cons_self
    have h0 : (Val.named 0).den ρ = 0 := by
      simp only [Range.has] at hx
      bv_omega
    show ρ.fn 0 ((Val.named 0).den ρ) 0 = 1
    rw [hfn, h0]
    rfl
  · have hx : Range.has ⟨1, -1⟩ ((Val.named 0).den ρ) :=
      hpre (.named 0, 1, -1) List.mem_cons_self
    show Bin.eval (.imul .w64) (ρ.fn 0 ((Val.named 0).den ρ + -1) 0) ((Val.named 0).den ρ)
      = ρ.fn 0 ((Val.named 0).den ρ) 0
    generalize (Val.named 0).den ρ = v at hx
    have hv : v ≠ 0 := by
      intro h0
      subst h0
      simp [Range.has] at hx
    rw [imul64, hfn]
    show BitVec.ofNat 64 (facNat (v + -1).toNat) * v = BitVec.ofNat 64 (facNat v.toNat)
    obtain ⟨m, hm⟩ : ∃ m, v.toNat = m + 1 := ⟨v.toNat - 1, by
      have : v.toNat ≠ 0 := fun h => hv (BitVec.eq_of_toNat_eq h)
      omega⟩
    have h1 : (v + -1).toNat = m := by bv_omega
    rw [h1, hm]
    show _ = BitVec.ofNat 64 ((m + 1) * facNat m)
    rw [BitVec.ofNat_mul, ← hm, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.mul_comm]

/-! ## What the labels want -/

/-- The program for the checker: its instructions; that it is to end with
status 120, the factorial of five; its function, and the laws. -/
def pg : Prog :=
  { code := progCode (Asm.table base code)
    pre := preExits (· == 120)
    fns := fns
    laws := laws }

/-- The labels: the start, with nothing known; and the function, of an
argument small enough, wanting sixteen bytes of stack for each unit of it,
and returning its factorial. -/
def labels : List U.Label :=
  [⟨entry, inProgram 11⟩,
   ⟨Asm.addr code base .fact,
     inFunction (known := [(.was .rdi, .range 0 0xFFFFFFF)]) (room := (Val.was .rdi) <<< 4)
       (results := [(.rax, fac (Val.was .rdi).lift)])⟩]

/-! ## The check, and what it shows -/

asm_checked code start .start stack 11 program pg labels labels exits (· == 120)
  laws lawsHold

end Fact
