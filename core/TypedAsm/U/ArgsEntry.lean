import TypedAsm.ArgText
import TypedAsm.U.Blocks

/-!
# A program started with arguments

What the kernel puts on a new program's stack: how many arguments, the
address of each one's text, four more words, and the texts. As the program
finds it: the count held at the stack pointer; after it a block others may
point into, whose values are the addresses and whose text is the texts; and
the rest of the stack's memory, plain bytes.
-/

namespace TypedAsm.U

open TypedAsm

/-- The typed values of the block of addresses: one for each argument, the
address of a byte of text. -/
def argvVals : Nat → Nat → List (Nat × Ty)
  | _, 0 => []
  | o, n + 1 => (o, Ty.str 0) :: argvVals (o + 8) n

theorem argvVals_mem : (o n i : Nat) → i < n → (o + 8 * i, Ty.str 0) ∈ argvVals o n
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | o, n + 1, 0, _ => List.mem_cons_self
  | o, n + 1, i + 1, h => by
    have := argvVals_mem (o + 8) n i (Nat.lt_of_succ_lt_succ h)
    rw [show o + 8 * (i + 1) = o + 8 + 8 * i by omega]
    exact List.mem_cons_of_mem _ this

theorem argvVals_spec : (o n : Nat) → ∀ p ∈ argvVals o n,
    ∃ i, i < n ∧ p = (o + 8 * i, Ty.str 0)
  | _, 0, p, h => nomatch h
  | o, n + 1, p, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, Nat.succ_pos _, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := argvVals_spec (o + 8) n p h
      exact ⟨i + 1, Nat.succ_lt_succ hi, by rw [show o + 8 * (i + 1) = o + 8 + 8 * i by omega]⟩

/-- The block after the count: an address for each argument, four more
words, and then the texts as its text. -/
def argvLayout (args : List (List Byte)) : Layout :=
  ⟨⟨8 * (argsGiven args).length + 32, argvVals 0 (argsGiven args).length⟩, false, none,
    (textBytes (argsGiven args)).length, none⟩

/-- The rest of the stack's memory: plain bytes that may be written. -/
def restLayout (args : List (List Byte)) : Layout :=
  ⟨⟨0x10000 - (argBytes args).length, []⟩, true, none, 0, none⟩

/-- The two blocks of a stack that holds arguments. -/
def argBlocks (args : List (List Byte)) : List (BitVec 64 × Layout) :=
  [(argBase + 8, argvLayout args),
   (argBase + BitVec.ofNat 64 (argBytes args).length, restLayout args)]

theorem argBytes_length (args : List (List Byte)) :
    (argBytes args).length
      = 8 * ((argsGiven args).length + 5) + (textBytes (argsGiven args)).length :=
  argBlock_length _

theorem argvLayout_size (args : List (List Byte)) :
    (argvLayout args).size = (argBytes args).length - 8 := by
  rw [argBytes_length]
  simp only [argvLayout, Layout.size]
  omega

/-- The texts, where there are any, end in a byte of nought. -/
theorem textBytes_last : (ts : List (List Byte)) → ts ≠ [] →
    (textBytes ts)[(textBytes ts).length - 1]? = some 0
  | [], h => absurd rfl h
  | [t], _ => by
    show (t ++ [0])[(t ++ [0]).length - 1]? = some 0
    simp
  | t :: u :: ts, _ => by
    have ih := textBytes_last (u :: ts) (by simp)
    have hpos : 0 < (textBytes (u :: ts)).length := by
      rw [textBytes_length_cons]
      omega
    show (t ++ 0 :: textBytes (u :: ts))[(t ++ 0 :: textBytes (u :: ts)).length - 1]? = some 0
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_append, List.length_cons]
    rw [show t.length + ((textBytes (u :: ts)).length + 1) - 1 - t.length
        = ((textBytes (u :: ts)).length - 1) + 1 by omega, List.getElem?_cons_succ]
    exact ih

/-- The state a program is started in with arguments: the program in
memory, the stack given and the arguments on it, and the instruction
pointer at the entry; in any outside world. -/
def argsState (p : State) (e : BitVec 64) (args : List (List Byte)) (w : World) : State :=
  { p.withArgs 0 args with rip := e, world := w }

section
variable (p : State) (e : BitVec 64) (args : List (List Byte)) (w : World)

theorem argsState_rsp : (argsState p e args w).getReg .rsp = argBase :=
  State.getReg_withArgs p 0 args

/-- The stack's memory may be read and written. -/
theorem argsState_perm {x : BitVec 64} (h1 : argBase.toNat ≤ x.toNat)
    (h2 : x.toNat < argBase.toNat + 0x10000) : (argsState p e args w).perm x = .rw :=
  State.perm_withArgs_in p 0 args (by omega) (by omega) h2

theorem argsState_canWrite {a : BitVec 64} {n : Nat} (h1 : argBase.toNat ≤ a.toNat)
    (h2 : a.toNat + n ≤ argBase.toNat + 0x10000) : (argsState p e args w).canWrite a n = true := by
  have hb : argBase.toNat = 0x7fff0000 := rfl
  refine State.canWrite_iff.mpr fun k hk => ?_
  rw [argsState_perm p e args w (by bv_omega) (by bv_omega)]
  rfl

theorem argsState_canRead {a : BitVec 64} {n : Nat} (h1 : argBase.toNat ≤ a.toNat)
    (h2 : a.toNat + n ≤ argBase.toNat + 0x10000) : (argsState p e args w).canRead a n = true := by
  have hb : argBase.toNat = 0x7fff0000 := rfl
  refine State.canRead_iff.mpr fun k hk => ?_
  rw [argsState_perm p e args w (by bv_omega) (by bv_omega)]
  rfl

/-- The arguments' bytes are on the stack. -/
theorem argsState_data : (argsState p e args w).HasData argBase (argBytes args) :=
  (State.hasData_withArgs p 0 args).congr rfl

/-- Below the stack, memory and permissions are the program's. -/
theorem argsState_mem_below {x : BitVec 64} (hx : x.toNat < argBase.toNat) :
    (argsState p e args w).mem x = p.mem x :=
  State.mem_withArgs_below p 0 args hx

end

end TypedAsm.U
