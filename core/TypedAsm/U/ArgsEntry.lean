import TypedAsm.ArgText
import TypedAsm.U.Blocks
import TypedAsm.U.Stack

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

/-- **The context a program started with arguments starts in**, as a
family: at the stack pointer, eight bytes held that hold a count; after
them a row of that many pointers to text; every register and the flags
whatever they are. -/
def entryArgs : CtxS where
  regs := ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3, .bvar 0 4, .bvar 0 5, .bvar 0 6, .bvar 0 7,
    .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13, .bvar 0 14, .bvar 0 15⟩
  flags := .bvar 0
  held := [(.bvar 0 4, ⟨8, [(0, .bvar 0 16)]⟩)]
  known := [(.add (.bvar 0 4) (.lit 8), .arr (.bvar 0 16) (.str (.lit 0)))]
  rest := .none

/-- The member of that family a state is, the count being `c`. -/
def Fam.ofArgs (s : State) (c : BitVec 64) : Fam where
  vals := fun i => if i = 16 then c else (Fam.ofState s).vals i
  flags := s.flags
  rest := []

/-- **A state starts as that context asks** where its blocks may be read
and written as they say, the eight bytes at its stack pointer may be
written and hold the count, they are apart from every block, and every byte
it can touch is one of them or a block's. -/
theorem starts_args {s : State} {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (ρ : Env) {c : BitVec 64}
    (hperm : ∀ x ∈ blocks,
      s.canRead x.1 x.2.size = true ∧ (x.2.writable = true → s.canWrite x.1 x.2.size = true))
    (hsaid : ∀ x ∈ blocks, ∀ bs : List (BitVec 8), x.2.said = some bs →
      ∀ k (hk : k < bs.length), s.mem (x.1 + BitVec.ofNat 64 k) = bs[k])
    (htext : ∀ x ∈ blocks, x.2.text ≠ 0 → s.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0)
    (hw : s.canWrite (s.getReg .rsp) 8 = true) (hc : s.load64 (s.getReg .rsp) = c)
    (hapart : ∀ x ∈ blocks, Disjoint (s.getReg .rsp) 8 x.1 x.2.size)
    (hcomplete : ∀ a : BitVec 64, s.perm a ≠ .none →
      (a - s.getReg .rsp).toNat < 8 ∨ ∃ x ∈ blocks, (a - x.1).toNat < x.2.size) :
    Starts blocks kinds (entryArgs.den { ρ with bound := Fam.ofArgs s c :: ρ.bound }) s where
  val := fun r => by cases r <;> rfl
  flags := rfl
  perms := hperm
  text := htext
  said := hsaid
  held := by
    have hheld : (entryArgs.den { ρ with bound := Fam.ofArgs s c :: ρ.bound }).held
        = [(s.getReg .rsp, ⟨8, [(0, c)]⟩)] := rfl
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb p hp => ?_, fun b hb p hp => ?_,
      fun b hb a l hl => ?_, ?_⟩
    · rw [hheld] at hb; cases List.mem_singleton.mp hb; exact hw
    · rw [hheld] at hb
      cases List.mem_singleton.mp hb
      exact (by decide : (8 : Nat) < 2 ^ 64)
    · rw [hheld] at hb
      cases List.mem_singleton.mp hb
      cases List.mem_singleton.mp hp
      exact Nat.le_refl _
    · rw [hheld] at hb
      cases List.mem_singleton.mp hb
      cases List.mem_singleton.mp hp
      show s.load64 (s.getReg .rsp + BitVec.ofNat 64 0) = c
      rw [show s.getReg .rsp + BitVec.ofNat 64 0 = s.getReg .rsp by simp]
      exact hc
    · rw [hheld] at hb
      cases List.mem_singleton.mp hb
      exact hapart (a, l) (MemTy.mem_of_ofList hl)
    · rw [hheld]; exact List.pairwise_singleton _ _
  complete := fun a ha => by
    rcases hcomplete a ha with h | ⟨x, hx, h⟩
    · exact .inl ⟨(s.getReg .rsp, ⟨8, [(0, c)]⟩), List.mem_singleton.mpr rfl, h⟩
    · exact .inr ⟨x, hx, h⟩

/-- Two ranges of bytes, one wholly before the other, are apart. -/
theorem disjoint_of_before {a b : BitVec 64} {n m : Nat} (h1 : a.toNat + n ≤ b.toNat)
    (h2 : b.toNat + m ≤ 18446744073709551616) : Disjoint a n b m := by
  have ha := a.isLt
  have hb := b.isLt
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_sub]
    have : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
    omega
  · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_sub]
    have : m % 2 ^ 64 = m := Nat.mod_eq_of_lt (by omega)
    omega

section
variable (p : State) (e : BitVec 64) (args : List (List Byte)) (w : World)

/-- The count is at the stack pointer. -/
theorem argsState_count :
    (argsState p e args w).load64 ((argsState p e args w).getReg .rsp) = argCount args := by
  rw [argsState_rsp]
  have h := (argsState_data p e args w).load64 (i := 0) (by
    rw [argBytes_length]
    omega)
  rw [show argBase + BitVec.ofNat 64 0 = argBase by simp] at h
  rw [h]
  exact word64_le64 _ _

/-- **The state a program is started in with arguments starts as the
entry asks**, under the blocks of the program below the stack and the two
of the stack: where the program's blocks may be read and written as they
say, hold what they say, lie below the stack, and with the stack's memory
are all the memory there is. -/
theorem starts_argsState (ρ : Env) {B : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (hB : ∀ x ∈ B, (argsState p e args w).canRead x.1 x.2.size = true ∧
      (x.2.writable = true → (argsState p e args w).canWrite x.1 x.2.size = true))
    (hBsaid : ∀ x ∈ B, ∀ bs : List (BitVec 8), x.2.said = some bs →
      ∀ k (hk : k < bs.length), (argsState p e args w).mem (x.1 + BitVec.ofNat 64 k) = bs[k])
    (hBtext : ∀ x ∈ B, x.2.text ≠ 0 →
      (argsState p e args w).mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0)
    (hBbelow : ∀ x ∈ B, x.1.toNat + x.2.size ≤ argBase.toNat)
    (hcov : ∀ a : BitVec 64, (argsState p e args w).perm a ≠ .none →
      (argBase.toNat ≤ a.toNat ∧ a.toNat < argBase.toNat + 0x10000) ∨
        ∃ x ∈ B, (a - x.1).toNat < x.2.size) :
    Starts (B ++ argBlocks args) kinds
      (entryArgs.den
        { ρ with bound := Fam.ofArgs (argsState p e args w) (argCount args) :: ρ.bound })
      (argsState p e args w) := by
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hL := argBytes_length_le args
  have hL' := argBytes_length args
  have hsz := argvLayout_size args
  have hA8 : (argBase + 8).toNat = 0x7fff0008 := rfl
  have hAL : (argBase + BitVec.ofNat 64 (argBytes args).length).toNat
      = 0x7fff0000 + (argBytes args).length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase]
    omega
  have hrest : (restLayout args).size = 0x10000 - (argBytes args).length := by
    simp only [restLayout, Layout.size]
    omega
  have hmemArg : ∀ x ∈ argBlocks args,
      x = (argBase + 8, argvLayout args) ∨
        x = (argBase + BitVec.ofNat 64 (argBytes args).length, restLayout args) := by
    intro x hx
    simpa only [argBlocks, List.mem_cons, List.not_mem_nil, or_false] using hx
  refine starts_args ρ (fun x hx => ?_) (fun x hx bs hs => ?_) (fun x hx ht => ?_) ?_
    (argsState_count p e args w) (fun x hx => ?_) (fun a ha => ?_)
  · rcases List.mem_append.mp hx with hx | hx
    · exact hB x hx
    · rcases hmemArg x hx with rfl | rfl
      · exact ⟨argsState_canRead p e args w (a := argBase + 8) (n := (argvLayout args).size)
          (by omega) (by omega), fun h => nomatch h⟩
      · exact ⟨argsState_canRead p e args w
            (a := argBase + BitVec.ofNat 64 (argBytes args).length) (n := (restLayout args).size)
            (by omega) (by omega),
          fun _ => argsState_canWrite p e args w
            (a := argBase + BitVec.ofNat 64 (argBytes args).length) (n := (restLayout args).size)
            (by omega) (by omega)⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact hBsaid x hx bs hs
    · rcases hmemArg x hx with rfl | rfl <;> cases hs
  · rcases List.mem_append.mp hx with hx | hx
    · exact hBtext x hx ht
    · rcases hmemArg x hx with rfl | rfl
      · have ht' : (textBytes (argsGiven args)).length ≠ 0 := ht
        have hne : argsGiven args ≠ [] := by
          intro h0
          rw [h0] at ht'
          exact ht' rfl
        have hlast := textBytes_last _ hne
        have hk : (argBytes args).length - 1 < (argBytes args).length := by omega
        have hd := argsState_data p e args w ((argBytes args).length - 1) hk
        have haddr : argBase + 8 + BitVec.ofNat 64 ((argvLayout args).size - 1)
            = argBase + BitVec.ofNat 64 ((argBytes args).length - 1) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add (argBase + 8), hA8, BitVec.toNat_ofNat, BitVec.toNat_add argBase,
            BitVec.toNat_ofNat, hbase]
          omega
        show (argsState p e args w).mem (argBase + 8 + BitVec.ofNat 64 ((argvLayout args).size - 1))
          = 0
        rw [haddr, hd]
        have hat := argBlock_text (argsGiven args) ((textBytes (argsGiven args)).length - 1)
        rw [hlast] at hat
        have hidx : 8 * ((argsGiven args).length + 5) + ((textBytes (argsGiven args)).length - 1)
            = (argBytes args).length - 1 := by omega
        rw [hidx] at hat
        have : (argBytes args)[(argBytes args).length - 1]? = some 0 := hat
        rw [List.getElem?_eq_getElem hk] at this
        exact Option.some.inj this
      · exact absurd rfl ht
  · rw [argsState_rsp]
    exact argsState_canWrite p e args w (by omega) (by omega)
  · rw [argsState_rsp]
    rcases List.mem_append.mp hx with hx | hx
    · exact (disjoint_of_before (hBbelow x hx) (by omega)).symm
    · rcases hmemArg x hx with rfl | rfl
      · exact disjoint_of_before (a := argBase) (n := 8) (b := argBase + 8)
          (m := (argvLayout args).size) (by omega) (by omega)
      · exact disjoint_of_before (a := argBase) (n := 8)
          (b := argBase + BitVec.ofNat 64 (argBytes args).length) (m := (restLayout args).size)
          (by omega) (by omega)
  · rw [argsState_rsp]
    rcases hcov a ha with ⟨h1, h2⟩ | ⟨x, hx, h⟩
    · by_cases hk8 : a.toNat < argBase.toNat + 8
      · exact .inl (by rw [BitVec.toNat_sub]; omega)
      · by_cases hkL : a.toNat < argBase.toNat + (argBytes args).length
        · refine .inr ⟨_, List.mem_append_right _ (List.mem_cons_self), ?_⟩
          show (a - (argBase + 8)).toNat < (argvLayout args).size
          rw [BitVec.toNat_sub, hA8]
          omega
        · refine .inr ⟨_, List.mem_append_right _
            (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
          show (a - (argBase + BitVec.ofNat 64 (argBytes args).length)).toNat
            < (restLayout args).size
          rw [BitVec.toNat_sub, hAL]
          omega
    · exact .inr ⟨x, List.mem_append_left _ hx, h⟩

end

end TypedAsm.U
