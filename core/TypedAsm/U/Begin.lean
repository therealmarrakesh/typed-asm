import TypedAsm.ArgWords
import TypedAsm.U.Blocks

/-!
# Where a program begins

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

/-- Where the stack's pages start, of a program given so many slots below
its arguments. -/
def stackLow (n : Nat) : Nat := 4096 * ((0x7fff0000 - 8 * n) / 4096)

/-- How many bytes of stack such a program has below its arguments: the
slots it is given, to whole pages. -/
def stackRoom (n : Nat) : Nat := 0x7fff0000 - stackLow n

theorem stackLow_le (n : Nat) : stackLow n ≤ 0x7fff0000 := by
  unfold stackLow
  omega

theorem stackLow_room (n : Nat) : stackLow n + stackRoom n = 0x7fff0000 := by
  have := stackLow_le n
  unfold stackRoom
  omega

/-- The state a program is started in with arguments: the program in
memory, the stack given, so many slots below the arguments on it, and the
instruction pointer at the entry; in any outside world. -/
def startState (p : State) (e : BitVec 64) (n : Nat) (args : List (List Byte)) (w : World) :
    State :=
  { p.withArgs n args with rip := e, world := w }

section
variable (p : State) (e : BitVec 64) (n : Nat) (args : List (List Byte)) (w : World)

theorem argsState_rsp : (startState p e n args w).getReg .rsp = argBase :=
  State.getReg_withArgs p n args

/-- The stack's memory may be read and written. -/
theorem argsState_perm (hn : 8 * n ≤ 0x7fff0000) {x : BitVec 64} (h1 : stackLow n ≤ x.toNat)
    (h2 : x.toNat < argBase.toNat + 0x10000) : (startState p e n args w).perm x = .rw :=
  State.perm_withArgs_in p n args hn h1 h2

theorem argsState_canWrite (hn : 8 * n ≤ 0x7fff0000) {a : BitVec 64} {m : Nat}
    (h1 : stackLow n ≤ a.toNat) (h2 : a.toNat + m ≤ argBase.toNat + 0x10000) :
    (startState p e n args w).canWrite a m = true := by
  have hb : argBase.toNat = 0x7fff0000 := rfl
  refine State.canWrite_iff.mpr fun k hk => ?_
  rw [argsState_perm p e n args w hn (by bv_omega) (by bv_omega)]
  rfl

theorem argsState_canRead (hn : 8 * n ≤ 0x7fff0000) {a : BitVec 64} {m : Nat}
    (h1 : stackLow n ≤ a.toNat) (h2 : a.toNat + m ≤ argBase.toNat + 0x10000) :
    (startState p e n args w).canRead a m = true := by
  have hb : argBase.toNat = 0x7fff0000 := rfl
  refine State.canRead_iff.mpr fun k hk => ?_
  rw [argsState_perm p e n args w hn (by bv_omega) (by bv_omega)]
  rfl

/-- The arguments' bytes are on the stack. -/
theorem argsState_data : (startState p e n args w).HasData argBase (argBytes args) :=
  (State.hasData_withArgs p n args).congr rfl

/-- Below the arguments, memory is the program's. -/
theorem argsState_mem_below {x : BitVec 64} (hx : x.toNat < argBase.toNat) :
    (startState p e n args w).mem x = p.mem x :=
  State.mem_withArgs_below p n args hx

end

/-- **The context a program starts in**, as a
family: a region held of so many bytes of stack and eight more, the stack
pointer at those eight, which hold a count; after them a row of that many
pointers to text; every other register and the flags whatever they are. -/
def entryCtx (room : Nat) : CtxS where
  regs := ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3,
    .add (.bvar 0 17) (litNat room), .bvar 0 5, .bvar 0 6, .bvar 0 7,
    .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13, .bvar 0 14, .bvar 0 15⟩
  flags := .bvar 0
  held := [(.bvar 0 17, ⟨litNat (room + 8), [(litNat room, .bvar 0 18)]⟩)]
  known := [(.add (.add (.bvar 0 17) (litNat room)) (.lit 8), .arr (.bvar 0 18) (.str (.lit 0)) 8)]
  rest := .none

/-- The member of that family a state is, the count being `c` and the
stack's region at `base`. -/
def Fam.ofStart (s : State) (c base : BitVec 64) : Fam where
  vals := fun i => if i = 18 then c else if i = 17 then base else (Fam.ofState s).vals i
  flags := s.flags
  rest := []

/-- The member a state started with these arguments and so many slots is. -/
abbrev startFam (s : State) (n : Nat) (args : List (List Byte)) : Fam :=
  Fam.ofStart s (argCount args) (BitVec.ofNat 64 (stackLow n))

/-- What that context holds, of a member: the stack's region, the count at
its end. -/
theorem entryCtx_held (ρ : Env) (s : State) (c base : BitVec 64) {room : Nat}
    (hsz : room + 8 < 18446744073709551616) :
    ((entryCtx room).den { ρ with bound := Fam.ofStart s c base :: ρ.bound }).held
      = [(base, ⟨room + 8, [(room, c)]⟩)] := by
  show [(base, (⟨(BitVec.ofNat 64 (room + 8)).toNat, [((BitVec.ofNat 64 room).toNat, c)]⟩ : Held))]
    = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz, Nat.mod_eq_of_lt (by omega)]

/-- **A state starts as that context asks** where its blocks may be read
and written as they say, the stack's region may be written, the stack
pointer is at its last eight bytes and they hold the count, the region is
apart from every block, and every byte the state can touch is in it or in
a block. -/
theorem starts_entry {s : State} {blocks : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (ρ : Env) {c base : BitVec 64} {room : Nat}
    (hperm : ∀ x ∈ blocks,
      s.canRead x.1 x.2.size = true ∧ (x.2.writable = true → s.canWrite x.1 x.2.size = true))
    (hsaid : ∀ x ∈ blocks, ∀ bs : List (BitVec 8), x.2.said = some bs →
      ∀ k (hk : k < bs.length), s.mem (x.1 + BitVec.ofNat 64 k) = bs[k])
    (htext : ∀ x ∈ blocks, x.2.text ≠ 0 → s.mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0)
    (hsz : room + 8 < 18446744073709551616)
    (hrsp : s.getReg .rsp = base + BitVec.ofNat 64 room)
    (hw : s.canWrite base (room + 8) = true) (hc : s.load64 (s.getReg .rsp) = c)
    (hapart : ∀ x ∈ blocks, Disjoint base (room + 8) x.1 x.2.size)
    (hcomplete : ∀ a : BitVec 64, s.perm a ≠ .none →
      (a - base).toNat < room + 8 ∨ ∃ x ∈ blocks, (a - x.1).toNat < x.2.size) :
    Starts blocks kinds ((entryCtx room).den { ρ with bound := Fam.ofStart s c base :: ρ.bound })
      s where
  val := fun r => by
    cases r <;> first | rfl | exact hrsp
  flags := rfl
  perms := hperm
  text := htext
  said := hsaid
  held := by
    have hheld := entryCtx_held ρ s c base hsz
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb p hp => ?_, fun b hb p hp => ?_,
      fun b hb a l hl => ?_, ?_⟩
    · rw [hheld] at hb; cases List.mem_singleton.mp hb; exact hw
    · rw [hheld] at hb; cases List.mem_singleton.mp hb; exact hsz
    · rw [hheld] at hb
      cases List.mem_singleton.mp hb
      cases List.mem_singleton.mp hp
      exact Nat.le_refl _
    · rw [hheld] at hb
      cases List.mem_singleton.mp hb
      cases List.mem_singleton.mp hp
      show s.load64 (base + BitVec.ofNat 64 room) = c
      rw [← hrsp]
      exact hc
    · rw [hheld] at hb
      cases List.mem_singleton.mp hb
      exact hapart (a, l) (MemTy.mem_of_ofList hl)
    · rw [hheld]; exact List.pairwise_singleton _ _
  complete := fun a ha => by
    rw [entryCtx_held ρ s c base hsz]
    rcases hcomplete a ha with h | ⟨x, hx, h⟩
    · exact .inl ⟨(base, ⟨room + 8, [(room, c)]⟩), List.mem_singleton.mpr rfl, h⟩
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
variable (p : State) (e : BitVec 64) (n : Nat) (args : List (List Byte)) (w : World)

/-- The count is at the stack pointer. -/
theorem argsState_count :
    (startState p e n args w).load64 ((startState p e n args w).getReg .rsp) = argCount args := by
  rw [argsState_rsp]
  have h := (argsState_data p e n args w).load64 (i := 0) (by
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
theorem starts_startState (ρ : Env) {B : List (BitVec 64 × Layout)} {kinds : Nat → Option Shape}
    (hB : ∀ x ∈ B, (startState p e n args w).canRead x.1 x.2.size = true ∧
      (x.2.writable = true → (startState p e n args w).canWrite x.1 x.2.size = true))
    (hBsaid : ∀ x ∈ B, ∀ bs : List (BitVec 8), x.2.said = some bs →
      ∀ k (hk : k < bs.length), (startState p e n args w).mem (x.1 + BitVec.ofNat 64 k) = bs[k])
    (hBtext : ∀ x ∈ B, x.2.text ≠ 0 →
      (startState p e n args w).mem (x.1 + BitVec.ofNat 64 (x.2.size - 1)) = 0)
    (hn : 8 * n ≤ 0x7fff0000)
    (hBbelow : ∀ x ∈ B, x.1.toNat + x.2.size ≤ stackLow n)
    (hcov : ∀ a : BitVec 64, (startState p e n args w).perm a ≠ .none →
      (stackLow n ≤ a.toNat ∧ a.toNat < argBase.toNat + 0x10000) ∨
        ∃ x ∈ B, (a - x.1).toNat < x.2.size) :
    Starts (B ++ argBlocks args) kinds
      ((entryCtx (stackRoom n)).den
        { ρ with bound := startFam (startState p e n args w) n args :: ρ.bound })
      (startState p e n args w) := by
  have hlow := stackLow_room n
  have hlowB : (BitVec.ofNat 64 (stackLow n)).toNat = stackLow n := by
    rw [BitVec.toNat_ofNat]
    omega
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
  have hrsp : (startState p e n args w).getReg .rsp
      = BitVec.ofNat 64 (stackLow n) + BitVec.ofNat 64 (stackRoom n) := by
    rw [argsState_rsp]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hbase]
    omega
  refine starts_entry ρ (fun x hx => ?_) (fun x hx bs hs => ?_) (fun x hx ht => ?_) (by omega)
    hrsp ?_ (argsState_count p e n args w) (fun x hx => ?_) (fun a ha => ?_)
  · rcases List.mem_append.mp hx with hx | hx
    · exact hB x hx
    · rcases hmemArg x hx with rfl | rfl
      · exact ⟨argsState_canRead p e n args w hn (a := argBase + 8) (m := (argvLayout args).size)
          (by omega) (by omega), fun h => nomatch h⟩
      · exact ⟨argsState_canRead p e n args w hn
            (a := argBase + BitVec.ofNat 64 (argBytes args).length) (m := (restLayout args).size)
            (by omega) (by omega),
          fun _ => argsState_canWrite p e n args w hn
            (a := argBase + BitVec.ofNat 64 (argBytes args).length) (m := (restLayout args).size)
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
        have hd := argsState_data p e n args w ((argBytes args).length - 1) hk
        have haddr : argBase + 8 + BitVec.ofNat 64 ((argvLayout args).size - 1)
            = argBase + BitVec.ofNat 64 ((argBytes args).length - 1) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add (argBase + 8), hA8, BitVec.toNat_ofNat, BitVec.toNat_add argBase,
            BitVec.toNat_ofNat, hbase]
          omega
        show (startState p e n args w).mem (argBase + 8 + BitVec.ofNat 64 ((argvLayout args).size - 1))
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
  · exact argsState_canWrite p e n args w hn (a := BitVec.ofNat 64 (stackLow n))
      (m := stackRoom n + 8) (by omega) (by omega)
  · rcases List.mem_append.mp hx with hx | hx
    · exact (disjoint_of_before (by have := hBbelow x hx; omega) (by omega)).symm
    · rcases hmemArg x hx with rfl | rfl
      · exact disjoint_of_before (a := BitVec.ofNat 64 (stackLow n)) (n := stackRoom n + 8)
          (b := argBase + 8) (m := (argvLayout args).size) (by omega) (by omega)
      · exact disjoint_of_before (a := BitVec.ofNat 64 (stackLow n)) (n := stackRoom n + 8)
          (b := argBase + BitVec.ofNat 64 (argBytes args).length) (m := (restLayout args).size)
          (by omega) (by omega)
  · rcases hcov a ha with ⟨h1, h2⟩ | ⟨x, hx, h⟩
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

variable {fetch : Fetch} {sys : Syscall}

section
variable (p : State) (e : BitVec 64) (n : Nat) (args : List (List Byte)) (w : World)

/-- **The block after the count is a row of as many pointers to text as
the count says.** -/
theorem argv_known {Ψ : MemTy} (k : Nat) (hΨ : Ψ (argBase + 8) = some (argvLayout args)) :
    HasTy fetch sys Ψ k (.arr (argCount args) (.str 0) 8) (argBase + 8) := by
  refine hasTy_arr.mpr ⟨argBase + 8, argvLayout args, 0, hΨ, by simp, fun i hi => ?_⟩
  have hc : (argCount args).toNat = (argsGiven args).length := by
    have := argsGiven_length_le args
    simp only [argCount, BitVec.toNat_ofNat]
    omega
  rw [hc] at hi
  exact argvVals_mem 0 _ i hi

/-- **Each of its values is the address of a byte of its text.** -/
theorem argv_heap {Ψ : MemTy} (k : Nat) (hΨ : Ψ (argBase + 8) = some (argvLayout args)) :
    ∀ q ∈ (argvLayout args).shape.vals,
      HasTy fetch sys Ψ k q.2
        ((startState p e n args w).load64 (argBase + 8 + BitVec.ofNat 64 q.1)) := by
  intro q hq
  have hbase : argBase.toNat = 0x7fff0000 := rfl
  have hA8 : (argBase + 8).toNat = 0x7fff0008 := rfl
  have hL := argBytes_length_le args
  have hL' := argBytes_length args
  obtain ⟨i, hi, rfl⟩ := argvVals_spec 0 _ q hq
  have hT : i < (textsAt (argsGiven args) (textBase (argsGiven args))).length := by
    rw [textsAt_length]; exact hi
  have hb := textsAt_bounds (argsGiven args) (textBase (argsGiven args)) _
    (List.getElem_mem hT)
  have htb : textBase (argsGiven args) = 0x7fff0000 + 8 * ((argsGiven args).length + 5) := by
    simp only [textBase, hbase]
  have hload : (startState p e n args w).load64 (argBase + 8 + BitVec.ofNat 64 (0 + 8 * i))
      = BitVec.ofNat 64 ((textsAt (argsGiven args) (textBase (argsGiven args)))[i]).1 := by
    have h := (argsState_data p e n args w).load64 (i := 8 * (i + 1)) (by omega)
    have ea : argBase + 8 + BitVec.ofNat 64 (0 + 8 * i) = argBase + BitVec.ofNat 64 (8 * (i + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add (argBase + 8), hA8, BitVec.toNat_ofNat, BitVec.toNat_add argBase,
        BitVec.toNat_ofNat, hbase]
      omega
    rw [ea, h]
    exact argBlock_slot (argsGiven args) i hi
  rw [hload]
  refine hasTy_str.mpr ⟨argBase + 8, argvLayout args,
    ((textsAt (argsGiven args) (textBase (argsGiven args)))[i]).1 - textBase (argsGiven args),
    hΨ, ?_, fun h => absurd rfl h, ?_⟩
  · show _ < (textBytes (argsGiven args)).length
    omega
  · apply BitVec.eq_of_toNat_eq
    show _ = (argBase + 8 + BitVec.ofNat 64 (8 * (argsGiven args).length + 32 + _)).toNat
    rw [BitVec.toNat_ofNat, BitVec.toNat_add (argBase + 8), hA8, BitVec.toNat_ofNat]
    omega

end

end TypedAsm.U
