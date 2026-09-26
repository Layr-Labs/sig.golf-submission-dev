import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChoose67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopyStack67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafInitial67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseH467; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseToInitial67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseH467
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def Outside (a : Word) : Prop :=
  a ≠ 0x810d0 ∧ a ≠ 0x810e8 ∧ a ≠ 0x810a8 ∧
  (∀ i : Nat, i < 2 → a ≠ Signing.wordAddress 0x810b0 i) ∧
  (∀ i : Nat, i < 3 → a ≠ Signing.wordAddress 0x81008 i)

theorem setup (s : MachineState)
    (pc : s.pc = 0x15e0) (height : s.getMem 0x81060 = 4) :
    ∃ finish : MachineState,
      OrdinarySteps image s 60 finish ∧
      finish.pc = 0x1720 ∧
      finish.getMem 0x810d0 = 16 ∧
      finish.getMem 0x810e8 = (s.getMem 0x81090 &&& 15#64) ∧
      finish.getMem 0x810a8 =
        (s.getMem 0x81090 &&& 18446744073709551600#64) ∧
      (∀ i : Nat, i < 2 →
        finish.getMem (Signing.wordAddress 0x810b0 i) =
          s.getMem (Signing.wordAddress 0x81098 i)) ∧
      (∀ i : Nat, i < 3 →
        finish.getMem (Signing.wordAddress 0x81008 i) =
          finish.getMem (Signing.wordAddress 0x810a8 i)) ∧
      (∀ a : Word, Outside a → finish.getMem a = s.getMem a) ∧
      finish.getReg .x2=s.getReg .x2 := by
  let chosen := GroupedBalancedSignUpperChoose67.chooseState s
  have chooseTrace := GroupedBalancedSignUpperChoose67.choose_steps s pc
  have chosenPc : chosen.pc = 0x168c := by
    have hh : s.getMem (528480#64) = (4#64) := height
    simpa [hh] using GroupedBalancedSignUpperChoose67.choose_pc s pc
  let entered := GroupedBalancedSignUpperEntryH467.entryState chosen
  have enterTrace := GroupedBalancedSignUpperEntryH467.entry_steps chosen chosenPc
  have enteredPc := GroupedBalancedSignUpperEntryH467.entry_pc chosen chosenPc
  obtain ⟨upper,upperTrace,upperPc,upperWords,upperFrame⟩ :=
    GroupedBalancedSignUpperCopiesH467.upper_copy entered enteredPc
  obtain ⟨base,baseTrace,basePc,baseWords,baseFrame⟩ :=
    GroupedBalancedSignUpperCopiesH467.base_copy upper upperPc
  let finish := GroupedBalancedSignUpperTailH467.tailState base
  have tailTrace := GroupedBalancedSignUpperTailH467.tail_steps base basePc
  have finishPc := GroupedBalancedSignUpperTailH467.tail_pc base basePc
  have trace : OrdinarySteps image s 60 finish := by
    simpa [finish,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Keygen.ordinary_trans image s base finish 56 4
        (Keygen.ordinary_trans image s upper base 33 23
          (Keygen.ordinary_trans image s entered upper 16 17
            (Keygen.ordinary_trans image s chosen entered 5 11 chooseTrace enterTrace)
            upperTrace) baseTrace) tailTrace
  have target : finish.getMem 0x810e8 = (s.getMem 0x81090 &&& 15#64) := by
    rw [GroupedBalancedSignUpperTailH467.tail_frame base 0x810e8 (by decide)]
    rw [baseFrame 0x810e8 (by intro i hi; interval_cases i <;> decide)]
    rw [upperFrame 0x810e8 (by intro i hi; interval_cases i <;> decide)]
    rw [GroupedBalancedSignUpperEntryH467.entry_selected chosen]
    rw [GroupedBalancedSignUpperChoose67.choose_frame s 0x81090]
  have rounded : finish.getMem 0x810a8 =
      (s.getMem 0x81090 &&& 18446744073709551600#64) := by
    rw [GroupedBalancedSignUpperTailH467.tail_frame base 0x810a8 (by decide)]
    rw [baseFrame 0x810a8 (by intro i hi; interval_cases i <;> decide)]
    rw [upperFrame 0x810a8 (by intro i hi; interval_cases i <;> decide)]
    rw [GroupedBalancedSignUpperEntryH467.entry_rounded chosen]
    rw [GroupedBalancedSignUpperChoose67.choose_frame s 0x81090]
  have upperRest : ∀ i : Nat, i < 2 →
      finish.getMem (Signing.wordAddress 0x810b0 i) =
        s.getMem (Signing.wordAddress 0x81098 i) := by
    intro i hi
    rw [GroupedBalancedSignUpperTailH467.tail_frame base _
      (by interval_cases i <;> decide)]
    rw [baseFrame _ (by intro j hj; interval_cases i <;> interval_cases j <;> decide)]
    rw [upperWords i hi]
    rw [GroupedBalancedSignUpperEntryH467.entry_frame chosen _
      (by interval_cases i <;> decide) (by interval_cases i <;> decide)]
    rw [GroupedBalancedSignUpperChoose67.choose_frame s _]
  have baseRest : ∀ i : Nat, i < 3 →
      finish.getMem (Signing.wordAddress 0x81008 i) =
        finish.getMem (Signing.wordAddress 0x810a8 i) := by
    intro i hi
    rw [GroupedBalancedSignUpperTailH467.tail_frame base _
      (by interval_cases i <;> decide)]
    rw [baseWords i hi]
    rw [GroupedBalancedSignUpperTailH467.tail_frame base _
      (by interval_cases i <;> decide)]
    rw [baseFrame _ (by intro j hj; interval_cases i <;> interval_cases j <;> decide)]
  have frame : ∀ a : Word, Outside a → finish.getMem a = s.getMem a := by
    intro a ha
    rw [GroupedBalancedSignUpperTailH467.tail_frame base a ha.1,
      baseFrame a ha.2.2.2.2,
      upperFrame a ha.2.2.2.1,
      GroupedBalancedSignUpperEntryH467.entry_frame chosen a ha.2.1 ha.2.2.1,
      GroupedBalancedSignUpperChoose67.choose_frame s a]
  have chooseSp : chosen.getReg .x2=s.getReg .x2 := by
    simp [chosen,GroupedBalancedSignUpperChoose67.chooseState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have entrySp : entered.getReg .x2=chosen.getReg .x2 := by
    simp [entered,GroupedBalancedSignUpperEntryH467.entryState,
      execInstrBr,MachineState.getReg_setReg_ne]
  have upperSp : upper.getReg .x2=entered.getReg .x2 :=
    GroupedBalancedSignUpperCopyStack67.upper_h4_sp entered upper
      enteredPc upperTrace
  have baseSp : base.getReg .x2=upper.getReg .x2 :=
    GroupedBalancedSignUpperCopyStack67.base_h4_sp upper base
      upperPc baseTrace
  have tailSp : finish.getReg .x2=base.getReg .x2 := by
    simp [finish,GroupedBalancedSignUpperTailH467.tailState,
      execInstrBr,MachineState.getReg_setReg_ne]
  exact ⟨finish,trace,finishPc,GroupedBalancedSignUpperTailH467.tail_count base,
    target,rounded,upperRest,baseRest,frame,
    tailSp.trans (baseSp.trans (upperSp.trans (entrySp.trans chooseSp)))⟩

#print axioms setup
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseH467

end

/-! Connect upper-group setup to the first decoded leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseToInitial67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperLeafFold67
open GroupedBalancedSignUpperLeafEntry67
open GroupedBalancedSignUpperLeafInitial67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image
def entryCost (message : BitVec 128) : Nat :=
  8 + (8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6) + 4

def OutsideCommon (a : Word) : Prop :=
  a ≠ 0x810d0 ∧ a ≠ 0x810e8 ∧ a ≠ 0x810a8 ∧
  (∀ i : Nat, i < 2 → a ≠ Signing.wordAddress 0x810b0 i) ∧
  (∀ i : Nat, i < 3 → a ≠ Signing.wordAddress 0x81008 i)

theorem outside_range (a : Word)
    (h : a.toNat<0x81000 ∨ 0x82000≤a.toNat) : OutsideCommon a := by
  unfold OutsideCommon
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro he
    have hn := congrArg BitVec.toNat he
    simp at hn
    omega
  · intro he
    have hn := congrArg BitVec.toNat he
    simp at hn
    omega
  · intro he
    have hn := congrArg BitVec.toNat he
    simp at hn
    omega
  · intro i hi
    interval_cases i <;> intro he
    all_goals
      have hn := congrArg BitVec.toNat he
      norm_num [Signing.wordAddress] at hn
      omega
  · intro i hi
    interval_cases i <;> intro he
    all_goals
      have hn := congrArg BitVec.toNat he
      norm_num [Signing.wordAddress] at hn
      omega

theorem outside_h3 (a : Word)
    (h : a.toNat<0x81000 ∨ 0x82000≤a.toNat) :
    GroupedBalancedSignUpperBaseH367.Outside a := by
  exact outside_range a h

theorem outside_h4 (a : Word)
    (h : a.toNat<0x81000 ∨ 0x82000≤a.toNat) :
    GroupedBalancedSignUpperBaseH467.Outside a := by
  exact outside_range a h

private theorem byte_frame (s t : MachineState) (addr : Word)
    (frame : ∀ a, OutsideCommon a → t.getMem a=s.getMem a)
    (range : (alignToDword addr).toNat<0x81000 ∨
      0x82000≤(alignToDword addr).toNat) :
    t.getByte addr=s.getByte addr := by
  simp only [MachineState.getByte,
    frame (alignToDword addr) (outside_range _ range)]

private theorem align_nat (addr : Word) :
    (alignToDword addr).toNat + byteOffset addr = addr.toNat := by
  unfold alignToDword byteOffset
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 7 from rfl]
  have hlo : addr.toNat &&& 7 = addr.toNat % 8 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod addr.toNat 3
  have hhi_mod : (addr.toNat &&& (2 ^ 64 - 1 - 7)) % 8 = 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_mod_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) % 2 ^ 3 = 0 from by decide]
    simp
  have hhi_div : (addr.toNat &&& (2 ^ 64 - 1 - 7)) / 8 = addr.toNat / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_div_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) / 2 ^ 3 = 2 ^ 61 - 1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by have := addr.isLt; omega)
  have hhi : addr.toNat &&& (2 ^ 64 - 1 - 7) = addr.toNat / 8 * 8 := by
    have heucl := Nat.div_add_mod (addr.toNat &&& (2 ^ 64 - 1 - 7)) 8
    omega
  rw [hlo, hhi]
  omega

private theorem message_align (j : Fin 16) :
    (alignToDword (BitVec.ofNat 64 (0x80500+j.val))).toNat <
      0x81000 := by
  have addrNat : (BitVec.ofNat 64 (0x80500+j.val)).toNat=0x80500+j.val := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  have relation := align_nat
    (BitVec.ofNat 64 (0x80500+j.val))
  omega

theorem table_align (i : Nat) (hi : i<2304) :
    0x82000 ≤ (alignToDword (BitVec.ofNat 64 (0xfff700+i))).toNat := by
  have addrNat : (BitVec.ofNat 64 (0xfff700+i)).toNat=0xfff700+i := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  have relation := align_nat
    (BitVec.ofNat 64 (0xfff700+i))
  have byteBound := byteOffset_lt_8 (addr := BitVec.ofNat 64 (0xfff700+i))
  omega

theorem table_align_base (i : Nat) (hi : i<2304) :
    0xfff700 ≤ (alignToDword (BitVec.ofNat 64 (0xfff700+i))).toNat := by
  let addr : Word := BitVec.ofNat 64 (0xfff700+i)
  have addrNat : addr.toNat=0xfff700+i := by
    simp only [addr,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  have relation := align_nat addr
  have byteBound := byteOffset_lt_8 (addr := addr)
  have aligned : (alignToDword addr).toNat % 8=0 := by
    unfold alignToDword
    rw [BitVec.toNat_and,show 8=2^3 from rfl,Nat.and_mod_two_pow]
    have hmask : (~~~7#64).toNat%2^3=0 := by decide
    rw [hmask]
    simp
  have baseAligned : 0xfff700%8=0 := by decide
  dsimp [addr] at *
  omega

theorem tables_of_high_frame (s t : MachineState)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (frame : ∀ a : Word, 0xfff700≤a.toNat → t.getMem a=s.getMem a) :
    GroupedBalancedVerifyByteContract67.Tables t := by
  intro i hi
  simp only [MachineState.getByte]
  rw [frame _ (table_align_base i hi)]
  exact tables i hi

theorem message_frame (s t : MachineState) (message : BitVec 128)
    (frame : ∀ a, OutsideCommon a → t.getMem a=s.getMem a)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8) :
    ∀ j : Fin 16,
      t.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8 := by
  intro j
  rw [byte_frame s t _ frame (Or.inl (message_align j))]
  exact hmsg j

theorem tables_frame (s t : MachineState)
    (frame : ∀ a, OutsideCommon a → t.getMem a=s.getMem a)
    (tables : GroupedBalancedVerifyByteContract67.Tables s) :
    GroupedBalancedVerifyByteContract67.Tables t := by
  intro i hi
  rw [byte_frame s t _ frame (Or.inr (table_align i hi))]
  exact tables i hi

private theorem outside_control (a : Word)
    (h : a=0x81000 ∨ a=0x81060 ∨ a=0x810f0) :
    OutsideCommon a := by
  rcases h with rfl | rfl | rfl
  all_goals
    unfold OutsideCommon
    refine ⟨by decide,by decide,by decide,?_,?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide

private theorem outside_boundary (a : Word)
    (h : a=0x81058 ∨ a=0x81090 ∨ a=0x81098 ∨ a=0x810a0) :
    OutsideCommon a := by
  rcases h with rfl | rfl | rfl | rfl
  all_goals
    unfold OutsideCommon
    refine ⟨by decide,by decide,by decide,?_,?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide

def BoundaryFrame (s t : MachineState) : Prop :=
  t.getMem 0x81058=s.getMem 0x81058 ∧
  t.getMem 0x81090=s.getMem 0x81090 ∧
  t.getMem 0x81098=s.getMem 0x81098 ∧
  t.getMem 0x810a0=s.getMem 0x810a0 ∧
  t.getMem 0x80500=s.getMem 0x80500 ∧
  t.getMem 0x80508=s.getMem 0x80508 ∧
  (∀ a : Word, a.toNat<0x100 → t.getMem a=s.getMem a)

theorem boundary_frame (s t : MachineState)
    (frame : ∀ a : Word, OutsideCommon a →
      (a.toNat<0x80600 ∨ 0x80800≤a.toNat) →
      a≠0x810e0 → a≠0x810f8 → t.getMem a=s.getMem a) :
    BoundaryFrame s t := by
  unfold BoundaryFrame
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact frame 0x81058 (outside_boundary _ (Or.inl rfl))
      (Or.inr (by decide)) (by decide) (by decide)
  · exact frame 0x81090 (outside_boundary _ (Or.inr (Or.inl rfl)))
      (Or.inr (by decide)) (by decide) (by decide)
  · exact frame 0x81098 (outside_boundary _ (Or.inr (Or.inr (Or.inl rfl))))
      (Or.inr (by decide)) (by decide) (by decide)
  · exact frame 0x810a0 (outside_boundary _ (Or.inr (Or.inr (Or.inr rfl))))
      (Or.inr (by decide)) (by decide) (by decide)
  · exact frame 0x80500 (outside_range _ (Or.inl (by decide)))
      (Or.inl (by decide)) (by decide) (by decide)
  · exact frame 0x80508 (outside_range _ (Or.inl (by decide)))
      (Or.inl (by decide)) (by decide) (by decide)
  · intro a ha
    exact frame a (outside_range _ (Or.inl (by omega)))
      (Or.inl (by omega))
      (by intro he; have hn := congrArg BitVec.toNat he; simp at hn; omega)
      (by intro he; have hn := congrArg BitVec.toNat he; simp at hn; omega)
theorem base_to_initial (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase setupCost : Nat)
    (s mid : MachineState) (message : BitVec 128)
    (setupSteps : OrdinarySteps image s setupCost mid)
    (pc : mid.pc=0x1720)
    (stack : s.getReg .x2=0xfff700)
    (stackFrame : mid.getReg .x2=s.getReg .x2)
    (frame : ∀ a, OutsideCommon a → mid.getMem a=s.getMem a)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (heightWord : s.getMem 0x81060=BitVec.ofNat 64 height)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (limit : mid.getMem 0x810d0=BitVec.ofNat 64 (2^height))
    (chosen : mid.getMem 0x810e8=BitVec.ofNat 64 selected)
    (low : mid.getMem 0x810a8=
      (BitVec.ofNat 192 leafBase).extractLsb' 0 64)
    (upper : ∀ i, i<2 →
      mid.getMem (Signing.wordAddress 0x810b0 i)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*(i+1)) 64)
    (base : ∀ i, i<3 →
      mid.getMem (Signing.wordAddress 0x81008 i)=
        mid.getMem (Signing.wordAddress 0x810a8 i)) :
    ∃ finish : MachineState,
      OrdinarySteps image s (setupCost+entryCost message) finish ∧
      Inv hash secretKey treeBase leafBase height selected witnessBase 0
        finish ∧
      (∀ a : Word, OutsideCommon a →
        (a.toNat<0x80600 ∨ 0x80800≤a.toNat) →
        a≠0x810e0 → a≠0x810f8 → finish.getMem a=s.getMem a) ∧
      finish.getReg .x2=s.getReg .x2 ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed,
        finish.getByte (BitVec.ofNat 64 (0x80600+j.val))=
          BitVec.ofNat 8 (GroupedBalancedUpperTree67.digit message j).val) ∧
      (∀ a : Word, a.toNat<0x80000 → finish.getMem a=s.getMem a) := by
  have midMsg := message_frame s mid message frame hmsg
  have midTables := tables_frame s mid frame tables
  have midStack : mid.getReg .x2=0xfff700 := stackFrame.trans stack
  have midTree : mid.getMem 0x81000=BitVec.ofNat 64 treeBase :=
    (frame _ (outside_control _ (Or.inl rfl))).trans tree
  have midHeight : mid.getMem 0x81060=BitVec.ofNat 64 height :=
    (frame _ (outside_control _ (Or.inr (Or.inl rfl)))).trans heightWord
  have midCurrent : ∃ b : Nat,
      mid.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0 := by
    obtain ⟨b,bword,bnext,blower,bupper,balign⟩ := current
    exact ⟨b,(frame _ (outside_control _
      (Or.inr (Or.inr rfl)))).trans bword,bnext,blower,bupper,balign⟩
  have midKey : ∀ j : Fin 4,
      mid.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64 := by
    intro j
    rw [frame _ (outside_range _ (Or.inl (by fin_cases j <;> decide)))]
    exact keyWords j
  have midScratch : ∀ w : Fin 3,
      mid.getMem (Signing.wordAddress 0x810a8 w.val)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64 := by
    intro w
    fin_cases w
    · simpa [Signing.wordAddress] using low
    · simpa [Signing.wordAddress] using upper 0 (by decide)
    · simpa [Signing.wordAddress] using upper 1 (by decide)
  have midAddress : ∀ w : Fin 3,
      mid.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*w.val) 64 := by
    intro w
    rw [base w.val w.isLt]
    exact midScratch w
  obtain ⟨entrySteps,inv⟩ := initial hash secretKey treeBase leafBase
    height selected witnessBase mid message pc midStack midMsg midTables
    limit chosen midTree midHeight midCurrent midAddress midScratch midKey
  have decodedDigits :=
    (GroupedBalancedSignUpperLeafEntry67.leaf_entry mid message pc
      midStack midMsg midTables).2.2.2.1
  refine ⟨leafEntryState mid message,?_,inv,?_,?_,?_,?_⟩
  · simpa only [entryCost,Nat.add_comm] using
      Keygen.ordinary_trans image s mid (leafEntryState mid message)
        setupCost (entryCost message) setupSteps entrySteps
  · intro a outside range notCount notWitness
    have notFlag : a≠0x80640 := by
      intro he
      have hn := congrArg BitVec.toNat he
      simp at hn
      omega
    have notCopy : ∀ k, k<16 →
        a≠alignToDword (BitVec.ofNat 64 (0x80600+4*k)) := by
      intro k hk he
      have hn := congrArg BitVec.toNat he
      have hbound : 0x80600 ≤
          (alignToDword (BitVec.ofNat 64 (0x80600+4*k))).toNat ∧
          (alignToDword (BitVec.ofNat 64 (0x80600+4*k))).toNat < 0x80800 := by
        interval_cases k <;> decide
      omega
    exact (GroupedBalancedSignUpperLeafEntryFrame67.entry_mem mid message
      a notCount notWitness notFlag notCopy).trans (frame a outside)
  · exact (GroupedBalancedSignUpperLeafEntryFrame67.entry_stack mid message).trans
      stackFrame
  · exact decodedDigits
  · intro a low
    have notCount : a≠0x810e0 := by
      intro he; have hn := congrArg BitVec.toNat he; simp at hn; omega
    have notWitness : a≠0x810f8 := by
      intro he; have hn := congrArg BitVec.toNat he; simp at hn; omega
    have notFlag : a≠0x80640 := by
      intro he; have hn := congrArg BitVec.toNat he; simp at hn; omega
    have notCopy : ∀ k, k<16 →
        a≠alignToDword (BitVec.ofNat 64 (0x80600+4*k)) := by
      intro k hk he
      have hn := congrArg BitVec.toNat he
      have hbound : 0x80600 ≤
          (alignToDword (BitVec.ofNat 64 (0x80600+4*k))).toNat := by
        interval_cases k <;> decide
      omega
    exact (GroupedBalancedSignUpperLeafEntryFrame67.entry_mem mid message
      a notCount notWitness notFlag notCopy).trans
      (frame a (outside_range a (Or.inl (by omega))))

theorem h3_initial (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase selected witnessBase : Nat)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc=0x15e0) (height : s.getMem 0x81060=3)
    (stack : s.getReg .x2=0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (selectedWord : s.getMem 0x81090 &&& 7#64 =
      BitVec.ofNat 64 selected)
    (roundedLow : s.getMem 0x81090 &&& 18446744073709551608#64 =
      (BitVec.ofNat 192 leafBase).extractLsb' 0 64)
    (sourceUpper : ∀ i, i<2 →
      s.getMem (Signing.wordAddress 0x81098 i)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*(i+1)) 64) :
    ∃ finish : MachineState,
      OrdinarySteps image s (61+entryCost message) finish ∧
      Inv hash secretKey treeBase leafBase 3 selected witnessBase 0 finish ∧
      (∀ a : Word, OutsideCommon a →
        (a.toNat<0x80600 ∨ 0x80800≤a.toNat) →
        a≠0x810e0 → a≠0x810f8 → finish.getMem a=s.getMem a) ∧
      finish.getReg .x2=s.getReg .x2 ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed,
        finish.getByte (BitVec.ofNat 64 (0x80600+j.val))=
          BitVec.ofNat 8 (GroupedBalancedUpperTree67.digit message j).val) ∧
      (∀ a : Word, a.toNat<0x80000 → finish.getMem a=s.getMem a) := by
  obtain ⟨mid,setupSteps,midPc,midLimit,midSelected,midLow,
    midUpper,midBase,midFrame,midSp⟩ :=
    GroupedBalancedSignUpperBaseH367.setup s pc height
  have commonFrame : ∀ a, OutsideCommon a →
      mid.getMem a=s.getMem a := by
    intro a ha
    exact midFrame a ha
  have midUpperData : ∀ i, i<2 →
      mid.getMem (Signing.wordAddress 0x810b0 i)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*(i+1)) 64 := by
    intro i hi
    rw [midUpper i hi]
    exact sourceUpper i hi
  exact base_to_initial hash secretKey treeBase leafBase 3 selected
    witnessBase 61 s mid message setupSteps midPc stack midSp
    commonFrame hmsg tables height tree current keyWords
    (by simpa using midLimit) (midSelected.trans selectedWord)
    (midLow.trans roundedLow) midUpperData midBase

theorem h4_initial (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase selected witnessBase : Nat)
    (s : MachineState) (message : BitVec 128)
    (pc : s.pc=0x15e0) (height : s.getMem 0x81060=4)
    (stack : s.getReg .x2=0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : GroupedBalancedVerifyByteContract67.Tables s)
    (tree : s.getMem 0x81000=BitVec.ofNat 64 treeBase)
    (current : ∃ b : Nat,
      s.getMem 0x810f0=BitVec.ofNat 64 b ∧ witnessBase=b+1072 ∧
      0x20060≤b ∧ b+16*67≤0x80000 ∧ b%8=0)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64)
    (selectedWord : s.getMem 0x81090 &&& 15#64 =
      BitVec.ofNat 64 selected)
    (roundedLow : s.getMem 0x81090 &&& 18446744073709551600#64 =
      (BitVec.ofNat 192 leafBase).extractLsb' 0 64)
    (sourceUpper : ∀ i, i<2 →
      s.getMem (Signing.wordAddress 0x81098 i)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*(i+1)) 64) :
    ∃ finish : MachineState,
      OrdinarySteps image s (60+entryCost message) finish ∧
      Inv hash secretKey treeBase leafBase 4 selected witnessBase 0 finish ∧
      (∀ a : Word, OutsideCommon a →
        (a.toNat<0x80600 ∨ 0x80800≤a.toNat) →
        a≠0x810e0 → a≠0x810f8 → finish.getMem a=s.getMem a) ∧
      finish.getReg .x2=s.getReg .x2 ∧
      (∀ j : GroupedBalancedUpperTree67.ChainMixed,
        finish.getByte (BitVec.ofNat 64 (0x80600+j.val))=
          BitVec.ofNat 8 (GroupedBalancedUpperTree67.digit message j).val) ∧
      (∀ a : Word, a.toNat<0x80000 → finish.getMem a=s.getMem a) := by
  obtain ⟨mid,setupSteps,midPc,midLimit,midSelected,midLow,
    midUpper,midBase,midFrame,midSp⟩ :=
    GroupedBalancedSignUpperBaseH467.setup s pc height
  have commonFrame : ∀ a, OutsideCommon a →
      mid.getMem a=s.getMem a := by
    intro a ha
    exact midFrame a ha
  have midUpperData : ∀ i, i<2 →
      mid.getMem (Signing.wordAddress 0x810b0 i)=
        (BitVec.ofNat 192 leafBase).extractLsb' (64*(i+1)) 64 := by
    intro i hi
    rw [midUpper i hi]
    exact sourceUpper i hi
  exact base_to_initial hash secretKey treeBase leafBase 4 selected
    witnessBase 60 s mid message setupSteps midPc stack midSp
    commonFrame hmsg tables height tree current keyWords
    (by simpa using midLimit) (midSelected.trans selectedWord)
    (midLow.trans roundedLow) midUpperData midBase

#print axioms outside_h3
#print axioms outside_h4
#print axioms message_frame
#print axioms tables_frame
#print axioms table_align_base
#print axioms tables_of_high_frame
#print axioms base_to_initial
#print axioms h3_initial
#print axioms h4_initial
#print axioms boundary_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseToInitial67
