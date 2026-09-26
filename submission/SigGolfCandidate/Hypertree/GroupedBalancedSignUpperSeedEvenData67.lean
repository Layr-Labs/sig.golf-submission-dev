import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedReady67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH1ResultData67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedOddData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedEvenData67. -/
section
/-! The odd chain reuses the high half of the preceding paired H1 answer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedOddData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def jumpState (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x0 0x110)

private theorem jump_code :
    Keygen.instructionAt image 0x1774 = some (.base (.JAL .x0 0x110)) := by
  decide

theorem jump_steps (s : MachineState) (pc : s.pc=0x1774) :
    OrdinarySteps image s 1 (jumpState s) := by
  apply OrdinarySteps.step s (jumpState s) _ (.base (.JAL .x0 0x110)) 0
  · simpa only [Keygen.fetch_at,pc] using jump_code
  · rfl
  exact OrdinarySteps.refl _

theorem jump_pc (s : MachineState) (pc : s.pc=0x1774) :
    (jumpState s).pc=0x1884 := by
  simp [jumpState,execInstrBr,signExtend21,pc]

theorem jump_frame (s : MachineState) (a : Word) :
    (jumpState s).getMem a=s.getMem a := by
  simp [jumpState,execInstrBr]

theorem jump_x19 (s : MachineState) :
    (jumpState s).getReg .x19=s.getReg .x19 := by
  simp [jumpState,execInstrBr,MachineState.getReg_setReg_ne]

theorem jump_x2 (s : MachineState) :
    (jumpState s).getReg .x2=s.getReg .x2 := by
  simp [jumpState,execInstrBr,MachineState.getReg_setReg_ne]

theorem dispatch_x2 (s : MachineState) :
    (GroupedBalancedSignUpperChainDispatch67.dispatchState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignUpperChainDispatch67.dispatchState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem odd_secret_words (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (chain : Fin 67) (parity : chain.val%2=1)
    (i : Fin 2) :
    (GroupedBalancedUpperTree67.secretPair hash secretKey base leaf
      (chain.val/2)).extractLsb' (128+64*i.val) 64 =
    (GroupedBalancedUpperTree67.secret hash secretKey base leaf
      chain).extractLsb' (64*i.val) 64 := by
  simp only [GroupedBalancedUpperTree67.secret,parity,
    show (1:Nat)=0 ↔ False from by decide,if_false]
  fin_cases i
  · ext j hj
    simp (disch := omega)
  · ext j hj
    simp (disch := omega)
    congr 1
    omega

theorem odd_seed (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (chain : Fin 67) (s : MachineState)
    (pc : s.pc=0x1760)
    (chainWord : s.getMem 0x81030=BitVec.ofNat 64 chain.val)
    (parity : chain.val%2=1)
    (oddBit : s.getMem 0x81030 &&& (1 : Word) ≠ 0)
    (cached : ∀ i : Fin 2,
      s.getMem (Signing.wordAddress 0x80d10 i.val)=
        (GroupedBalancedUpperTree67.secretPair hash secretKey base leaf
          (chain.val/2)).extractLsb' (128+64*i.val) 64) :
    ∃ final : MachineState,
      Trace hash image s 26 26 0 0 final ∧
      final.pc=0x18e8 ∧
      final.getReg .x19=BitVec.ofNat 64 chain.val ∧
      final.getReg .x2=s.getReg .x2 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val)=
          (GroupedBalancedUpperTree67.secret hash secretKey base leaf
            chain).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80d10 i.val)=
          s.getMem (Signing.wordAddress 0x80d10 i.val)) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → final.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
        final.getMem a=s.getMem a) ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a.toNat < 0x80800 →
        final.getMem a=s.getMem a) := by
  let dispatched := GroupedBalancedSignUpperChainDispatch67.dispatchState s
  have first := GroupedBalancedSignUpperChainDispatch67.dispatch_steps s pc
  have firstPc : dispatched.pc=0x1774 := by
    rw [GroupedBalancedSignUpperChainDispatch67.dispatch_pc s pc]
    simpa using oddBit
  let jumped := jumpState dispatched
  have second := jump_steps dispatched firstPc
  have secondPc := jump_pc dispatched firstPc
  have secondX19 : jumped.getReg .x19=s.getMem 0x81030 := by
    rw [jump_x19,GroupedBalancedSignUpperChainDispatch67.dispatch_chain]
  have jumpedOdd : jumped.getReg .x19 &&& (1:Word) ≠ 0 := by
    rw [secondX19]
    exact oddBit
  obtain ⟨final,third,finalPc,finalX19,finalSp,seed,frame⟩ :=
    GroupedBalancedSignUpperSeedReady67.odd_ready jumped secondPc jumpedOdd
  have full : OrdinarySteps image s 26 final := by
    simpa only [Nat.reduceAdd] using
      (Keygen.ordinary_trans image s jumped final 6 20
        (by simpa only [Nat.reduceAdd] using
          Keygen.ordinary_trans image s dispatched jumped 5 1 first second)
        third)
  refine ⟨final,full.trace (hash := hash),finalPc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [finalX19,secondX19,chainWord]
  · rw [finalSp,jump_x2,dispatch_x2]
  · intro i
    have h := seed i.val i.isLt
    rw [h,jump_frame,GroupedBalancedSignUpperChainDispatch67.dispatch_frame]
    rw [cached i]
    exact odd_secret_words hash secretKey base leaf chain parity i
  · intro i
    rw [frame _ (by
      intro j hj eq
      have hn := congrArg BitVec.toNat eq
      fin_cases i <;> interval_cases j <;>
        simp [Signing.wordAddress] at hn <;> omega),
      jump_frame,GroupedBalancedSignUpperChainDispatch67.dispatch_frame]
  · intro a high
    have outside : ∀ i, i<2 → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      interval_cases i <;> simp [Signing.wordAddress] at hn <;> omega
    rw [frame a outside,jump_frame,
      GroupedBalancedSignUpperChainDispatch67.dispatch_frame]
  · intro a middle beforeCache
    have outside : ∀ i, i<2 → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    rw [frame a outside,jump_frame,
      GroupedBalancedSignUpperChainDispatch67.dispatch_frame]
  · intro a low
    have outside : ∀ i, i<2 → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    rw [frame a outside,jump_frame,
      GroupedBalancedSignUpperChainDispatch67.dispatch_frame]
  · intro a low high
    have outside : ∀ i, i<2 → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    rw [frame a outside,jump_frame,
      GroupedBalancedSignUpperChainDispatch67.dispatch_frame]

#print axioms odd_seed
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedOddData67

end

/-! The even chain derives its 16-byte seed with one paired H1 call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedEvenData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

theorem pair_x19 (s : MachineState) :
    (GroupedBalancedSignUpperPairIndex67.pairState s).getReg .x19 =
      s.getReg .x19 := by
  simp [GroupedBalancedSignUpperPairIndex67.pairState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem pair_x2 (s : MachineState) :
    (GroupedBalancedSignUpperPairIndex67.pairState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignUpperPairIndex67.pairState,execInstrBr,
    MachineState.getReg_setReg_ne]

theorem even_secret_words (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (chain : Fin 67) (parity : chain.val%2=0)
    (i : Fin 2) :
    (GroupedBalancedUpperTree67.secretPair hash secretKey base leaf
      (chain.val/2)).extractLsb' (64*i.val) 64 =
    (GroupedBalancedUpperTree67.secret hash secretKey base leaf
      chain).extractLsb' (64*i.val) 64 := by
  simp only [GroupedBalancedUpperTree67.secret,parity,if_true]
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem even_seed (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (chain : Fin 67) (s : MachineState)
    (pc : s.pc=0x1760)
    (chainWord : s.getMem 0x81030=BitVec.ofNat 64 chain.val)
    (parity : chain.val%2=0)
    (evenBit : s.getMem 0x81030 &&& (1 : Word) = 0)
    (level : s.getMem 0x81000=BitVec.ofNat 64 base)
    (address : ∀ j : Fin 3,
      s.getMem (Signing.wordAddress 0x81008 j.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64)
    (keyWords : ∀ j : Fin 4,
      s.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64) :
    ∃ final : MachineState,
      Trace hash image s 127 134 1 1 final ∧
      final.pc=0x18e8 ∧
      final.getReg .x19=BitVec.ofNat 64 chain.val ∧
      final.getReg .x2=s.getReg .x2 ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80020 i.val)=
          (GroupedBalancedUpperTree67.secret hash secretKey base leaf
            chain).extractLsb' (64*i.val) 64) ∧
      (∀ i : Fin 2,
        final.getMem (Signing.wordAddress 0x80d10 i.val)=
          (GroupedBalancedUpperTree67.secretPair hash secretKey base leaf
            (chain.val/2)).extractLsb' (128+64*i.val) 64) ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → final.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80800 ≤ a.toNat → a.toNat < 0x80d00 →
        final.getMem a=s.getMem a) ∧
      (∀ a : Word, a.toNat < 0x80000 → final.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80600 ≤ a.toNat → a.toNat < 0x80800 →
        final.getMem a=s.getMem a) := by
  let d := GroupedBalancedSignUpperChainDispatch67.dispatchState s
  have first := GroupedBalancedSignUpperChainDispatch67.dispatch_steps s pc
  have dpc : d.pc=0x1778 := by
    rw [GroupedBalancedSignUpperChainDispatch67.dispatch_pc s pc]
    simpa using evenBit
  let p := GroupedBalancedSignUpperPairIndex67.pairState d
  have second := GroupedBalancedSignUpperPairIndex67.pair_steps d dpc
  have ppc := GroupedBalancedSignUpperPairIndex67.pair_pc d dpc
  have pPair : p.getMem 0x81030=BitVec.ofNat 64 (chain.val/2) := by
    rw [GroupedBalancedSignUpperPairIndex67.pair_index,
      GroupedBalancedSignUpperChainDispatch67.dispatch_chain,chainWord]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have pHigh (a : Word) (ne30 : a≠0x81030) : p.getMem a=s.getMem a := by
    rw [GroupedBalancedSignUpperPairIndex67.pair_frame d a ne30,
      GroupedBalancedSignUpperChainDispatch67.dispatch_frame]
  obtain ⟨copied,third,cpc,copyWords,copyFrame,copyX19,copySp⟩ :=
    GroupedBalancedSignUpperSecretCopy67.secret_copy p ppc
  have cPair : copied.getMem 0x81030=BitVec.ofNat 64 (chain.val/2) := by
    rw [copyFrame 0x81030]
    · exact pPair
    · intro i hi eq
      have hn := congrArg BitVec.toNat eq
      interval_cases i <;> simp [Signing.wordAddress] at hn <;> omega
  have cLevel : copied.getMem 0x81000=BitVec.ofNat 64 base := by
    rw [copyFrame 0x81000 (by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      interval_cases i <;> simp [Signing.wordAddress] at hn <;> omega),
      pHigh 0x81000 (by decide),level]
  have cAddress : ∀ j : Fin 3,
      copied.getMem (Signing.wordAddress 0x81008 j.val)=
        (BitVec.ofNat 192 leaf).extractLsb' (64*j.val) 64 := by
    intro j
    rw [copyFrame _ (by
      intro i hi eq
      fin_cases j <;> interval_cases i <;>
        simp [Signing.wordAddress] at eq <;> omega),
      pHigh _ (by fin_cases j <;> decide),address j]
  have cKey : ∀ j : Fin 4,
      copied.getMem (Signing.wordAddress 0x80020 j.val)=
        secretKey.extractLsb' (64*j.val) 64 := by
    intro j
    rw [copyWords j.val j.isLt,
      pHigh _ (by fin_cases j <;> decide)]
    exact keyWords j
  obtain ⟨answered,fourth,apc,answerX19,answerSp,restored,
      pairWords,answerFrame,answerMiddle,answerLow,answerDigit⟩ :=
    GroupedBalancedSignUpperH1ResultData67.run hash secretKey base leaf
      (chain.val/2) copied cpc cLevel cPair cAddress cKey
  have answerEven : answered.getReg .x19 &&& (1 : Word) = 0 := by
    rw [answerX19,copyX19,pair_x19,
      GroupedBalancedSignUpperChainDispatch67.dispatch_chain]
    exact evenBit
  obtain ⟨final,fifth,fpc,finalX19,finalSp,seedWords,seedFrame⟩ :=
    GroupedBalancedSignUpperSeedReady67.even_ready answered apc answerEven
  have all : Trace hash image s 127 134 1 1 final := by
    have firstTwo := Keygen.ordinary_trans image s d p 5 4 first second
    have firstThree := Keygen.ordinary_trans image s p copied 9 28
      (by simpa only [Nat.reduceAdd] using firstTwo) third
    have head : Trace hash image s 37 37 0 0 copied := by
      simpa only [Nat.reduceAdd] using
        (OrdinarySteps.trace (hash := hash) firstThree)
    have tail : Trace hash image answered 19 19 0 0 final :=
      OrdinarySteps.trace (hash := hash) fifth
    simpa only [Nat.reduceAdd] using (head.trans fourth).trans tail
  refine ⟨final,all,fpc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [finalX19,answerX19,copyX19,pair_x19,
      GroupedBalancedSignUpperChainDispatch67.dispatch_chain,chainWord]
  · rw [finalSp,answerSp,copySp,pair_x2,
      GroupedBalancedSignUpperSeedOddData67.dispatch_x2]
  · intro i
    rw [seedWords i.val i.isLt,pairWords ⟨i.val,by omega⟩]
    exact even_secret_words hash secretKey base leaf chain parity i
  · intro i
    rw [seedFrame (Signing.wordAddress 0x80d10 i.val) (by
      intro j hj eq
      have hn := congrArg BitVec.toNat eq
      fin_cases i <;> interval_cases j <;>
        simp [Signing.wordAddress] at hn <;> omega)]
    fin_cases i
    · simpa [Signing.wordAddress] using pairWords (2 : Fin 4)
    · simpa [Signing.wordAddress] using pairWords (3 : Fin 4)
  · intro a high
    have outside : ∀ i, i<2 → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      interval_cases i <;> simp [Signing.wordAddress] at hn <;> omega
    rw [seedFrame a outside]
    by_cases ne30 : a=0x81030
    · subst a
      rw [restored,copyX19,pair_x19,
        GroupedBalancedSignUpperChainDispatch67.dispatch_chain]
    · rw [answerFrame a high ne30,
        copyFrame a (by
          intro i hi eq
          have hn := congrArg BitVec.toNat eq
          interval_cases i <;> simp [Signing.wordAddress] at hn <;> omega),
        pHigh a ne30]
  · intro a middle beforeCache
    have outside (count : Nat) (small : count≤4) :
        ∀ i, i<count → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    have ne30 : a≠0x81030 := by
      intro eq
      subst a
      simp [BitVec.toNat_ofNat] at beforeCache
    rw [seedFrame a (outside 2 (by decide)),
      answerMiddle a middle beforeCache,
      copyFrame a (outside 4 (by decide)),pHigh a ne30]
  · intro a low
    have outside (count : Nat) (small : count≤4) :
        ∀ i, i<count → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    have ne30 : a≠0x81030 := by
      intro eq
      subst a
      simp [BitVec.toNat_ofNat] at low
    rw [seedFrame a (outside 2 (by decide)),answerLow a low,
      copyFrame a (outside 4 (by decide)),pHigh a ne30]
  · intro a low high
    have outside (count : Nat) (small : count≤4) :
        ∀ i, i<count → a≠Signing.wordAddress 0x80020 i := by
      intro i hi eq
      have hn := congrArg BitVec.toNat eq
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80020+8*i<2^64)] at hn
      omega
    have ne30 : a≠0x81030 := by
      intro eq
      subst a
      simp [BitVec.toNat_ofNat] at high
    rw [seedFrame a (outside 2 (by decide)),answerDigit a low high,
      copyFrame a (outside 4 (by decide)),pHigh a ne30]

#print axioms even_seed
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSeedEvenData67
