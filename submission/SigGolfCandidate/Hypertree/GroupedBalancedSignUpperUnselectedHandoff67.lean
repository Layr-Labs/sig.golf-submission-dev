import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedFold67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperHandoff67

/-! An unselected upper leaf computes its Merkle value while retaining all
previously written signature words. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedHandoff67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperLeafH3Data67
open GroupedBalancedSignBottomStackSlots67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev zero := GroupedBalancedSignUpperChainZero67.zeroState

theorem unselected_handoff (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase i : Nat)
    (s : MachineState)
    (hh : height=3 ∨ height=4)
    (baseBound : treeBase<256)
    (hi : i<2^height)
    (inv : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey
      treeBase leafBase height selected witnessBase i s)
    (different : s.getMem 0x810e0≠s.getMem 0x810e8) :
    ∃ (n c : Nat) (ready : MachineState),
      Trace hash image s n c 247 247 ready ∧
      Ready hash secretKey treeBase leafBase height selected i ready ∧
      (∀ a : Word, a.toNat<0x80000 →
        ready.getMem a=s.getMem a) ∧
      ready.getMem 0x810f0=s.getMem 0x810f0 ∧
      ready.getReg .x2=s.getReg .x2 ∧
      (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
        ready.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80600≤a.toNat → a.toNat<0x80800 →
        ready.getMem a=s.getMem a) ∧
      n ≤ 36122 ∧ c ≤ 41281 := by
  have spc : s.pc=0x1750 := by simpa [hi] using inv.data.pc
  let start := zero s
  have zeroTrace := GroupedBalancedSignUpperChainZero67.zero_steps s spc
  have zeroPc := GroupedBalancedSignUpperChainZero67.zero_pc s spc
  have zeroCounter := GroupedBalancedSignUpperChainZero67.zero_chain s
  obtain ⟨b,bWord,bLower,bUpper,bAlign⟩ := inv.currentWitness
  have startKey : ∀ w : Fin 4,
      start.getMem (Signing.wordAddress 0x20 w.val)=
        secretKey.extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignUpperChainZero67.zero_frame s _
      (by fin_cases w <;> decide)]
    exact inv.keyWords w
  have startUnselected : start.getMem 0x810e0≠
      start.getMem 0x810e8 := by
    rw [GroupedBalancedSignUpperChainZero67.zero_frame s 0x810e0
      (by decide),GroupedBalancedSignUpperChainZero67.zero_frame s 0x810e8
      (by decide)]
    exact different
  have startInv := GroupedBalancedSignUpperUnselectedFold67.initial hash
    secretKey treeBase (leafBase+i) start zeroPc zeroCounter startKey
      startUnselected
  have startLevel : start.getMem 0x81000=BitVec.ofNat 64 treeBase := by
    rw [GroupedBalancedSignUpperChainZero67.zero_frame s 0x81000
      (by decide)]
    exact inv.data.tree
  have startAddress : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 (leafBase+i)).extractLsb'
          (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignUpperChainZero67.zero_frame s _
      (by fin_cases w <;> decide)]
    exact inv.data.address hi w
  have startWitness : start.getMem 0x810f0=BitVec.ofNat 64 b := by
    rw [GroupedBalancedSignUpperChainZero67.zero_frame s 0x810f0
      (by decide)]
    exact bWord
  obtain ⟨n,c,ready,path,readyPc,_readyDifferent,endpointWords,
    controlFrame,readySp,_keyWords,lowFrame,digitFrame,nBound,cBound⟩ :=
    GroupedBalancedSignUpperUnselectedFold67.run_all_copy hash secretKey
      treeBase (leafBase+i) b start baseBound startLevel startAddress
      startWitness bLower bUpper bAlign startInv
  have control (a : Word) (high : 0x81000≤a.toNat)
      (ne30 : a≠0x81030) (ne38 : a≠0x81038) :
      ready.getMem a=s.getMem a := by
    rw [controlFrame a high ne30 ne38,
      GroupedBalancedSignUpperChainZero67.zero_frame s a ne30]
  have readyData : Ready hash secretKey treeBase leafBase height
      selected i ready := by
    refine ⟨readyPc,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [control 0x810e0 (by decide) (by decide) (by decide)]
      exact inv.data.count
    · rw [control 0x810d0 (by decide) (by decide) (by decide)]
      exact inv.data.limit
    · rw [control 0x810e8 (by decide) (by decide) (by decide)]
      exact inv.data.chosen
    · rw [control 0x81000 (by decide) (by decide) (by decide)]
      exact inv.data.tree
    · intro w
      rw [control _ (by fin_cases w <;> decide)
        (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
      exact inv.data.address hi w
    · intro w
      rw [control _ (by fin_cases w <;> decide)
        (by fin_cases w <;> decide) (by fin_cases w <;> decide)]
      exact inv.data.scratch w
    · intro j hj w
      have small : j<1024 := by rcases hh with rfl | rfl <;> omega
      have range := GroupedBalancedSignBottomStackSlots67.slot_range
        j w.val small w.isLt
      rw [control (slot j w.val) (by omega)
        (by
          intro eq
          have hn := congrArg BitVec.toNat eq
          have numeric : (0x81030 : Word).toNat=0x81030 := by decide
          rw [numeric] at hn
          omega)
        (by
          intro eq
          have hn := congrArg BitVec.toNat eq
          have numeric : (0x81038 : Word).toNat=0x81038 := by decide
          rw [numeric] at hn
          omega)]
      exact inv.data.previous j hj w
    · exact endpointWords
  have full : Trace hash image s (4+n) (4+c) 247 247 ready := by
    simpa only [Nat.zero_add] using
      (zeroTrace.trace (hash := hash)).trans path
  have belowFrame : ∀ a : Word, a.toNat<0x80000 →
      ready.getMem a=s.getMem a := by
    intro a low
    rw [lowFrame a low]
    exact GroupedBalancedSignUpperChainZero67.zero_frame s a (by
      intro eq
      subst a
      have numeric : (0x81030 : Word).toNat=0x81030 := by decide
      rw [numeric] at low
      omega)
  refine ⟨4+n,4+c,ready,full,readyData,belowFrame,?_,?_,?_,?_,
    by omega,by omega⟩
  · exact control 0x810f0 (by decide) (by decide) (by decide)
  · rw [readySp,GroupedBalancedSignUpperHandoff67.zero_sp]
  · intro a persistent
    rcases persistent with low | safe | table
    · exact belowFrame a (by omega)
    · rcases safe with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact control _ (by decide) (by decide) (by decide)
    · exact control a (by omega) (by
        intro eq; subst a
        have numeric : (0x81030 : Word).toNat=0x81030 := by decide
        omega) (by
        intro eq; subst a
        have numeric : (0x81038 : Word).toNat=0x81038 := by decide
        omega)
  · intro a low high
    rw [digitFrame a low high]
    exact GroupedBalancedSignUpperChainZero67.zero_frame s a (by
      intro eq; subst a
      have numeric : (0x81030 : Word).toNat=0x81030 := by decide
      rw [numeric] at high
      omega)

theorem unselected_leaf (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase i : Nat)
    (s : MachineState)
    (hh : height=3 ∨ height=4)
    (baseBound : treeBase<256)
    (aligned : leafBase%2^height=0)
    (bound : leafBase+2^height≤2^160)
    (hi : i<2^height)
    (inv : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey
      treeBase leafBase height selected witnessBase i s)
    (different : s.getMem 0x810e0≠s.getMem 0x810e8) :
    ∃ (n c : Nat) (next : MachineState),
      Trace hash image s n c 248 265 next ∧
      GroupedBalancedSignUpperLeafFold67.Inv hash secretKey treeBase
        leafBase height selected witnessBase (i+1) next ∧
      (∀ a : Word, a.toNat<0x80000 →
        next.getMem a=s.getMem a) ∧
      (∀ a : Word, 0x80600≤a.toNat → a.toNat<0x80800 →
        next.getMem a=s.getMem a) ∧
      next.getMem 0x810f0=s.getMem 0x810f0 ∧
      (∀ a : Word, GroupedBalancedSignUpperLeafPersistent67.Persistent a →
        next.getMem a=s.getMem a) ∧
      next.getReg .x2=s.getReg .x2 ∧
      n ≤ 36188 ∧ c ≤ 41490 := by
  obtain ⟨n,c,ready,wotsTrace,readyData,belowFrame,
    readyCurrent,readySp,readyFrame,readyDigits,nBound,cBound⟩ :=
    unselected_handoff hash secretKey treeBase leafBase height
      selected witnessBase i s hh baseBound hi inv different
  obtain ⟨next,h3Trace,after,frame,nextSp,nextLow,nextDigits⟩ :=
    GroupedBalancedSignUpperLeafH3Data67.one_leaf hash secretKey treeBase
      leafBase height selected i ready hh aligned bound hi readyData
  have countSmall : (ready.getMem 0x810e0).toNat<1024 := by
    rw [readyData.count]
    simp only [BitVec.toNat_ofNat]
    have h16 : i<16 := by rcases hh with rfl | rfl <;> omega
    rw [Nat.mod_eq_of_lt (by omega : i<2^64)]
    omega
  have stable (a : Word) (high : 0x81000≤a.toNat)
      (low : a.toNat<0x83000) (ne08 : a≠0x81008)
      (neE0 : a≠0x810e0) : next.getMem a=ready.getMem a := by
    obtain ⟨ne0,ne8⟩ := GroupedBalancedSignBottomStackBound67.below_stack
      (ready.getMem 0x810e0) a countSmall low
    exact frame a high ne0 ne8 ne08 neE0
  have nextHeight : next.getMem 0x81060=BitVec.ofNat 64 height := by
    rw [stable 0x81060 (by decide) (by decide) (by decide) (by decide),
      readyFrame 0x81060 (Or.inr (Or.inl (Or.inr (Or.inl rfl))))]
    exact inv.heightWord
  have nextWitness : next.getMem 0x810f8=
      BitVec.ofNat 64 witnessBase := by
    rw [stable 0x810f8 (by decide) (by decide) (by decide) (by decide),
      readyFrame 0x810f8 (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))]
    exact inv.witness
  have nextCurrent : ∃ current : Nat,
      next.getMem 0x810f0=BitVec.ofNat 64 current ∧
      0x20060≤current ∧ current+16*67≤0x80000 ∧ current%8=0 := by
    obtain ⟨b,bWord,bLower,bUpper,bAlign⟩ := inv.currentWitness
    refine ⟨b,?_,bLower,bUpper,bAlign⟩
    rw [stable 0x810f0 (by decide) (by decide)
      (by decide) (by decide),readyCurrent,bWord]
  have nextStack : next.getReg .x2=0xfff7e0 ∨
      next.getReg .x2=0xfff700 := by
    rw [nextSp,readySp]
    exact inv.stack
  have nextKey : ∀ j : Fin 4,
      next.getMem (Signing.wordAddress 0x20 j.val)=
        secretKey.extractLsb' (64*j.val) 64 := by
    intro j
    have low : (Signing.wordAddress 0x20 j.val).toNat<0x80000 := by
      fin_cases j <;> decide
    rw [nextLow _ low,belowFrame _ low]
    exact inv.keyWords j
  have nextInv : GroupedBalancedSignUpperLeafFold67.Inv hash secretKey
      treeBase leafBase height selected witnessBase (i+1) next :=
    ⟨after,nextHeight,nextWitness,nextCurrent,nextStack,nextKey⟩
  have nextBelow : ∀ a : Word, a.toNat<0x80000 →
      next.getMem a=s.getMem a := by
    intro a low
    rw [nextLow a low,belowFrame a low]
  have nextDigitFrame : ∀ a : Word, 0x80600≤a.toNat →
      a.toNat<0x80800 → next.getMem a=s.getMem a := by
    intro a low high
    rw [nextDigits a low high,readyDigits a low high]
  have nextPersistent : ∀ a : Word,
      GroupedBalancedSignUpperLeafPersistent67.Persistent a →
      next.getMem a=s.getMem a := by
    intro a ha
    have leafFrame : next.getMem a=ready.getMem a := by
      rcases ha with low | safe | table
      · exact nextLow a (by omega)
      · obtain ⟨high,below,_,_,ne08,_,_,_,_,_,_,_,_,_,_⟩ :=
          GroupedBalancedSignUpperTreeControlFrame67.safe_facts a safe
        have neE0 : a≠0x810e0 := by
          rcases safe with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact stable a high below ne08 neE0
      · have slotRange := GroupedBalancedSignBottomStackBound67.stack0_range
          (ready.getMem 0x810e0) countSmall
        have slot8 := GroupedBalancedSignBottomStackBound67.stack8_nat
          (ready.getMem 0x810e0) countSmall
        have ne0 : a≠GroupedBalancedSignBottomStackBound67.stack0
            (ready.getMem 0x810e0) := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          omega
        have ne8 : a≠GroupedBalancedSignBottomStackBound67.stack0
            (ready.getMem 0x810e0)+8 := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          rw [slot8] at hn
          omega
        have ne08 : a≠0x81008 := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          simp at hn
          omega
        have neE0 : a≠0x810e0 := by
          intro eq
          have hn := congrArg BitVec.toNat eq
          simp at hn
          omega
        exact frame a (by omega) ne0 ne8 ne08 neE0
    exact leafFrame.trans (readyFrame a ha)
  refine ⟨n+66,c+209,next,?_,nextInv,nextBelow,nextDigitFrame,?_,
    nextPersistent,?_,by omega,by omega⟩
  · simpa [Nat.add_assoc] using wotsTrace.trans h3Trace
  · rw [stable 0x810f0 (by decide) (by decide) (by decide) (by decide),
      readyCurrent]
  · rw [nextSp,readySp]

#print axioms unselected_handoff
#print axioms unselected_leaf
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperUnselectedHandoff67
