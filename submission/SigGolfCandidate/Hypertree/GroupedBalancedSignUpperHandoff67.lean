import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChainFold67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafFold67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperLeafPersistent67

/-! The complete upper WOTS program supplies the leaf-fold handoff. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperHandoff67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperLeafH3Data67
open GroupedBalancedSignBottomStackSlots67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev zero := GroupedBalancedSignUpperChainZero67.zeroState

theorem zero_sp (s : MachineState) :
    (zero s).getReg .x2=s.getReg .x2 := by
  simp [zero,GroupedBalancedSignUpperChainZero67.zeroState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem handoff (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase height selected witnessBase : Nat)
    (hh : height=3 ∨ height=4)
    (baseBound : treeBase<256) :
    GroupedBalancedSignUpperLeafPersistent67.Handoff hash secretKey
      treeBase leafBase height selected witnessBase := by
  intro i s hi inv
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
  have startInv := GroupedBalancedSignUpperChainFold67.initial hash
    secretKey treeBase (leafBase+i) start zeroPc zeroCounter startKey
  have startLevel : start.getMem 0x81000=BitVec.ofNat 64 treeBase := by
    rw [GroupedBalancedSignUpperChainZero67.zero_frame s 0x81000
      (by decide)]
    exact inv.data.tree
  have startAddress : ∀ w : Fin 3,
      start.getMem (Signing.wordAddress 0x81008 w.val)=
        (BitVec.ofNat 192 (leafBase+i)).extractLsb' (64*w.val) 64 := by
    intro w
    rw [GroupedBalancedSignUpperChainZero67.zero_frame s _
      (by fin_cases w <;> decide)]
    exact inv.data.address hi w
  have startWitness : start.getMem 0x810f0=BitVec.ofNat 64 b := by
    rw [GroupedBalancedSignUpperChainZero67.zero_frame s 0x810f0
      (by decide)]
    exact bWord
  obtain ⟨n,c,ready,path,readyPc,readySp,endpointWords,
    controlFrame,keyWords,lowFrame,nBound,cBound⟩ :=
    GroupedBalancedSignUpperChainFold67.run_all_copy hash secretKey
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
  refine ⟨4+n,4+c,ready,full,readyData,?_,?_,?_,?_,?_,?_,
    by omega,by omega⟩
  · exact control 0x81060 (by decide) (by decide) (by decide)
  · exact control 0x810f8 (by decide) (by decide) (by decide)
  · exact control 0x810f0 (by decide) (by decide) (by decide)
  · rw [readySp,zero_sp]
  · intro w
    rw [keyWords w]
    exact (inv.keyWords w).symm
  · intro a persistent
    rcases persistent with low | safe | table
    · rw [lowFrame a low,
        GroupedBalancedSignUpperChainZero67.zero_frame s a (by
          intro eq
          subst a
          have numeric : (0x81030 : Word).toNat=0x81030 := by decide
          rw [numeric] at low
          omega)]
    · rcases safe with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact control _ (by decide) (by decide) (by decide)
    · have neq (b : Word) (hb : b.toNat<0x90000) : a≠b := by
        intro eq
        subst a
        omega
      exact control a (by omega) (neq 0x81030 (by decide))
        (neq 0x81038 (by decide))

#print axioms handoff
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperHandoff67
