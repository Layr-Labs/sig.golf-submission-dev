import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoopStart67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomIndexBounds67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedH167

/-! From official loaded signer state through all 1,024 bottom leaves. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedLeaves67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomAddress67
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

private abbrev image := GroupedBalancedSignImage67.image
private abbrev submission := GroupedBalancedProgram67Byte.submission

private theorem stable_control (a : Word)
    (h : a = 0x81060 ∨ a = 0x810d0 ∨ a = 0x810f8 ∨
      a = 0x810e8 ∨ a = 0x81090) :
    GroupedBalancedSignBottomLeafTickData67.StableAddress a := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold GroupedBalancedSignBottomLeafTickData67.StableAddress
    simp [Signing.wordAddress]
    constructor <;> intro i <;> fin_cases i <;> decide

private theorem stable_rounded (i : Fin 3) :
    GroupedBalancedSignBottomLeafTickData67.StableAddress
      (Signing.wordAddress 0x810a8 i.val) := by
  fin_cases i <;>
    unfold GroupedBalancedSignBottomLeafTickData67.StableAddress <;>
    simp [Signing.wordAddress] <;>
    constructor <;> intro j <;> fin_cases j <;> decide

theorem loaded_all_bottom_leaves (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial finish : MachineState, ∃ n c : Nat,
      initialState submission .sign (secretKey,cache,message) = some initial ∧
      Trace hash image initial n c 2050 2052 finish ∧
      finish.pc = 0x14ec ∧
      (∀ j : Nat, j < 1024 →
        finish.getMem (GroupedBalancedSignBottomStackSlots67.slot j 0) =
          (GroupedBottomTree.leafRoot hash secretKey
            (leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)) + j)).extractLsb' 0 64 ∧
        finish.getMem (GroupedBalancedSignBottomStackSlots67.slot j 1) =
          (GroupedBottomTree.leafRoot hash secretKey
            (leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)) + j)).extractLsb' 64 64) ∧
      finish.getMem 0x81060 = 10 ∧
      finish.getMem 0x810d0 = 1024 ∧
      finish.getMem 0x810f8 = 0x20090 ∧
      (∀ i : Fin 3,
        finish.getMem (Signing.wordAddress 0x810a8 i.val) =
          (BitVec.ofNat 192 (leafIndex (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)))).extractLsb'
              (64*i.val) 64) ∧
      finish.getMem 0x810e8 =
        (finish.getMem 0x81090 &&& 1023#64) ∧
      finish.getMem 0x81000 = 0 := by
  obtain ⟨initial,randomized,h5Ready,h5After,loaded,prefixRun,randomPc,
    h5ReadyPc,h5AfterPc,randomValue,h5Query,h5AfterEq,h5Words,keyWords,_,_⟩ :=
    GroupedBalancedSignIndexPrefix67.loaded_two_hash_prefix
      hash secretKey cache message
  let randomizer := Reference.randomizer hash secretKey message
  let answer := hash (SecurityRandomOracle.indexInput message randomizer)
  let index := answer.extractLsb' 0 160
  let leaf := leafIndex index
  have indexEq : index = Reference.indexOf hash message randomizer := by rfl
  obtain ⟨stored,extract,storedPc,storedLow,storedHigh,storedKey,_,_⟩ :=
    GroupedBalancedSignIndexExtract67.extract_answer h5After answer
      h5AfterPc h5Words
  have low : (stored.getMem 0x81090 &&& 18446744073709550592#64) =
      (BitVec.ofNat 192 leaf).extractLsb' 0 64 := by
    rw [show stored.getMem 0x81090 = answer.extractLsb' 0 64 from by
      simpa [Signing.wordAddress] using storedLow 0]
    rw [answerLow answer]
    exact (leafLow index).symm
  have middle : stored.getMem 0x81098 =
      (BitVec.ofNat 192 leaf).extractLsb' 64 64 := by
    rw [show stored.getMem 0x81098 = answer.extractLsb' 64 64 from by
      simpa [Signing.wordAddress] using storedLow 1]
    rw [answerMid answer]
    exact (leafMid index).symm
  have high : stored.getMem 0x810a0 =
      (BitVec.ofNat 192 leaf).extractLsb' 128 64 := by
    rw [storedHigh,answerHigh answer]
    exact (leafHigh index).symm
  have storedSecret : ∀ i : Fin 4,
      stored.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [storedKey i]
    exact keyWords i
  obtain ⟨start,setupTrace,initialInv,startHeight,startCount,startWitness,
    startRounded,startSelected,startIndexWords,_,_⟩ :=
    GroupedBalancedSignBottomLoopStart67.setup_initial hash stored
      secretKey leaf storedPc low middle high storedSecret
  have indexAlign : leaf % 1024 = 0 :=
    GroupedBalancedSignBottomIndexBounds67.leafIndex_align index
  have indexBound : leaf + 1024 ≤ 2^160 :=
    GroupedBalancedSignBottomIndexBounds67.leafIndex_bound index
  obtain ⟨n,c,finish,bottomTrace,finishPc,stackWords,stable⟩ :=
    GroupedBalancedSignBottomLeafInvariant67.run_all_stable hash secretKey
      leaf (start.getMem 0x810e8) start indexBound indexAlign initialInv
  refine ⟨initial,finish,196+25+72+n,226+25+72+c,loaded,?_,finishPc,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · have extractTrace := OrdinarySteps.trace (hash := hash) extract
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ((prefixRun.trans extractTrace).trans setupTrace).trans bottomTrace
  · intro j hj
    simpa only [leaf,indexEq,randomizer] using stackWords j hj
  · exact (stable 0x81060 (stable_control _ (Or.inl rfl))).trans startHeight
  · exact (stable 0x810d0 (stable_control _ (Or.inr (Or.inl rfl)))).trans startCount
  · exact (stable 0x810f8 (stable_control _ (Or.inr (Or.inr (Or.inl rfl))))).trans startWitness
  · intro i
    rw [stable _ (stable_rounded i)]
    simpa only [leaf,indexEq,randomizer] using startRounded i
  · rw [stable 0x810e8 (stable_control _
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      startSelected,stable 0x81090 (stable_control _
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]
    simpa [Signing.wordAddress] using
      congrArg (fun w : Word => w &&& 1023#64) (startIndexWords 0).symm
  · have safe : GroupedBalancedSignBottomLeafTickData67.StableAddress
        0x81000 := by
      unfold GroupedBalancedSignBottomLeafTickData67.StableAddress
      simp [Signing.wordAddress]
      constructor <;> intro i <;> fin_cases i <;> decide
    exact (stable 0x81000 safe).trans initialInv.2.2.2.1

#print axioms loaded_all_bottom_leaves
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedLeaves67
