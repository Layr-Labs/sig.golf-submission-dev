import SigGolfCandidate.Hypertree.GroupedBalancedSignIndexExtract67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddress67

/-! The loaded signer reaches the first bottom secret with the H5-derived address. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedH167
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image
private abbrev submission := GroupedBalancedProgram67Byte.submission
open SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddress67

theorem loaded_first_bottom_secret (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial ready after : MachineState,
      initialState submission .sign (secretKey,cache,message) = some initial ∧
      Trace hash image initial 355 392 3 5 after ∧
      ready.pc = 0x1378 ∧ after.pc = 0x137c ∧
      hashInput ready = Reference.packed (KeygenDomain.secretPayload
        (KeygenDomain.header 1 0 0 0 0)
          (leafIndex (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message))) secretKey) ∧
      (∀ i : Fin 2, after.getMem (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.secret hash secretKey
          (leafIndex (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)))).extractLsb'
              (64*i.val) 64) ∧
      after.getMem 0x81000 = 0 ∧
      (∀ i : Fin 3, after.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 (leafIndex (Reference.indexOf hash message
          (Reference.randomizer hash secretKey message)))).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 4,
        after.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) := by
  obtain ⟨initial,randomized,h5Ready,h5After,loaded,prefixRun,randomPc,
    h5ReadyPc,h5AfterPc,randomValue,h5Query,h5AfterEq,h5Words,keyWords,_,
    h5RandomWords⟩ :=
    GroupedBalancedSignIndexPrefix67.loaded_two_hash_prefix
      hash secretKey cache message
  let randomizer := Reference.randomizer hash secretKey message
  let answer := hash (SecurityRandomOracle.indexInput message randomizer)
  let index := answer.extractLsb' 0 160
  let leaf := leafIndex index
  have indexEq : index = Reference.indexOf hash message randomizer := by
    rfl
  obtain ⟨stored,extract,storedPc,storedLow,storedHigh,storedKey,_,
    extractRandomFrame⟩ :=
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
  obtain ⟨staged,ready,after,h1,stagedPc,readyPc,afterPc,query,
    afterEq,seedWords,levelOut,addressOut,firstRandomFrame⟩ :=
    GroupedBalancedSignBottomFirstLeaf67.first_leaf hash stored
      secretKey leaf storedPc low middle high storedSecret
  refine ⟨initial,ready,after,loaded,?_,readyPc,afterPc,?_,?_,levelOut,?_,?_⟩
  · have extractTrace := OrdinarySteps.trace (hash := hash) extract
    simpa [image,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (prefixRun.trans extractTrace).trans h1
  · simpa only [leaf,indexEq,randomizer] using query
  · intro i
    simpa only [leaf,indexEq,randomizer] using seedWords i
  · intro i
    simpa only [leaf,indexEq,randomizer] using addressOut i
  · intro i
    rw [firstRandomFrame _ (by fin_cases i <;> decide)
      (by fin_cases i <;> decide),
      extractRandomFrame _ (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)]
    exact h5RandomWords i

#print axioms loaded_first_bottom_secret
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedH167
