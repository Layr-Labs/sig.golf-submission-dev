import SigGolfCandidate.Hypertree.GroupedBalancedSignByteInitialAgree67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomLoadedUpperSelected67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedBoundary67


/-! Loaded byte-signing program through the bottom tree and first upper boundary. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedUpperSelected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomAddress67
set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem loaded_bottom_to_upper_selected (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial upper : MachineState, ∃ n c : Nat,
      initialState GroupedBalancedProgram67ByteSign.submission .sign
        (secretKey,cache,message) = some initial ∧
      Trace hash GroupedBalancedSignImage67Byte.image initial n c
        3073 3075 upper ∧
      upper.pc = 0x15e0 ∧
      (∀ i : Fin 2,
        upper.getMem (BitVec.ofNat 64 (0x80500+8*i.val)) =
          (GroupedBottomTree.root hash secretKey 10
            ((leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)))/1024)).extractLsb'
                (64*i.val) 64) ∧
      upper.getMem 0x81058 = 0 ∧
      upper.getMem 0x81060 = 3 ∧
      upper.getMem 0x810f0 = 0x20130 ∧
      (∀ i : Fin 3,
        upper.getMem (Signing.wordAddress 0x81090 i.val) =
          ((BitVec.ofNat 192 (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)).toNat) >>> 10).extractLsb'
              (64*i.val) 64) ∧
      upper.getReg .x2=0xfff700 ∧
      upper.getMem 0x81000=10 ∧
      (∀ i : Fin 4, upper.getMem (Signing.wordAddress 0x20 i.val) =
        secretKey.extractLsb' (64*i.val) 64) ∧
      (∀ a : Word, 0xfff700 ≤ a.toNat →
        upper.getMem a = initial.getMem a) ∧
      n ≤ 257742 ∧ c ≤ 279269 ∧
      (∀ i : Fin 4,
        upper.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 2,
        upper.getMem (Signing.wordAddress 0x20080 i.val) =
          (GroupedBottomTree.secret hash secretKey
            (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).toNat).extractLsb'
                (64*i.val) 64) ∧
      (∀ level, level<10 → ∀ i : Fin 2,
        upper.getMem (GroupedBalancedSignBottomSelectedLevels67.pathSlot level i) =
          (GroupedBalancedSignBottomSelectedLevels67.siblingNode hash secretKey
            (leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)))
            ((Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).extractLsb'
                0 10).toNat level).extractLsb' (64*i.val) 64) := by
  rw [← GroupedBalancedSignByteInitialAgree67.submission_eq]
  exact GroupedBalancedSignBottomLoadedUpperSelected67.loaded_bottom_to_upper_selected
    hash secretKey cache message

#print axioms loaded_bottom_to_upper_selected
end SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedUpperSelected67


/-! A bounded loaded prefix from the byte signer to the first upper group. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBoundSelected67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperOuterInvariant67
open GroupedBalancedSignBottomAddress67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem loaded_boundary_bounded_selected (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial upper : MachineState, ∃ steps cycles : Nat,
      initialState GroupedBalancedProgram67ByteSign.submission .sign
        (secretKey,cache,message) = some initial ∧
      Trace hash GroupedBalancedSignImage67Byte.image initial steps cycles
        3073 3075 upper ∧
      Boundary hash secretKey
        (GroupedBalancedSignByteLoadedBoundary67.initialIndex
          hash secretKey message) 0
        (GroupedBalancedSignByteLoadedBoundary67.bottomRoot
          hash secretKey message) upper ∧
      (GroupedBalancedSignByteLoadedBoundary67.initialIndex
        hash secretKey message).toNat < 2^150 ∧
      steps ≤ 257742 ∧ cycles ≤ 279269 ∧
      (∀ i : Fin 4,
        upper.getMem (Signing.wordAddress 0x20060 i.val) =
          (Reference.randomizer hash secretKey message).extractLsb'
            (64*i.val) 64) ∧
      (∀ i : Fin 2,
        upper.getMem (Signing.wordAddress 0x20080 i.val) =
          (GroupedBottomTree.secret hash secretKey
            (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).toNat).extractLsb'
                (64*i.val) 64) ∧
      (∀ level, level<10 → ∀ i : Fin 2,
        upper.getMem (GroupedBalancedSignBottomSelectedLevels67.pathSlot level i) =
          (GroupedBalancedSignBottomSelectedLevels67.siblingNode hash secretKey
            (leafIndex (Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)))
            ((Reference.indexOf hash message
              (Reference.randomizer hash secretKey message)).extractLsb'
                0 10).toNat level).extractLsb' (64*i.val) 64) := by
  obtain ⟨initial,upper,steps,cycles,loaded,run,pc,rootWords,layer,height,
    witness,selected,stack,treeWord,keyWords,highFrame,stepsBound,cyclesBound,
    randomWords,seedWords,pathWords⟩ :=
    GroupedBalancedSignByteLoadedUpperSelected67.loaded_bottom_to_upper_selected
      hash secretKey cache message
  have initialTables := GroupedBalancedSignByteLoader67.initial_tables
    (secretKey,cache,message) initial loaded
  have upperTables :=
    GroupedBalancedSignUpperBaseToInitial67.tables_of_high_frame
      initial upper initialTables highFrame
  have boundary : Boundary hash secretKey
      (GroupedBalancedSignByteLoadedBoundary67.initialIndex
        hash secretKey message) 0
      (GroupedBalancedSignByteLoadedBoundary67.bottomRoot
        hash secretKey message) upper := by
    refine ⟨pc,?_,?_,?_,?_,?_,?_,stack,keyWords,upperTables⟩
    · simpa using layer
    · simpa [GroupedBalancedSignUpperSchedule67.height] using height
    · simpa [GroupedBalancedSignUpperSchedule67.treeBase,
        GroupedBalancedSignUpperSchedule67.prefixHeight] using treeWord
    · simpa [GroupedBalancedSignUpperSchedule67.currentWitness,
        GroupedBalancedSignUpperSchedule67.prefixHeight] using witness
    · intro w
      simpa [GroupedBalancedSignByteLoadedBoundary67.initialIndex,
        GroupedBalancedSignUpperOuterInvariant67.indexAt,
        GroupedBalancedSignUpperSchedule67.prefixHeight] using selected w
    · exact current_of_root upper
        (GroupedBalancedSignByteLoadedBoundary67.bottomRoot
          hash secretKey message)
        (by intro w; simpa [GroupedBalancedSignByteLoadedBoundary67.bottomRoot]
          using rootWords w)
  exact ⟨initial,upper,steps,cycles,loaded,run,boundary,
    GroupedBalancedSignByteLoadedBoundary67.initial_index_bound
    hash secretKey message,stepsBound,cyclesBound,randomWords,seedWords,pathWords⟩

#print axioms loaded_boundary_bounded_selected
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBoundSelected67
