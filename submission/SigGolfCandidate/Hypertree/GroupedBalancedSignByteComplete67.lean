import SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedBoundary67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterComplete67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBound67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignByteComplete67. -/
section
/-! A bounded loaded prefix from the byte signer to the first upper group. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBound67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem loaded_boundary_bounded (hash : Hash) (secretKey : SecretKey)
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
                (64*i.val) 64) := by
  obtain ⟨initial,upper,steps,cycles,loaded,run,pc,rootWords,layer,height,
    witness,selected,stack,treeWord,keyWords,highFrame,stepsBound,cyclesBound,
    randomWords,seedWords⟩ :=
    GroupedBalancedSignByteLoadedUpper67.loaded_bottom_to_upper
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
    hash secretKey message,stepsBound,cyclesBound,randomWords,seedWords⟩

#print axioms loaded_boundary_bounded
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomBound67

end

/-! Complete direct67 signing execution from the official byte loader. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteComplete67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev byteSubmission := GroupedBalancedProgram67ByteSign.submission

theorem loaded_success (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial final : MachineState, ∃ steps cycles : Nat,
      initialState byteSubmission .sign (secretKey, cache, message) =
        some initial ∧
      Executes hash image initial steps
        ⟨.success, final, cycles, 122548, 130710⟩ ∧
      steps ≤ 27392745 ∧ cycles ≤ 31914272 := by
  obtain ⟨initial, upper, prefixSteps, prefixCycles, loaded, prefixTrace,
      boundary, indexBound, prefixStepBound, prefixCycleBound,_,_⟩ :=
    GroupedBalancedSignBottomBound67.loaded_boundary_bounded
      hash secretKey cache message
  obtain ⟨upperSteps, upperCycles, final, suffix, upperStepBound,
      upperCycleBound⟩ :=
    GroupedBalancedSignUpperOuterComplete67.all_groups hash secretKey
      (GroupedBalancedSignByteLoadedBoundary67.initialIndex
        hash secretKey message) indexBound
      (GroupedBalancedSignByteLoadedBoundary67.bottomRoot
        hash secretKey message) upper boundary
  refine ⟨initial, final, prefixSteps + upperSteps,
    prefixCycles + upperCycles, loaded, ?_, by omega, by omega⟩
  simpa only [Execution.charge, Nat.reduceAdd] using prefixTrace.then_executes suffix

theorem run_bound (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    let result := byteSubmission.runWith hash .sign (secretKey, cache, message)
    result.finished = true ∧ result.cycles ≤ 31914272 ∧
      result.hashCalls = 122548 ∧ result.hashCompressions = 130710 := by
  obtain ⟨initial, final, steps, cycles, loaded, run, _, cyclesBound⟩ :=
    loaded_success hash secretKey cache message
  have actual := runWith_of_executes byteSubmission hash .sign
    (secretKey, cache, message) initial steps
    ⟨.success, final, cycles, 122548, 130710⟩ loaded run
    (by unfold CYCLE_LIMIT; omega)
  simp [actual, cyclesBound]

#print axioms loaded_success
#print axioms run_bound
end SigGolfCandidate.Hypertree.GroupedBalancedSignByteComplete67
