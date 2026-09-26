import SigGolfCandidate.Hypertree.GroupedBalancedVerifyLoadedComplete67

/-! The completed verifier trace runs within the organizer fuel budget. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyRun67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyGroupFold67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev program := GroupedBalancedProgram67ByteSign.submission

theorem run_observation (hash : Hash)
    (input : Input program.sizes .verify) :
    ∃ initial entry cycles,
      initialState program .verify input = some initial ∧
      cycles ≤ 156325 ∧
      (program.runWith hash .verify input).finished = true ∧
      (program.runWith hash .verify input).cycles = cycles ∧
      (program.runWith hash .verify input).value.isSome =
        decide (rootAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
          45 = GroupedBalancedVerifyFinalGroup67.publicKeyDigest initial) ∧
      (program.runWith hash .verify input).hashCalls =
        12+callsAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
          45 ∧
      (program.runWith hash .verify input).hashCompressions =
        13+blocksAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
          45 ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame initial entry ∧
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat =
        GroupedMixedIndex.bottomTree
          (Reference.indexOf hash input.1
            (GroupedBalancedWire67.decode input.2.2).randomizer) ∧
      GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry =
        GroupedBottomTree.recover hash 10
          (GroupedMixedIndex.bottomTree
            (Reference.indexOf hash input.1
              (GroupedBalancedWire67.decode input.2.2).randomizer))
          (Reference.indexOf hash input.1
            (GroupedBalancedWire67.decode input.2.2).randomizer).toNat
          (GroupedBalancedWire67.decode input.2.2).bottom := by
  obtain ⟨initial,entry,final,steps,cycles,loaded,stepsBound,
    cyclesBound,exec,low,indexEq,rootEq⟩ :=
    GroupedBalancedVerifyLoadedComplete67.loaded_complete hash input
  let accept := rootAt hash entry
    (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
    45 = GroupedBalancedVerifyFinalGroup67.publicKeyDigest initial
  have limit : steps ≤ CYCLE_LIMIT := by
    have h : 161393 ≤ CYCLE_LIMIT := by decide
    omega
  have run := runWith_of_executes program hash .verify input initial steps
    ⟨if accept then .success else .failure,final,cycles,
      12+callsAt hash entry
        (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat 45,
      13+blocksAt hash entry
        (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat 45⟩
    loaded exec limit
  have result : program.runWith hash .verify input =
      ⟨if accept then
          some (readOutput program.sizes program.layout .verify final)
        else none,
        true,cycles,
        12+callsAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
          45,
        13+blocksAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
          45⟩ := by
    have yes : (Exit.success != Exit.unfinished) = true := by decide
    have no : (Exit.failure != Exit.unfinished) = true := by decide
    by_cases h : accept
    · simpa [h,yes] using run
    · simpa [h,no] using run
  refine ⟨initial,entry,cycles,loaded,cyclesBound,?_,?_,?_,?_,?_,low,
    indexEq,rootEq⟩
  · rw [result]
  · rw [result]
  · rw [result]
    by_cases h : accept <;> simp [accept,h]
  · rw [result]
  · rw [result]

#print axioms run_observation
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyRun67
