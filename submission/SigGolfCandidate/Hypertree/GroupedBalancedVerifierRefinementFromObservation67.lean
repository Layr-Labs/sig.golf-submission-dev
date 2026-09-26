import SigGolfCandidate.Hypertree.GroupedBalancedVerifyRefineFromEntry67

/-! Package the loaded verifier's semantic entry state into the exact
arbitrary-wire refinement needed by the security proof. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifierRefinementFromObservation67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev program := GroupedBalancedProgram67ByteSign.submission

def EntryObservation : Prop :=
  ∀ (hash : Hash) (pk : PublicKey) (message : Message)
    (wire : Bytes 50848),
    ∃ initial entry : MachineState,
      initialState program .verify (message,pk,wire) = some initial ∧
      GroupedBalancedVerifyStackGlobal67.LowFrame initial entry ∧
      (program.runWith hash .verify (message,pk,wire)).value.isSome =
        decide (GroupedBalancedVerifyGroupFold67.rootAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
          45 = GroupedBalancedVerifyFinalGroup67.publicKeyDigest initial) ∧
      (program.runWith hash .verify (message,pk,wire)).hashCalls =
        12+GroupedBalancedVerifyGroupFold67.callsAt hash entry
          (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat
          45 ∧
      (GroupedBalancedVerifyTreeLoadedDecoderSafe67.currentIndex entry).toNat =
        GroupedMixedIndex.bottomTree
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer) ∧
      GroupedBalancedVerifyTreeDecoderHandoff67.currentRoot entry =
        GroupedBottomTree.recover hash 10
          (GroupedMixedIndex.bottomTree
            (Reference.indexOf hash message
              (GroupedBalancedWire67.decode wire).randomizer))
          (Reference.indexOf hash message
            (GroupedBalancedWire67.decode wire).randomizer).toNat
          (GroupedBalancedWire67.decode wire).bottom

theorem verifier_refinement (observation : EntryObservation) :
    GroupedBalancedSecurityCheckConditional67.VerifierRefinement := by
  intro hash pk message wire
  obtain ⟨initial,entry,loaded,frame,value,calls,index,root⟩ :=
    observation hash pk message wire
  exact GroupedBalancedVerifyRefineFromEntry67.one hash pk message wire
    initial entry loaded frame value calls index root

#print axioms verifier_refinement
end SigGolfCandidate.Hypertree.GroupedBalancedVerifierRefinementFromObservation67
