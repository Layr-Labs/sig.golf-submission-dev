import SigGolfCandidate.Hypertree.GroupedBalancedSecurityObservedPhases67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphHonestSignView67
import SigGolfCandidate.Hypertree.GroupedBalancedOrganizerCoherence67

/-! The actual signer returns the graph-view signature when planted private
sources agree with the residual oracle's private derivations. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityProgrammedSign67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphProgrammedReference67
set_option maxRecDepth 8192

private abbrev submission := GroupedBalancedProgram67ByteSign.submission

theorem graph_signature (residual : Hash) (secretKey : SecretKey)
    (labels : Labels) (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index : BitVec 160,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (request : SigningRequest) :
    let hash := programmedGrouped residual secretKey labels
    let randomizer := residual
      (SecurityRandomOracle.randomizerInput secretKey request.message)
    let indexAnswer := residual
      (SecurityRandomOracle.indexInput request.message randomizer)
    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
    evalWithAnswerFn hash (GroupedBalancedSecurityObservedPhases67.view <$>
      submission.signingOracle secretKey request) =
      (some (GroupedBalancedWire67.wire
        (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
          (GroupedBalancedGraphMonitorSetup67.cache table) randomizer index
          (table (.inr (.inl index))))),122548) := by
  dsimp only
  rw [GroupedBalancedSecurityObservedPhases67.signing]
  rw [GroupedBalancedGraphHonestSignView67.programmed_sign_from_answers
    residual secretKey labels table labelsMatch bottomMatch sourceMatch
    request.message]

theorem completed_signature (table : PointTable)
    (answers : SecurityGraphIdeal.PrivateTable)
    (secretKey : SecretKey) (finalCache : QueryCache HashSpec)
    (request : SigningRequest) :
    let residual := GroupedBalancedResidualCompletion67.completion
      table answers secretKey finalCache
    let hash := programmedGrouped residual secretKey
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
    let randomizer := answers (.randomizer request.message)
    let indexAnswer := hash
      (SecurityRandomOracle.indexInput request.message randomizer)
    let index : BitVec 160 := indexAnswer.extractLsb' 0 160
    evalWithAnswerFn hash (GroupedBalancedSecurityObservedPhases67.view <$>
      submission.signingOracle secretKey request) =
      (some (GroupedBalancedWire67.wire
        (GroupedBalancedGraphHonestSignView67.signatureFromAnswers
          (GroupedBalancedGraphMonitorSetup67.cache table) randomizer index
          (table (.inr (.inl index))))),122548) := by
  dsimp only
  rw [GroupedBalancedSecurityObservedPhases67.signing]
  have honest := GroupedBalancedOrganizerCoherence67.completion_signLaw
    table answers secretKey finalCache request.message
      ((programmedGrouped
        (GroupedBalancedResidualCompletion67.completion
          table answers secretKey finalCache) secretKey
          (GroupedBalancedGraphMonitorTable67.labelsOf table))
        (SecurityRandomOracle.indexInput request.message
          (answers (.randomizer request.message)))) rfl
  rw [honest]

#print axioms graph_signature
#print axioms completed_signature

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityProgrammedSign67
