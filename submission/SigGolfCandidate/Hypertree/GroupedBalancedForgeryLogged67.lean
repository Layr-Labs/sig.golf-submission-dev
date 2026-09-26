import SigGolfCandidate.Hypertree.GroupedBalancedAcceptedLogged67
import SigGolfCandidate.Hypertree.GroupedBalancedBottomSourceLogged67
import SigGolfCandidate.Hypertree.GroupedBalancedSignedForgedLogged67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedUnsignedForgedLogged67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedForgeryLogged67. -/
section
/-! An accepted signature at an unsigned index forces an observed verifier
query to contact the grouped graph monitor. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUnsignedForgedLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem accepted_unsigned_logged
    (table : GroupedBalancedGraphPassive67.PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (safe : GroupedBalancedGraphMonitorInvariant67.ExposedSafe
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom exposed)
    (pk : PublicKey) (message : Message)
    (index : BitVec 160) (unsigned : index ∉ signedBottom)
    (signature : GroupedBalancedScheme67.Signature)
    (indexEq : Reference.indexOf
      (programmedGrouped residual secretKey labels)
      message signature.randomizer = index)
    (accepted : recoverLayers
      (programmedGrouped residual secretKey labels) Heights 10
      (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.recover
        (programmedGrouped residual secretKey labels) 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper = GroupedBalancedScheme67.keygen
        (programmedGrouped residual secretKey labels) secretKey) :
    (∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.verify pk message signature)) ∨
    (∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.inputHit table exposed query ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.verify pk message signature)) := by
  rcases GroupedBalancedAcceptedLogged67.accepted_logged_or_bottom_source
    table residual secretKey labels labelsMatch bottomMatch sourceMatch
    signedBottom exposed safe pk message index signature indexEq accepted with
    output | input | seed
  · exact Or.inl output
  · exact Or.inr input
  · exact Or.inr
      (GroupedBalancedBottomSourceLogged67.bottom_source_logged
        table residual secretKey labels bottomMatch signedBottom exposed safe
        pk message signature index indexEq unsigned seed)

#print axioms accepted_unsigned_logged

end SigGolfCandidate.Hypertree.GroupedBalancedUnsignedForgedLogged67

end

/-! A complete deterministic strong-forgery split for direct67: every
accepted fresh structured signature forces a logged graph verifier contact or
a distinct H5 input collision at a previously signed index. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedForgeryLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem accepted_fresh_logged_or_reuse
    (table : GroupedBalancedGraphPassive67.PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache GroupedBalancedGraphPassive67.PointSpec)
    (safe : GroupedBalancedGraphMonitorInvariant67.ExposedSafe
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom exposed)
    (responses : GroupedBalancedStrongExtraction67.History)
    (honest : GroupedBalancedStrongExtraction67.HonestHistory
      (programmedGrouped residual secretKey labels) secretKey responses)
    (indicesExact : ∀ index,
      index ∈ signedBottom ↔
        ∃ entry ∈ responses,
          Reference.indexOf (programmedGrouped residual secretKey labels)
            entry.1 entry.2.randomizer = index)
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (accepted : GroupedBalancedScheme67.verify
      (programmedGrouped residual secretKey labels)
      (GroupedBalancedScheme67.keygen
        (programmedGrouped residual secretKey labels) secretKey)
      message signature)
    (fresh : (message, signature) ∉ responses) :
    (∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.verify pk message signature)) ∨
    (∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.inputHit table exposed query ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.verify pk message signature)) ∨
    GroupedBalancedStrongExtraction67.PairReuse
      (programmedGrouped residual secretKey labels)
      responses message signature := by
  let hash := programmedGrouped residual secretKey labels
  let index := Reference.indexOf hash message signature.randomizer
  have indexEq : Reference.indexOf hash message signature.randomizer = index := rfl
  by_cases signed : index ∈ signedBottom
  · exact GroupedBalancedSignedForgedLogged67.accepted_signed_logged_or_reuse
      table residual secretKey labels labelsMatch bottomMatch sourceMatch
      signedBottom exposed safe responses honest pk message signature
      accepted fresh ((indicesExact index).mp signed)
  · have acceptedRoot : recoverLayers hash Heights 10
        (GroupedMixedIndex.bottomTree index)
        (GroupedBottomTree.recover hash 10
          (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
        signature.upper = GroupedBalancedScheme67.keygen hash secretKey := by
      simpa only [GroupedBalancedScheme67.verify, index] using accepted
    rcases GroupedBalancedUnsignedForgedLogged67.accepted_unsigned_logged
      table residual secretKey labels labelsMatch bottomMatch sourceMatch
      signedBottom exposed safe pk message index signed signature indexEq
      acceptedRoot with output | input
    · exact Or.inl output
    · exact Or.inr (Or.inl input)

#print axioms accepted_fresh_logged_or_reuse

end SigGolfCandidate.Hypertree.GroupedBalancedForgeryLogged67
