import SigGolfCandidate.Hypertree.GroupedBalancedAcceptedLogged67
import SigGolfCandidate.Hypertree.GroupedBalancedStrongExtraction67
import SigGolfCandidate.Hypertree.GroupedBalancedBottomVerifyLogged67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedUpperVerifyLogged67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignedForgedLogged67. -/
section
/-! A fault in any of the 45 upper groups is a graph monitor contact on
the final verifier trace, including the earlier signed-frontier case. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperVerifyLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedGraphSignHistory67
open GroupedBalancedGraphCanonicalRoot67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem upper_fault_verify_logged
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
    (index : BitVec 160) (signature : GroupedBalancedScheme67.Signature)
    (indexEq : Reference.indexOf
      (programmedGrouped residual secretKey labels)
      message signature.randomizer = index)
    (upper : GroupedBalancedMixedPathFault67.UpperFault
      (programmedGrouped residual secretKey labels)
      secretKey index signature) :
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
  let hash := programmedGrouped residual secretKey labels
  have indexEqHash : Reference.indexOf hash message signature.randomizer =
      index := indexEq
  have indexBound : GroupedMixedIndex.bottomTree index < 2 ^ (160 - 10) := by
    change index.toNat / 2 ^ 10 < 2 ^ (160 - 10)
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 10)]
    have factor : 2 ^ (160 - 10) * 2 ^ 10 = 2 ^ 160 := by decide
    rw [factor]
    exact index.isLt
  rcases GroupedBalancedPathFaultLogged67.path_fault_logged_or_exposure
      table residual secretKey labels labelsMatch bottomMatch sourceMatch
      Heights 10 (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.root hash secretKey 10
        (GroupedMixedIndex.bottomTree index))
      (GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper heights_schedule (by decide) (by decide)
      indexBound upper with contact | exposure
  · obtain ⟨query, hit, member⟩ := contact
    refine Or.inl ⟨query, hit, ?_⟩
    apply GroupedBalancedVerifyTrace67.mem_verify_upper hash pk
      message signature query
    simpa only [indexEqHash] using member
  · have incoming :
        ∃ baseFin : Fin 150, baseFin.val + 10 = 10 ∧
          GroupedBottomTree.root hash secretKey 10
            (GroupedMixedIndex.bottomTree index) =
          GroupedBalancedGraphMonitorAuthorization67.canonicalMessage
            labels baseFin
            (BitVec.ofNat 160 (GroupedMixedIndex.bottomTree index)) := by
      refine ⟨⟨0, by decide⟩, rfl, ?_⟩
      exact bottom_root_canonical residual secretKey labels index
    obtain ⟨query, hit, member⟩ :=
      GroupedBalancedPathInputLogged67.earlier_exposure_logged
        table residual secretKey labels labelsMatch sourceMatch
        signedBottom exposed safe Heights 10
        (GroupedMixedIndex.bottomTree index)
        (GroupedBottomTree.root hash secretKey 10
          (GroupedMixedIndex.bottomTree index))
        (GroupedBottomTree.recover hash 10
          (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
        signature.upper heights_schedule (by decide) (by decide)
        indexBound incoming exposure
    refine Or.inr ⟨query, hit, ?_⟩
    apply GroupedBalancedVerifyTrace67.mem_verify_upper hash pk
      message signature query
    simpa only [indexEqHash] using member

#print axioms upper_fault_verify_logged

end SigGolfCandidate.Hypertree.GroupedBalancedUpperVerifyLogged67

end

/-! A fresh accepted pair at a signed index either contacts the graph monitor
on a verifier read or reuses the index through a distinct H5 input. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignedForgedLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedScheme67
open GroupedBalancedGraphProgrammedReference67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem accepted_signed_logged_or_reuse
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
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (accepted : GroupedBalancedScheme67.verify
      (programmedGrouped residual secretKey labels)
      (GroupedBalancedScheme67.keygen
        (programmedGrouped residual secretKey labels) secretKey)
      message signature)
    (fresh : (message, signature) ∉ responses)
    (signedIndex : ∃ entry ∈ responses,
      Reference.indexOf (programmedGrouped residual secretKey labels)
        entry.1 entry.2.randomizer =
      Reference.indexOf (programmedGrouped residual secretKey labels)
        message signature.randomizer) :
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
  rcases GroupedBalancedStrongExtraction67.signed_index_fresh_fault_or_reuse
      hash secretKey responses honest message signature accepted fresh
      signedIndex with upper | bottom | reuse
  · rcases GroupedBalancedUpperVerifyLogged67.upper_fault_verify_logged
        table residual secretKey labels labelsMatch bottomMatch sourceMatch
        signedBottom exposed safe pk message index signature indexEq upper with
        output | input
    · exact Or.inl output
    · exact Or.inr (Or.inl input)
  · exact Or.inl
      (GroupedBalancedBottomVerifyLogged67.bad_verify_logged table
        residual secretKey labels labelsMatch bottomMatch sourceMatch
        pk message signature index indexEq bottom)
  · exact Or.inr (Or.inr reuse)

#print axioms accepted_signed_logged_or_reuse

end SigGolfCandidate.Hypertree.GroupedBalancedSignedForgedLogged67
