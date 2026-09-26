import SigGolfCandidate.Hypertree.GroupedBalancedBottomBadLogged67

/-! A bottom Merkle fault produces an output contact on the final verifier trace. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedBottomVerifyLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedGraphProgrammedReference67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem bad_verify_logged
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
    (pk : PublicKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (index : BitVec 160)
    (indexEq : Reference.indexOf
      (programmedGrouped residual secretKey labels)
      message signature.randomizer = index)
    (bad : GroupedBottomExtraction.Bad
      (programmedGrouped residual secretKey labels) secretKey 10
      (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom) :
    ∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.verify pk message signature) := by
  have indexBound : GroupedMixedIndex.bottomTree index < 2 ^ (160 - 10) := by
    change index.toNat / 2 ^ 10 < 2 ^ (160 - 10)
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 10)]
    have factor : 2 ^ (160 - 10) * 2 ^ 10 = 2 ^ 160 := by decide
    rw [factor]
    exact index.isLt
  obtain ⟨query, hit, member⟩ :=
    GroupedBalancedBottomBadLogged67.bad_contact_logged table residual
      secretKey labels labelsMatch bottomMatch sourceMatch 10
      (GroupedMixedIndex.bottomTree index) index.toNat (by decide)
      indexBound signature.bottom bad
  refine ⟨query, hit, ?_⟩
  apply GroupedBalancedVerifyTrace67.mem_verify_bottom
    (programmedGrouped residual secretKey labels) pk message signature query
  simpa only [indexEq] using member

#print axioms bad_verify_logged

end SigGolfCandidate.Hypertree.GroupedBalancedBottomVerifyLogged67
