import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorAuthorization67

/-! The direct 67-chain verifier's concrete earlier point is a specific
unauthorized coordinate of the passive table. Only used chain-source halves
must match; the unused 68th paired half has no security role. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorExposure67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
abbrev Digest := Reference.Digest

theorem earlierValue_eq_table (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67)
    (digit : Fin 11) :
    GroupedBalancedGraphEarlierExposure67.earlierValue residual secretKey labels
      base leaf chain digit =
    truncate (table (earlierPoint base leaf chain digit)) := by
  by_cases zero : digit.val = 0
  · simp only [GroupedBalancedGraphEarlierExposure67.earlierValue,
      earlierPoint, zero, if_pos, dif_pos]
    rw [← GroupedBalancedGraphReference67.upper_source_value
      residual secretKey base leaf chain]
    rw [sourceMatch, GroupedBalancedGraphMonitorTable67.upper_source]
  · simp only [GroupedBalancedGraphEarlierExposure67.earlierValue,
      earlierPoint, zero, if_neg, dif_neg]
    rw [labelsMatch]
    rfl

theorem exposure_at_unopened (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (table : PointTable)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (signedBottom : Finset (BitVec 160))
    (base : Fin 150) (leaf : BitVec 160)
    (forged : Digest) {height : Nat}
    (witness : GroupedBalancedUpperTree67.Witness height)
    (exposure : GroupedBalancedUpperPathFault67.EarlierPointExposure
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat
      (canonicalMessage labels base leaf) forged witness) :
    ∃ chain : Fin 67,
      let digit := GroupedBalancedUpperTree67.digit forged chain
      ¬Authorized labels signedBottom
        (earlierPoint base leaf chain digit) ∧
      GroupedBalancedUpperIndex67.witnessValues witness chain =
        truncate (table (earlierPoint base leaf chain digit)) := by
  obtain ⟨chain, earlier, point⟩ :=
    GroupedBalancedGraphEarlierExposure67.exposure_eq_graph_point
      residual secretKey labels base leaf
      (canonicalMessage labels base leaf) forged witness exposure
  refine ⟨chain, ?_, ?_⟩
  · exact earlier_unauthorized labels signedBottom base leaf chain
      (GroupedBalancedUpperTree67.digit forged chain) earlier
  · exact point.trans (earlierValue_eq_table residual secretKey labels table
      labelsMatch sourceMatch base leaf chain
      (GroupedBalancedUpperTree67.digit forged chain))

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorExposure67
