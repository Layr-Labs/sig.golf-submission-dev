import SigGolfCandidate.Hypertree.GroupedBalancedGraphPathFaultContact67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorSuccessor67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorExposure67

/-! A verifier starting a WOTS chain strictly before the signed frontier
queries a hidden canonical predecessor and triggers the monitor input contact. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphEarlierInputHit67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorAuthorization67
open GroupedBalancedGraphMonitorPredecessor67
open GroupedBalancedGraphMonitorPublicCoupling67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem predecessor_earlier (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (digit : Fin 11) (bound : digit.val < 10) :
    predecessor
      (upperChain base leaf chain ⟨digit.val, bound⟩).val =
      some (earlierPoint base leaf chain digit) := by
  by_cases zero : digit.val = 0
  · have stepEq : (⟨digit.val, bound⟩ : Fin 10) = 0 := Fin.ext zero
    rw [stepEq,
      GroupedBalancedGraphMonitorSuccessor67.predecessor_upper_zero]
    simp only [earlierPoint, zero, dif_pos]
  · have positive : 0 < (⟨digit.val, bound⟩ : Fin 10).val := by
      change 0 < digit.val
      omega
    rw [GroupedBalancedGraphMonitorSuccessor67.predecessor_upper_positive
      base leaf chain ⟨digit.val, bound⟩ positive]
    simp [earlierPoint, zero]

theorem exposure_inputHit
    (table : GroupedBalancedGraphPassive67.PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (sourceMatch : ∀ base leaf chain,
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      GroupedBalancedGraphPayload67.chainSource
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (signedBottom : Finset (BitVec 160))
    (exposed : QueryCache PointSpec)
    (safe : GroupedBalancedGraphMonitorInvariant67.ExposedSafe
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom exposed)
    (base : Fin 150) (leaf : BitVec 160)
    (signed forged : Reference.Digest)
    (signedEq : signed = canonicalMessage labels base leaf)
    {height : Nat} (witness : GroupedBalancedUpperTree67.Witness height)
    (exposure : GroupedBalancedUpperPathFault67.EarlierPointExposure
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat signed forged witness) :
    ∃ query, inputHit table exposed query := by
  obtain ⟨chain, earlier, witnessEq⟩ :=
    GroupedBalancedGraphEarlierExposure67.exposure_eq_graph_point
      residual secretKey labels base leaf signed forged witness exposure
  let digit := GroupedBalancedUpperTree67.digit forged chain
  have digitBound := GroupedBalancedChecksum67.digit_le_max signed chain
  change (GroupedBalancedUpperTree67.digit signed chain).val ≤
    GroupedBalancedUpperTree67.maxDigit chain at digitBound
  have maxBound := GroupedBalancedSecurityGraph67.max_digit_le_ten chain
  have stepBound : digit.val < 10 := by
    dsimp [digit]
    omega
  let position := upperChain base leaf chain ⟨digit.val, stepBound⟩
  let point := earlierPoint base leaf chain digit
  have previous : predecessor position.val = some point := by
    exact predecessor_earlier base leaf chain digit stepBound
  have unauthorized : ¬Authorized
      (GroupedBalancedGraphMonitorTable67.labelsOf table)
      signedBottom point := by
    rw [← labelsMatch]
    apply earlier_unauthorized labels signedBottom base leaf chain digit
    change digit.val <
      (GroupedBalancedUpperTree67.digit
        (canonicalMessage labels base leaf) chain).val
    rw [← signedEq]
    exact earlier
  have hidden : exposed point = none :=
    safe.hidden _ _ exposed point unauthorized
  have valueEq :
      GroupedBalancedUpperIndex67.witnessValues witness chain =
      truncate (table point) := by
    exact witnessEq.trans
      (GroupedBalancedGraphMonitorExposure67.earlierValue_eq_table
        residual secretKey labels table labelsMatch sourceMatch
        base leaf chain digit)
  let query := position.input
    (bytes (GroupedBalancedUpperIndex67.witnessValues witness chain))
  have canonical : query =
      GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
    have chainPayload :=
      GroupedBalancedGraphMonitorPredecessor67.chain_payload_eq table position.val
    rw [previous] at chainPayload
    dsimp only [query]
    rw [valueEq]
    simp only [query, GroupedBalancedGraphCausality67.graphInput]
    have tagTwo : position.val.tag.val = 2 := by rfl
    rw [GroupedBalancedGraphPayload67.payload, if_pos tagTwo]
    exact congrArg position.input chainPayload.symm
  refine ⟨query, ?_⟩
  have located : GroupedBalancedGraphQuery67.locate query = some position := by
    exact GroupedBalancedGraphQuery67.locate_address position _
  have tagTwo : position.val.tag.val = 2 := by rfl
  simp only [inputHit, located, tagTwo, if_pos, previous]
  exact ⟨hidden, canonical⟩

end SigGolfCandidate.Hypertree.GroupedBalancedGraphEarlierInputHit67
