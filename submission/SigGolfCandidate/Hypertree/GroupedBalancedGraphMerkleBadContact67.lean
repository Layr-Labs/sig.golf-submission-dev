import SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleExpected67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperMerkleExtraction67

/-! An upper authentication-path fault gives a public query that contacts a
canonical planted tree-node output. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleBadContact67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedUpperTree67
open GroupedBalancedUpperMerkleExtraction67
open SecurityExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem bad_contact (table : GroupedBalancedGraphPassive67.PointTable)
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
    (base : Fin 150) (message : Reference.Digest)
    (height address index : Nat)
    (heightBound : height ≤ 4)
    (levelBound : base.val + height ≤ 150)
    (aligned : ∀ offset < height,
      GroupedBalancedGraphPayload67.groupBase
        (base.val + 10 + offset) = base.val + 10)
    (addressBound : address < 2 ^ (160 - height))
    (witness : Witness height)
    (bad : Bad (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) message height address index witness) :
    ∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) := by
  induction height generalizing address with
  | zero =>
      cases witness with
      | leaf _ => exact False.elim bad
  | succ height ih =>
      cases witness with
      | step inner sibling =>
          have nodeLevel : base.val + height < 150 := by omega
          have childHeight : height ≤ 4 := by omega
          have nodeHeight : height < 4 := by omega
          have childAligned : ∀ offset < height,
              GroupedBalancedGraphPayload67.groupBase
                (base.val + 10 + offset) = base.val + 10 := by
            intro offset bound
            exact aligned offset (by omega)
          have capacity : 2 ^ (160 - height) =
              2 * 2 ^ (160 - (height + 1)) := by
            have exponent : 160 - height = 160 - (height + 1) + 1 := by omega
            rw [exponent, pow_succ]
            ring
          have leftBound : 2 * address < 2 ^ (160 - height) := by
            rw [capacity]
            omega
          have rightBound : 2 * address + 1 < 2 ^ (160 - height) := by
            rw [capacity]
            omega
          by_cases bit : index / 2 ^ height % 2 = 0
          · simp only [Bad, if_pos bit] at bad
            rcases bad with ⟨pairDifferent, sameRoot⟩ | childBad
            · let actualLeft := recover
                (programmedGrouped residual secretKey labels)
                (base.val + 10) height (2 * address) index message inner
              let expectedLeft := root
                (programmedGrouped residual secretKey labels)
                secretKey (base.val + 10) height (2 * address)
              let expectedRight := root
                (programmedGrouped residual secretKey labels)
                secretKey (base.val + 10) height (2 * address + 1)
              rcases node_binding (programmedGrouped residual secretKey labels)
                (base.val + 10 + height) address expectedLeft expectedRight
                actualLeft sibling sameRoot with equal | collision
              · exact False.elim (pairDifferent (Prod.ext equal.1 equal.2))
              · refine ⟨(upperNode ⟨base.val + height, nodeLevel⟩
                    (BitVec.ofNat 160 address)).input
                    (bytes actualLeft ++ bytes sibling), ?_⟩
                exact GroupedBalancedGraphMerkleExpected67.upper_node_collision_contact
                  table residual secretKey labels labelsMatch bottomMatch
                  sourceMatch base height address nodeHeight nodeLevel aligned
                  addressBound (bytes actualLeft ++ bytes sibling) collision
            · exact ih (2 * address) childHeight (le_of_lt nodeLevel) childAligned
                leftBound inner childBad
          · simp only [Bad, if_neg bit] at bad
            rcases bad with ⟨pairDifferent, sameRoot⟩ | childBad
            · let actualRight := recover
                (programmedGrouped residual secretKey labels)
                (base.val + 10) height (2 * address + 1) index message inner
              let expectedLeft := root
                (programmedGrouped residual secretKey labels)
                secretKey (base.val + 10) height (2 * address)
              let expectedRight := root
                (programmedGrouped residual secretKey labels)
                secretKey (base.val + 10) height (2 * address + 1)
              rcases node_binding (programmedGrouped residual secretKey labels)
                (base.val + 10 + height) address expectedLeft expectedRight
                sibling actualRight sameRoot with equal | collision
              · exact False.elim (pairDifferent (Prod.ext equal.1 equal.2))
              · refine ⟨(upperNode ⟨base.val + height, nodeLevel⟩
                    (BitVec.ofNat 160 address)).input
                    (bytes sibling ++ bytes actualRight), ?_⟩
                exact GroupedBalancedGraphMerkleExpected67.upper_node_collision_contact
                  table residual secretKey labels labelsMatch bottomMatch
                  sourceMatch base height address nodeHeight nodeLevel aligned
                  addressBound (bytes sibling ++ bytes actualRight) collision
            · exact ih (2 * address + 1) childHeight (le_of_lt nodeLevel) childAligned
                rightBound inner childBad

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleBadContact67
