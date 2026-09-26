import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleExpected67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperMerkleExtraction67


/-! Address-level trace membership for an upper Merkle node query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperContactTrace67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67
open GroupedBalancedVerifyOracle67
open SecurityVerifyTrace
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem node_query (hash : Hash) (base : Fin 150)
    (height address index : Nat) (message : Reference.Digest)
    (levelBound : base.val + height < 150)
    (addressBound : address < 2 ^ 160)
    (inner : GroupedBalancedUpperTree67.Witness height)
    (sibling : Reference.Digest) :
    let child := if index / 2 ^ height % 2 = 0 then 2 * address
      else 2 * address + 1
    let current := GroupedBalancedUpperTree67.recover hash (base.val + 10)
      height child index message inner
    (upperNode ⟨base.val + height, levelBound⟩
      (BitVec.ofNat 160 address)).input
      (if index / 2 ^ height % 2 = 0 then
        bytes current ++ bytes sibling
      else bytes sibling ++ bytes current) ∈
      queries hash (recoverUpper (base.val + 10) (height + 1)
        address index message (.step inner sibling)) := by
  dsimp only
  rw [upper_node_input]
  have treeValue : (BitVec.ofNat 160 address).toNat = address := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBound]
  rw [treeValue]
  have levelValue : (⟨base.val + height, levelBound⟩ : Fin 150).val + 10 =
      base.val + 10 + height := by simp only [Fin.val_mk]; omega
  rw [levelValue]
  exact GroupedBalancedVerifyTrace67.mem_recoverUpper_node hash
    (base.val + 10) height address index message inner sibling

end SigGolfCandidate.Hypertree.GroupedBalancedUpperContactTrace67


/-! An upper authentication-path fault contacts a planted output at an
actual verifier query. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperMerkleBadLogged67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedUpperTree67
open GroupedBalancedUpperMerkleExtraction67
open SecurityExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem bad_contact_logged (table : GroupedBalancedGraphPassive67.PointTable)
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
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.recoverUpper
          (base.val + 10) height address index message witness) := by
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
          have addressFits : address < 2 ^ 160 := by
            exact lt_of_lt_of_le addressBound
              (Nat.pow_le_pow_right (by decide) (by omega))
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
              · let query := (upperNode ⟨base.val + height, nodeLevel⟩
                    (BitVec.ofNat 160 address)).input
                    (bytes actualLeft ++ bytes sibling)
                refine ⟨query, ?_, ?_⟩
                · exact GroupedBalancedGraphMerkleExpected67.upper_node_collision_contact
                    table residual secretKey labels labelsMatch bottomMatch
                    sourceMatch base height address nodeHeight nodeLevel aligned
                    addressBound (bytes actualLeft ++ bytes sibling) collision
                · simpa only [if_pos bit, actualLeft] using
                    (GroupedBalancedUpperContactTrace67.node_query
                      (programmedGrouped residual secretKey labels)
                      base height address index message nodeLevel addressFits
                      inner sibling)
            · obtain ⟨query, contact, member⟩ := ih (2 * address)
                childHeight (le_of_lt nodeLevel) childAligned leftBound inner childBad
              refine ⟨query, contact, ?_⟩
              exact GroupedBalancedVerifyTrace67.mem_recoverUpper_inner
                (programmedGrouped residual secretKey labels)
                (base.val + 10) height address index message inner sibling query
                (by simpa only [if_pos bit] using member)
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
              · let query := (upperNode ⟨base.val + height, nodeLevel⟩
                    (BitVec.ofNat 160 address)).input
                    (bytes sibling ++ bytes actualRight)
                refine ⟨query, ?_, ?_⟩
                · exact GroupedBalancedGraphMerkleExpected67.upper_node_collision_contact
                    table residual secretKey labels labelsMatch bottomMatch
                    sourceMatch base height address nodeHeight nodeLevel aligned
                    addressBound (bytes sibling ++ bytes actualRight) collision
                · simpa only [if_neg bit, actualRight] using
                    (GroupedBalancedUpperContactTrace67.node_query
                      (programmedGrouped residual secretKey labels)
                      base height address index message nodeLevel addressFits
                      inner sibling)
            · obtain ⟨query, contact, member⟩ := ih (2 * address + 1)
                childHeight (le_of_lt nodeLevel) childAligned rightBound inner childBad
              refine ⟨query, contact, ?_⟩
              exact GroupedBalancedVerifyTrace67.mem_recoverUpper_inner
                (programmedGrouped residual secretKey labels)
                (base.val + 10) height address index message inner sibling query
                (by simpa only [if_neg bit] using member)

#print axioms bad_contact_logged

end SigGolfCandidate.Hypertree.GroupedBalancedUpperMerkleBadLogged67
