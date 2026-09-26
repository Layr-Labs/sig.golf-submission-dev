import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTrace67
import SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomMerkleContact67


/-! Address-level trace membership for the two bottom Merkle fault queries. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedBottomContactTrace67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67
open GroupedBalancedVerifyOracle67
open SecurityVerifyTrace
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem leaf_query (hash : Hash) (address : Nat)
    (addressBound : address < 2 ^ 160)
    (seed : Reference.Digest) :
    (bottomLeaf (BitVec.ofNat 160 address)).input (bytes seed) ∈
      queries hash (recoverBottom 0 address address (.seed seed)) := by
  rw [bottom_leaf_input, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt addressBound]
  simp only [recoverBottom, GroupedBalancedVerifyTrace67.queries_bottomLeaf]
  exact List.mem_singleton_self _

theorem node_query (hash : Hash) (height address index : Nat)
    (heightBound : height < 10) (addressBound : address < 2 ^ 160)
    (inner : GroupedBottomTree.Witness height)
    (sibling : Reference.Digest) :
    let child := if index / 2 ^ height % 2 = 0 then 2 * address
      else 2 * address + 1
    let current := GroupedBottomTree.recover hash height child index inner
    (bottomNode (Fin.ofNat 10 height) (BitVec.ofNat 160 address)).input
      (if index / 2 ^ height % 2 = 0 then
        bytes current ++ bytes sibling
      else bytes sibling ++ bytes current) ∈
      queries hash (recoverBottom (height + 1) address index
        (.step inner sibling)) := by
  dsimp only
  rw [bottom_node_input]
  have levelValue : (Fin.ofNat 10 height).val = height := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt heightBound]
  have treeValue : (BitVec.ofNat 160 address).toNat = address := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBound]
  rw [levelValue, treeValue]
  exact GroupedBalancedVerifyTrace67.mem_recoverBottom_node hash
    height address index inner sibling

end SigGolfCandidate.Hypertree.GroupedBalancedBottomContactTrace67


/-! Every bottom-path collision fault is a monitored output contact on an
actual query in the bottom verifier walk. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedBottomBadLogged67
open SigGolf SigGolfCandidate.Hypertree Reference OracleSpec
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBottomTree GroupedBottomExtraction SecurityExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem bad_contact_logged
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
    (height address index : Nat)
    (heightBound : height ≤ 10)
    (addressBound : address < 2 ^ (160 - height))
    (witness : Witness height)
    (bad : Bad (programmedGrouped residual secretKey labels)
      secretKey height address index witness) :
    ∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) ∧
      query ∈ SecurityVerifyTrace.queries
        (programmedGrouped residual secretKey labels)
        (GroupedBalancedVerifyOracle67.recoverBottom height address index witness) := by
  induction height generalizing address with
  | zero =>
      cases witness with
      | seed seed =>
          obtain ⟨different, same⟩ := bad
          have collision : CollisionAt
              (programmedGrouped residual secretKey labels)
              2 0 address 0 0 0
              (bytes (secret (programmedGrouped residual secretKey labels)
                secretKey address)) (bytes seed) :=
            collisionAt_of_payload_ne _ 2 0 address 0 0 0 _ _
              (fun equal => different (SecurityPacking.bytes_injective 16 equal))
              (by simpa only [GroupedBottomTree.leafRoot,
                GroupedBottomTree.leafFromSeed] using same)
          have addressFits : (BitVec.ofNat 160 address).toNat = address := by
            rw [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt (by simpa using addressBound)
          have sourceEq :
              GroupedBottomTree.secret
                (programmedGrouped residual secretKey labels)
                secretKey address =
              GroupedBottomTree.secret residual secretKey address := by
            simpa only [addressFits] using
              GroupedBalancedGraphProgrammedReference67.programmed_bottom_secret
                residual secretKey labels (BitVec.ofNat 160 address)
          rw [sourceEq] at collision
          let query := (bottomLeaf (BitVec.ofNat 160 address)).input (bytes seed)
          refine ⟨query, ?_, ?_⟩
          · exact GroupedBalancedGraphMonitorCollisionBridge67.bottom_leaf_collision_outputHit
              table residual secretKey labels labelsMatch bottomMatch
              sourceMatch (BitVec.ofNat 160 address) (bytes seed)
              (by simpa only [addressFits] using collision)
          · exact GroupedBalancedBottomContactTrace67.leaf_query
              (programmedGrouped residual secretKey labels) address
              (by simpa using addressBound) seed
  | succ height ih =>
      cases witness with
      | step inner sibling =>
          have nodeHeight : height < 10 := by omega
          have childHeight : height ≤ 10 := by omega
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
                height (2 * address) index inner
              let expectedLeft := root
                (programmedGrouped residual secretKey labels)
                secretKey height (2 * address)
              let expectedRight := root
                (programmedGrouped residual secretKey labels)
                secretKey height (2 * address + 1)
              rcases node_binding (programmedGrouped residual secretKey labels)
                height address expectedLeft expectedRight actualLeft sibling
                sameRoot with equal | collision
              · exact False.elim (pairDifferent (Prod.ext equal.1 equal.2))
              · let query := (bottomNode (Fin.ofNat 10 height)
                    (BitVec.ofNat 160 address)).input
                    (bytes actualLeft ++ bytes sibling)
                refine ⟨query, ?_, ?_⟩
                · exact GroupedBalancedGraphBottomMerkleContact67.bottom_node_collision_contact
                    table residual secretKey labels labelsMatch bottomMatch
                    sourceMatch height address nodeHeight addressBound
                    (bytes actualLeft ++ bytes sibling) collision
                · simpa only [if_pos bit, actualLeft] using
                    (GroupedBalancedBottomContactTrace67.node_query
                      (programmedGrouped residual secretKey labels)
                      height address index nodeHeight addressFits inner sibling)
            · obtain ⟨query, contact, member⟩ :=
                ih (2 * address) childHeight leftBound inner childBad
              refine ⟨query, contact, ?_⟩
              exact GroupedBalancedVerifyTrace67.mem_recoverBottom_inner
                (programmedGrouped residual secretKey labels)
                height address index inner sibling query
                (by simpa only [if_pos bit] using member)
          · simp only [Bad, if_neg bit] at bad
            rcases bad with ⟨pairDifferent, sameRoot⟩ | childBad
            · let actualRight := recover
                (programmedGrouped residual secretKey labels)
                height (2 * address + 1) index inner
              let expectedLeft := root
                (programmedGrouped residual secretKey labels)
                secretKey height (2 * address)
              let expectedRight := root
                (programmedGrouped residual secretKey labels)
                secretKey height (2 * address + 1)
              rcases node_binding (programmedGrouped residual secretKey labels)
                height address expectedLeft expectedRight sibling actualRight
                sameRoot with equal | collision
              · exact False.elim (pairDifferent (Prod.ext equal.1 equal.2))
              · let query := (bottomNode (Fin.ofNat 10 height)
                    (BitVec.ofNat 160 address)).input
                    (bytes sibling ++ bytes actualRight)
                refine ⟨query, ?_, ?_⟩
                · exact GroupedBalancedGraphBottomMerkleContact67.bottom_node_collision_contact
                    table residual secretKey labels labelsMatch bottomMatch
                    sourceMatch height address nodeHeight addressBound
                    (bytes sibling ++ bytes actualRight) collision
                · simpa only [if_neg bit, actualRight] using
                    (GroupedBalancedBottomContactTrace67.node_query
                      (programmedGrouped residual secretKey labels)
                      height address index nodeHeight addressFits inner sibling)
            · obtain ⟨query, contact, member⟩ :=
                ih (2 * address + 1) childHeight rightBound inner childBad
              refine ⟨query, contact, ?_⟩
              exact GroupedBalancedVerifyTrace67.mem_recoverBottom_inner
                (programmedGrouped residual secretKey labels)
                height address index inner sibling query
                (by simpa only [if_neg bit] using member)

end SigGolfCandidate.Hypertree.GroupedBalancedBottomBadLogged67
