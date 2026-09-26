import SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleBadContact67
import SigGolfCandidate.Hypertree.GroupedBottomExtraction

/-! A bottom authentication-path fault, including its selected leaf seed,
contacts a planted graph output. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomMerkleContact67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedGraphProgrammedTree67
open GroupedBottomTree GroupedBottomExtraction SecurityExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem bottom_node_expected (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (height address : Nat) (heightBound : height < 10)
    (addressBound : address < 2 ^ (160 - (height + 1))) :
    GroupedBalancedGraphPayload67.nodePayload labels
      (bottomNode (Fin.ofNat 10 height) (BitVec.ofNat 160 address)).val =
      bytes (root (programmedGrouped residual secretKey labels)
        secretKey height (2 * address)) ++
      bytes (root (programmedGrouped residual secretKey labels)
        secretKey height (2 * address + 1)) := by
  have addressFits : address < 2 ^ 160 := by
    exact lt_of_lt_of_le addressBound (Nat.pow_le_pow_right (by decide) (by omega))
  have treeValue : (BitVec.ofNat 160 address).toNat = address := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt addressFits
  have capacity : 2 ^ (160 - height) =
      2 * 2 ^ (160 - (height + 1)) := by
    have exponent : 160 - height = 160 - (height + 1) + 1 := by omega
    rw [exponent, pow_succ]
    ring
  have childLeft : 2 * address < 2 ^ (160 - height) := by
    rw [capacity]
    omega
  have childRight : 2 * address + 1 < 2 ^ (160 - height) := by
    rw [capacity]
    omega
  have children := bottomRootPosition_children height heightBound
    (BitVec.ofNat 160 address)
  rw [treeValue] at children
  rw [GroupedBalancedGraphPayload67.nodePayload, children]
  rw [programmed_bottom_root residual secretKey labels height
      (2 * address) (by omega) childLeft]
  rw [programmed_bottom_root residual secretKey labels height
      (2 * address + 1) (by omega) childRight]

theorem bottom_node_collision_contact
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
    (height address : Nat) (heightBound : height < 10)
    (addressBound : address < 2 ^ (160 - (height + 1)))
    (actual : List Byte)
    (collision : CollisionAt (programmedGrouped residual secretKey labels)
      4 height address 0 0 0
      (bytes (root (programmedGrouped residual secretKey labels)
        secretKey height (2 * address)) ++
       bytes (root (programmedGrouped residual secretKey labels)
        secretKey height (2 * address + 1))) actual) :
    GroupedBalancedGraphMonitorPublicCoupling67.outputHit table
      ((bottomNode (Fin.ofNat 10 height)
        (BitVec.ofNat 160 address)).input actual)
      ((programmedGrouped residual secretKey labels)
        ((bottomNode (Fin.ofNat 10 height)
          (BitVec.ofNat 160 address)).input actual)) := by
  let position := bottomNode (Fin.ofNat 10 height)
    (BitVec.ofNat 160 address)
  have expected := bottom_node_expected residual secretKey labels
    height address heightBound addressBound
  apply GroupedBalancedGraphMonitorCollisionBridge67.programmed_collision_outputHit
    table residual secretKey labels labelsMatch bottomMatch sourceMatch
    position 4 height address 0 0 0
    (bytes (root (programmedGrouped residual secretKey labels)
      secretKey height (2 * address)) ++
     bytes (root (programmedGrouped residual secretKey labels)
      secretKey height (2 * address + 1))) actual
  · intro payload
    have treeValue : (BitVec.ofNat 160 address).toNat = address := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le addressBound
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have levelValue : (Fin.ofNat 10 height).val = height := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt heightBound]
    simpa only [position, bottom_node_input, treeValue, levelValue]
  · have nodeEq := GroupedBalancedGraphPayload67.node_payload_of_tag_four
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
      labels position (by rfl) (by
        simp only [position, bottomNode, Fin.val_ofNat]
        have := heightBound
        omega)
    change position.input _ = position.input
      (GroupedBalancedGraphPayload67.payload
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        labels position)
    exact congrArg position.input (expected.symm.trans nodeEq.symm)
  · exact collision

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
    (height address index : Nat)
    (heightBound : height ≤ 10)
    (addressBound : address < 2 ^ (160 - height))
    (witness : Witness height)
    (bad : Bad (programmedGrouped residual secretKey labels)
      secretKey height address index witness) :
    ∃ query,
      GroupedBalancedGraphMonitorPublicCoupling67.outputHit table query
        ((programmedGrouped residual secretKey labels) query) := by
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
          refine ⟨(bottomLeaf (BitVec.ofNat 160 address)).input (bytes seed), ?_⟩
          exact GroupedBalancedGraphMonitorCollisionBridge67.bottom_leaf_collision_outputHit
            table residual secretKey labels labelsMatch bottomMatch
            sourceMatch (BitVec.ofNat 160 address) (bytes seed)
            (by simpa only [addressFits] using collision)
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
              · refine ⟨(bottomNode (Fin.ofNat 10 height)
                    (BitVec.ofNat 160 address)).input
                    (bytes actualLeft ++ bytes sibling), ?_⟩
                exact bottom_node_collision_contact table residual secretKey
                  labels labelsMatch bottomMatch sourceMatch height address
                  nodeHeight addressBound (bytes actualLeft ++ bytes sibling)
                  collision
            · exact ih (2 * address) childHeight leftBound inner childBad
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
              · refine ⟨(bottomNode (Fin.ofNat 10 height)
                    (BitVec.ofNat 160 address)).input
                    (bytes sibling ++ bytes actualRight), ?_⟩
                exact bottom_node_collision_contact table residual secretKey
                  labels labelsMatch bottomMatch sourceMatch height address
                  nodeHeight addressBound (bytes sibling ++ bytes actualRight)
                  collision
            · exact ih (2 * address + 1) childHeight rightBound inner childBad

end SigGolfCandidate.Hypertree.GroupedBalancedGraphBottomMerkleContact67
