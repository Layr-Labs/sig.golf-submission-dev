import SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorPairedOracle67
import SigGolfCandidate.Hypertree.SecurityExtraction
import SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedTree67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCollisionBridge67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleExpected67. -/
section
/-! A concrete differing-payload 128-bit collision against one canonical graph
target is exactly the monitor's public output-contact event at that address. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCollisionBridge67
open SigGolf OracleComp OracleSpec Reference
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPassive67
open GroupedBalancedGraphMonitorPublicCoupling67
open SecurityExtraction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem collision_outputHit (table : PointTable) (hash : Hash)
    (position : Position) (tag level tree leaf chain step : Nat)
    (expected actual : List Byte)
    (address : ∀ payload,
      position.input payload = SecurityRandomOracle.addressedInput
        tag level tree leaf chain step payload)
    (expectedInput : position.input expected =
      GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position)
    (canonicalValue : hash (position.input expected) = table (.inl position))
    (collision : CollisionAt hash tag level tree leaf chain step
      expected actual) :
    outputHit table (position.input actual)
      (hash (position.input actual)) := by
  have different : position.input actual ≠
      GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
    intro same
    apply collision.1
    rw [← address actual, ← address expected]
    exact same.trans expectedInput.symm
  have sameValue : truncate (hash (position.input actual)) =
      truncate (table (.inl position)) := by
    have same := collision.2
    change truncate (hash (SecurityRandomOracle.addressedInput
      tag level tree leaf chain step actual)) =
      truncate (hash (SecurityRandomOracle.addressedInput
        tag level tree leaf chain step expected)) at same
    rw [← address actual, ← address expected, canonicalValue] at same
    exact same
  simp only [outputHit, GroupedBalancedGraphQuery67.locate_address]
  exact ⟨different, sameValue⟩

/-- A collision found by the concrete direct67 verifier becomes a public
monitor contact once its expected input is identified with the planted
reference graph. This requires only the 67 used source halves. -/
theorem programmed_collision_outputHit (table : PointTable)
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
        (GroupedBalancedGraphMonitorTable67.privateOf table) base leaf chain)
    (position : Position) (tag level tree leaf chain step : Nat)
    (expected actual : List Byte)
    (address : ∀ payload,
      position.input payload = SecurityRandomOracle.addressedInput
        tag level tree leaf chain step payload)
    (expectedSource : position.input expected =
      GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        labels position)
    (collision : CollisionAt
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      tag level tree leaf chain step expected actual) :
    outputHit table (position.input actual)
      ((GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels) (position.input actual)) := by
  subst labels
  have expectedInput : position.input expected =
      GroupedBalancedGraphCausality67.graphInput
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table) position := by
    rw [expectedSource]
    exact congrArg position.input
      (GroupedBalancedGraphMonitorPayloadExt67.payload_ext
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        (GroupedBalancedGraphMonitorTable67.privateOf table)
        (GroupedBalancedGraphMonitorTable67.labelsOf table)
        bottomMatch sourceMatch position)
  have canonicalValue :
      GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey (GroupedBalancedGraphMonitorTable67.labelsOf table)
        (position.input expected) = table (.inl position) := by
    have graphValue := GroupedBalancedGraphProgramming67.programmed_graph
      (GroupedBalancedGraphPayload67.payload
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        (GroupedBalancedGraphMonitorTable67.labelsOf table))
      (GroupedBalancedGraphMonitorTable67.labelsOf table) residual position
    change GroupedBalancedGraphProgrammedReference67.programmedGrouped
      residual secretKey (GroupedBalancedGraphMonitorTable67.labelsOf table)
        (GroupedBalancedGraphCausality67.graphInput
          (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
          (GroupedBalancedGraphMonitorTable67.labelsOf table) position) =
      table (.inl position) at graphValue
    rw [← expectedSource] at graphValue
    exact graphValue
  exact collision_outputHit table _ position tag level tree leaf chain step
    expected actual address expectedInput canonicalValue collision

theorem bottom_leaf_collision_outputHit (table : PointTable)
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
        (GroupedBalancedGraphMonitorTable67.privateOf table) base leaf chain)
    (index : BitVec 160) (actual : List Byte)
    (collision : CollisionAt
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      2 0 index.toNat 0 0 0
      (bytes (GroupedBottomTree.secret residual secretKey index.toNat)) actual) :
    outputHit table ((bottomLeaf index).input actual)
      ((GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels) ((bottomLeaf index).input actual)) := by
  apply programmed_collision_outputHit table residual secretKey labels
    labelsMatch bottomMatch sourceMatch (bottomLeaf index)
    2 0 index.toNat 0 0 0
    (bytes (GroupedBottomTree.secret residual secretKey index.toNat)) actual
  · intro payload
    exact bottom_leaf_input index payload
  · exact (bottom_leaf_input index _).trans
      (GroupedBalancedGraphReference67.bottom_leaf_graph_input
        residual secretKey labels index).symm
  · exact collision

theorem upper_zero_collision_outputHit (table : PointTable)
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
        (GroupedBalancedGraphMonitorTable67.privateOf table) base leaf chain)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67)
    (actual : List Byte)
    (collision : CollisionAt
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      2 (base.val + 10) leaf.toNat 0 chain.val 0
      (bytes (GroupedBalancedUpperTree67.secret residual secretKey
        (base.val + 10) leaf.toNat chain)) actual) :
    outputHit table ((upperChain base leaf chain 0).input actual)
      ((GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
        ((upperChain base leaf chain 0).input actual)) := by
  apply programmed_collision_outputHit table residual secretKey labels
    labelsMatch bottomMatch sourceMatch (upperChain base leaf chain 0)
    2 (base.val + 10) leaf.toNat 0 chain.val 0
    (bytes (GroupedBalancedUpperTree67.secret residual secretKey
      (base.val + 10) leaf.toNat chain)) actual
  · intro payload
    exact upper_chain_input base leaf chain 0 payload
  · exact (upper_chain_input base leaf chain 0 _).trans
      (GroupedBalancedGraphReference67.upper_chain_zero_graph_input
        residual secretKey labels base leaf chain).symm
  · exact collision

theorem upper_step_collision_outputHit (table : PointTable)
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
        (GroupedBalancedGraphMonitorTable67.privateOf table) base leaf chain)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67)
    (step : Fin 9) (actual : List Byte)
    (collision : CollisionAt
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      2 (base.val + 10) leaf.toNat 0 chain.val (step.val + 1)
      (bytes (truncate (labels
        (upperChain base leaf chain ⟨step.val, by omega⟩)))) actual) :
    outputHit table
      ((upperChain base leaf chain ⟨step.val + 1, by omega⟩).input actual)
      ((GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
        ((upperChain base leaf chain ⟨step.val + 1, by omega⟩).input actual)) := by
  apply programmed_collision_outputHit table residual secretKey labels
    labelsMatch bottomMatch sourceMatch
    (upperChain base leaf chain ⟨step.val + 1, by omega⟩)
    2 (base.val + 10) leaf.toNat 0 chain.val (step.val + 1)
    (bytes (truncate (labels
      (upperChain base leaf chain ⟨step.val, by omega⟩)))) actual
  · intro payload
    exact upper_chain_input base leaf chain ⟨step.val + 1, by omega⟩ payload
  · exact (upper_chain_input base leaf chain ⟨step.val + 1, by omega⟩ _).trans
      (GroupedBalancedGraphReference67.upper_chain_step_graph_input
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        labels base leaf chain step).symm
  · exact collision

theorem upper_leaf_collision_outputHit (table : PointTable)
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
        (GroupedBalancedGraphMonitorTable67.privateOf table) base leaf chain)
    (base : Fin 150) (leaf : BitVec 160) (actual : List Byte)
    (collision : CollisionAt
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      3 (base.val + 10) leaf.toNat 0 0 0
      ((List.ofFn (fun chain : Fin 67 =>
        truncate (labels (upperChain base leaf chain
          (endpointStep chain))))).flatMap bytes) actual) :
    outputHit table ((upperLeaf base leaf).input actual)
      ((GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels) ((upperLeaf base leaf).input actual)) := by
  apply programmed_collision_outputHit table residual secretKey labels
    labelsMatch bottomMatch sourceMatch (upperLeaf base leaf)
    3 (base.val + 10) leaf.toNat 0 0 0
    ((List.ofFn (fun chain : Fin 67 =>
      truncate (labels (upperChain base leaf chain
        (endpointStep chain))))).flatMap bytes) actual
  · intro payload
    exact upper_leaf_input base leaf payload
  · exact (upper_leaf_input base leaf _).trans
      (GroupedBalancedGraphReference67.upper_leaf_graph_input
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        labels base leaf).symm
  · exact collision

theorem node_collision_outputHit (table : PointTable)
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
        (GroupedBalancedGraphMonitorTable67.privateOf table) base leaf chain)
    (position : Position) (tagFour : position.val.tag.val = 4)
    (levelBound : position.val.level.val < 160)
    (actual : List Byte)
    (collision : CollisionAt
      (GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels)
      position.val.tag.val position.val.level.val position.val.tree.toNat
      position.val.leaf.val position.val.chain.val position.val.step.val
      (GroupedBalancedGraphPayload67.nodePayload labels position.val) actual) :
    outputHit table (position.input actual)
      ((GroupedBalancedGraphProgrammedReference67.programmedGrouped
        residual secretKey labels) (position.input actual)) := by
  apply programmed_collision_outputHit table residual secretKey labels
    labelsMatch bottomMatch sourceMatch position
    position.val.tag.val position.val.level.val position.val.tree.toNat
    position.val.leaf.val position.val.chain.val position.val.step.val
    (GroupedBalancedGraphPayload67.nodePayload labels position.val) actual
  · intro payload
    rfl
  · exact congrArg position.input
      (GroupedBalancedGraphPayload67.node_payload_of_tag_four
        (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        labels position tagFour levelBound).symm
  · exact collision

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMonitorCollisionBridge67

end

/-! Exact expected payload at a direct67 upper Merkle node, in terms of its
two canonical child roots. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleExpected67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67
open GroupedBalancedGraphPayload67
open GroupedBalancedGraphProgrammedReference67
open GroupedBalancedGraphProgrammedTree67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem upper_node_expected (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (base : Fin 150) (height address : Nat)
    (heightBound : height < 4)
    (levelBound : base.val + height < 150)
    (aligned : ∀ offset < height + 1,
      GroupedBalancedGraphPayload67.groupBase
        (base.val + 10 + offset) = base.val + 10)
    (addressBound : address < 2 ^ (160 - (height + 1))) :
    nodePayload labels
      (upperNode ⟨base.val + height, levelBound⟩
        (BitVec.ofNat 160 address)).val =
      bytes (GroupedBalancedUpperTree67.root
        (programmedGrouped residual secretKey labels)
        secretKey (base.val + 10) height (2 * address)) ++
      bytes (GroupedBalancedUpperTree67.root
        (programmedGrouped residual secretKey labels)
        secretKey (base.val + 10) height (2 * address + 1)) := by
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
  have children := upperRootPosition_children base height levelBound
    (aligned height (by omega)) (BitVec.ofNat 160 address)
  have nodeEq : upperNode ⟨base.val + height, levelBound⟩
      (BitVec.ofNat 160 address) =
      upperNode (Fin.ofNat 150 (base.val + height))
        (BitVec.ofNat 160 address) := by
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt levelBound]
  rw [nodeEq]
  rw [nodePayload, children, treeValue]
  rw [programmed_upper_root residual secretKey labels base height
      (2 * address) (by omega) (by omega)
      (fun offset bound => aligned offset (by omega)) childLeft]
  rw [programmed_upper_root residual secretKey labels base height
      (2 * address + 1) (by omega) (by omega)
      (fun offset bound => aligned offset (by omega)) childRight]

theorem upper_node_collision_contact (table : GroupedBalancedGraphPassive67.PointTable)
    (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels)
    (labelsMatch : labels = GroupedBalancedGraphMonitorTable67.labelsOf table)
    (bottomMatch : ∀ index,
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey).bottom index =
        (GroupedBalancedGraphMonitorTable67.privateOf table).bottom index)
    (sourceMatch : ∀ base leaf chain,
      chainSource (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
        base leaf chain =
      chainSource (GroupedBalancedGraphMonitorTable67.privateOf table)
        base leaf chain)
    (base : Fin 150) (height address : Nat)
    (heightBound : height < 4)
    (levelBound : base.val + height < 150)
    (aligned : ∀ offset < height + 1,
      GroupedBalancedGraphPayload67.groupBase
        (base.val + 10 + offset) = base.val + 10)
    (addressBound : address < 2 ^ (160 - (height + 1)))
    (actual : List Byte)
    (collision : SecurityExtraction.CollisionAt
      (programmedGrouped residual secretKey labels)
      4 (base.val + 10 + height) address 0 0 0
      (bytes (GroupedBalancedUpperTree67.root
        (programmedGrouped residual secretKey labels)
        secretKey (base.val + 10) height (2 * address)) ++
       bytes (GroupedBalancedUpperTree67.root
        (programmedGrouped residual secretKey labels)
        secretKey (base.val + 10) height (2 * address + 1))) actual) :
    GroupedBalancedGraphMonitorPublicCoupling67.outputHit table
      ((upperNode ⟨base.val + height, levelBound⟩
        (BitVec.ofNat 160 address)).input actual)
      ((programmedGrouped residual secretKey labels)
        ((upperNode ⟨base.val + height, levelBound⟩
          (BitVec.ofNat 160 address)).input actual)) := by
  let position := upperNode ⟨base.val + height, levelBound⟩
    (BitVec.ofNat 160 address)
  have expected := upper_node_expected residual secretKey labels base
    height address heightBound levelBound aligned addressBound
  apply GroupedBalancedGraphMonitorCollisionBridge67.programmed_collision_outputHit
    table residual secretKey labels labelsMatch bottomMatch sourceMatch
    position 4 (base.val + 10 + height) address 0 0 0
    (bytes (GroupedBalancedUpperTree67.root
      (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) height (2 * address)) ++
     bytes (GroupedBalancedUpperTree67.root
      (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) height (2 * address + 1))) actual
  · intro payload
    have treeValue : (BitVec.ofNat 160 address).toNat = address := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le addressBound
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simpa only [position, upper_node_input, treeValue,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · have nodeEq := node_payload_of_tag_four
      (GroupedBalancedGraphReference67.sourceAnswers residual secretKey)
      labels position (by rfl) (by change base.val + height + 10 < 160; omega)
    change position.input _ = position.input
      (payload (GroupedBalancedGraphReference67.sourceAnswers
        residual secretKey) labels position)
    exact congrArg position.input (expected.symm.trans nodeEq.symm)
  · exact collision

end SigGolfCandidate.Hypertree.GroupedBalancedGraphMerkleExpected67
