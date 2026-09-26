import SigGolfCandidate.Hypertree.GroupedBalancedGraphPayload67
import SigGolfCandidate.Hypertree.GroupedBalancedScheme67
import SigGolfCandidate.Hypertree.GroupedBalancedAddressDomains67

/-! Bridges from the grouped graph's private-answer tables to the actual
tree-addressed functional signer and public hash queries. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphReference67
open SigGolf Reference SecurityRandomOracle GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67

def sourceAnswers (hash : Hash) (secretKey : SecretKey) : PrivateAnswers where
  bottom := fun index => hash (GroupedBottomIndex.sourceInput secretKey index)
  upper := fun base leaf pair =>
    hash (GroupedBalancedAddressDomains67.upperInput secretKey
      ⟨base.val + 10, by have := base.isLt; omega⟩ leaf pair)

theorem bottom_source_value (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) :
    truncate ((sourceAnswers hash secretKey).bottom index) =
      GroupedBottomTree.secret hash secretKey index.toNat := by
  rfl

theorem upper_source_value (hash : Hash) (secretKey : SecretKey)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    chainSource (sourceAnswers hash secretKey) base leaf chain =
      GroupedBalancedUpperTree67.secret hash secretKey (base.val + 10) leaf.toNat chain := by
  rfl

theorem bottom_leaf_graph_input (hash : Hash) (secretKey : SecretKey)
    (labels : Labels) (index : BitVec 160) :
    (bottomLeaf index).input
      (payload (sourceAnswers hash secretKey) labels (bottomLeaf index)) =
    addressedInput 2 0 index.toNat 0 0 0
      (bytes (GroupedBottomTree.secret hash secretKey index.toNat)) := by
  rw [bottom_leaf_payload, bottom_leaf_input, bottom_source_value]

theorem upper_chain_zero_graph_input (hash : Hash) (secretKey : SecretKey)
    (labels : Labels) (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) :
    (upperChain base leaf chain 0).input
      (payload (sourceAnswers hash secretKey) labels (upperChain base leaf chain 0)) =
    addressedInput 2 (base.val + 10) leaf.toNat 0 chain.val 0
      (bytes (GroupedBalancedUpperTree67.secret hash secretKey (base.val + 10) leaf.toNat chain)) := by
  rw [upper_chain_zero_payload, upper_chain_input, upper_source_value]
  rfl

theorem upper_chain_step_graph_input (privateAnswers : PrivateAnswers)
    (labels : Labels) (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (step : Fin 9) :
    (upperChain base leaf chain ⟨step.val + 1, by omega⟩).input
      (payload privateAnswers labels
        (upperChain base leaf chain ⟨step.val + 1, by omega⟩)) =
    addressedInput 2 (base.val + 10) leaf.toNat 0 chain.val (step.val + 1)
      (bytes (truncate (labels
        (upperChain base leaf chain ⟨step.val, by omega⟩)))) := by
  rw [upper_chain_step_payload, upper_chain_input]

theorem upper_leaf_graph_input (privateAnswers : PrivateAnswers)
    (labels : Labels) (base : Fin 150) (leaf : BitVec 160) :
    (upperLeaf base leaf).input (payload privateAnswers labels (upperLeaf base leaf)) =
    addressedInput 3 (base.val + 10) leaf.toNat 0 0 0
      ((List.ofFn (fun chain : Fin 67 =>
        truncate (labels (upperChain base leaf chain (endpointStep chain))))).flatMap bytes) := by
  rw [upper_leaf_payload, upper_leaf_input]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphReference67
