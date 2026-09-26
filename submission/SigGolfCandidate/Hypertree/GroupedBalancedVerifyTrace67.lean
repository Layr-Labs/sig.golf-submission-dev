import SigGolfCandidate.Hypertree.GroupedBalancedVerifyOracle67
import SigGolfCandidate.Hypertree.SecurityVerifyTrace
import SigGolfCandidate.Hypertree.GroupedBalancedUpperIndex67

/-! Exact deterministic hash-input trace for the grouped direct67 verifier.
These membership lemmas attach extractor contacts to queries actually made by
the final verifier, including cached and repeated oracle reads. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTrace67
open SigGolf SigGolfCandidate.Hypertree Reference OracleComp OracleSpec
open GroupedBalancedVerifyOracle67
open SecurityVerifyTrace
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

@[simp] theorem queries_bottomLeaf (hash : Hash) (address : Nat)
    (seed : Reference.Digest) :
    queries hash (bottomLeaf address seed) =
      [SecurityRandomOracle.addressedInput 2 0 address 0 0 0
        (bytes seed)] := by
  simp only [GroupedBalancedVerifyOracle67.bottomLeaf,
    SecurityVerifyTrace.queries_map, SecurityVerifyTrace.queries_ask]

@[simp] theorem queries_node (hash : Hash) (level address : Nat)
    (left right : Reference.Digest) :
    queries hash (node level address left right) =
      [SecurityRandomOracle.addressedInput 4 level address 0 0 0
        (bytes left ++ bytes right)] := by
  simp only [GroupedBalancedVerifyOracle67.node,
    SecurityVerifyTrace.queries_map, SecurityVerifyTrace.queries_ask]

@[simp] theorem queries_chainHash (hash : Hash) (base leaf : Nat)
    (chain : Fin 67) (step : Nat) (value : Reference.Digest) :
    queries hash (chainHash base leaf chain step value) =
      [SecurityRandomOracle.addressedInput 2 base leaf 0 chain.val step
        (bytes value)] := by
  simp only [GroupedBalancedVerifyOracle67.chainHash,
    SecurityVerifyTrace.queries_map, SecurityVerifyTrace.queries_ask]

@[simp] theorem queries_compressLeaf (hash : Hash) (base leaf : Nat)
    (values : Fin 67 → Reference.Digest) :
    queries hash (compressLeaf base leaf values) =
      [SecurityRandomOracle.addressedInput 3 base leaf 0 0 0
        ((List.ofFn values).flatMap bytes)] := by
  simp only [GroupedBalancedVerifyOracle67.compressLeaf,
    SecurityVerifyTrace.queries_map, SecurityVerifyTrace.queries_ask]

theorem mem_walk (hash : Hash) (base leaf : Nat) (chain : Fin 67)
    (start count offset : Nat) (value : Reference.Digest)
    (within : offset < count) :
    SecurityRandomOracle.addressedInput 2 base leaf 0 chain.val
      (start + offset)
      (bytes (Hypertree.walk
        (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
        start offset value)) ∈
      queries hash (SecurityReference.walk
        (GroupedBalancedVerifyOracle67.chainHash base leaf chain)
        start count value) := by
  induction count generalizing start offset value with
  | zero => omega
  | succ count ih =>
      simp only [SecurityReference.walk, queries_bind,
        queries_chainHash, eval_chainHash,
        List.mem_append, List.mem_singleton]
      cases offset with
      | zero => exact Or.inl (by simp [Hypertree.walk])
      | succ offset =>
          right
          simpa only [Hypertree.walk, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) offset
              (GroupedBalancedUpperTree67.chainHash hash base leaf chain
                start value) (by omega)

theorem mem_recoverLeaf_chain (hash : Hash) (base leaf : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) (chain : Fin 67)
    (offset : Nat)
    (within : offset < GroupedBalancedUpperTree67.maxDigit chain -
      (GroupedBalancedUpperTree67.digit message chain).val) :
    SecurityRandomOracle.addressedInput 2 base leaf 0 chain.val
      ((GroupedBalancedUpperTree67.digit message chain).val + offset)
      (bytes (Hypertree.walk
        (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
        (GroupedBalancedUpperTree67.digit message chain).val offset
        (values chain))) ∈
      queries hash (recoverLeaf base leaf message values) := by
  simp only [GroupedBalancedVerifyOracle67.recoverLeaf,
    queries_bind, List.mem_append]
  exact Or.inl
    (SecurityVerifyTrace.mem_sequenceFin hash 67 _ chain _
      (mem_walk hash base leaf chain _ _ offset _ within))

theorem mem_recoverLeaf_compress (hash : Hash) (base leaf : Nat)
    (message : Reference.Digest)
    (values : Fin 67 → Reference.Digest) :
    SecurityRandomOracle.addressedInput 3 base leaf 0 0 0
      ((List.ofFn fun chain : Fin 67 =>
        Hypertree.walk
          (GroupedBalancedUpperTree67.chainHash hash base leaf chain)
          (GroupedBalancedUpperTree67.digit message chain).val
          (GroupedBalancedUpperTree67.maxDigit chain -
            (GroupedBalancedUpperTree67.digit message chain).val)
          (values chain)).flatMap bytes) ∈
      queries hash (recoverLeaf base leaf message values) := by
  simp only [GroupedBalancedVerifyOracle67.recoverLeaf,
    queries_bind, SecurityReference.eval_sequenceFin,
    SecurityReference.eval_walk, eval_chainHash,
    queries_compressLeaf, List.mem_append, List.mem_singleton,
    or_true]

theorem mem_recoverBottom_inner (hash : Hash) (height address index : Nat)
    (inner : GroupedBottomTree.Witness height)
    (sibling : Reference.Digest) (query : Query)
    (member : query ∈ queries hash
      (recoverBottom height
        (if index / 2 ^ height % 2 = 0 then 2 * address
          else 2 * address + 1) index inner)) :
    query ∈ queries hash
      (recoverBottom (height + 1) address index (.step inner sibling)) := by
  by_cases bit : index / 2 ^ height % 2 = 0
  · simp only [recoverBottom, if_pos bit, queries_bind, List.mem_append]
    exact Or.inl (by simpa only [if_pos bit] using member)
  · simp only [recoverBottom, if_neg bit, queries_bind, List.mem_append]
    exact Or.inl (by simpa only [if_neg bit] using member)

theorem mem_recoverUpper_inner (hash : Hash) (base height address index : Nat)
    (message : Reference.Digest)
    (inner : GroupedBalancedUpperTree67.Witness height)
    (sibling : Reference.Digest) (query : Query)
    (member : query ∈ queries hash
      (recoverUpper base height
        (if index / 2 ^ height % 2 = 0 then 2 * address
          else 2 * address + 1) index message inner)) :
    query ∈ queries hash
      (recoverUpper base (height + 1) address index message
        (.step inner sibling)) := by
  by_cases bit : index / 2 ^ height % 2 = 0
  · simp only [recoverUpper, if_pos bit, queries_bind, List.mem_append]
    exact Or.inl (by simpa only [if_pos bit] using member)
  · simp only [recoverUpper, if_neg bit, queries_bind, List.mem_append]
    exact Or.inl (by simpa only [if_neg bit] using member)

theorem mem_recoverBottom_leaf (hash : Hash)
    (height address index : Nat)
    (witness : GroupedBottomTree.Witness height) :
    SecurityRandomOracle.addressedInput 2 0
      (GroupedBottomTree.selectedLeafAddress height address index) 0 0 0
      (bytes witness.seedValue) ∈
        queries hash (recoverBottom height address index witness) := by
  induction witness generalizing address with
  | seed seed =>
      simp only [GroupedBottomTree.selectedLeafAddress,
        GroupedBottomTree.Witness.seedValue, recoverBottom,
        queries_bottomLeaf]
      exact List.mem_singleton_self _
  | @step height inner sibling ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [GroupedBottomTree.selectedLeafAddress, if_pos bit,
          GroupedBottomTree.Witness.seedValue]
        apply mem_recoverBottom_inner hash height address index inner sibling
        simpa only [if_pos bit] using ih (2 * address)
      · simp only [GroupedBottomTree.selectedLeafAddress, if_neg bit,
          GroupedBottomTree.Witness.seedValue]
        apply mem_recoverBottom_inner hash height address index inner sibling
        simpa only [if_neg bit] using ih (2 * address + 1)

theorem mem_recoverUpper_leaf (hash : Hash) (base height address index : Nat)
    (message : Reference.Digest)
    (witness : GroupedBalancedUpperTree67.Witness height)
    (query : Query)
    (member : query ∈ queries hash
      (recoverLeaf base
        (GroupedBottomTree.selectedLeafAddress height address index)
        message (GroupedBalancedUpperIndex67.witnessValues witness))) :
    query ∈ queries hash
      (recoverUpper base height address index message witness) := by
  induction witness generalizing address with
  | leaf values => exact member
  | @step height inner sibling ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [GroupedBottomTree.selectedLeafAddress, if_pos bit,
          GroupedBalancedUpperIndex67.witnessValues] at member
        apply mem_recoverUpper_inner hash base height address index
          message inner sibling query
        simpa only [if_pos bit] using ih (2 * address) member
      · simp only [GroupedBottomTree.selectedLeafAddress, if_neg bit,
          GroupedBalancedUpperIndex67.witnessValues] at member
        apply mem_recoverUpper_inner hash base height address index
          message inner sibling query
        simpa only [if_neg bit] using ih (2 * address + 1) member

theorem mem_recoverBottom_node (hash : Hash)
    (height address index : Nat)
    (inner : GroupedBottomTree.Witness height)
    (sibling : Reference.Digest) :
    let child := if index / 2 ^ height % 2 = 0 then 2 * address
      else 2 * address + 1
    let current := GroupedBottomTree.recover hash height child index inner
    SecurityRandomOracle.addressedInput 4 height address 0 0 0
      (if index / 2 ^ height % 2 = 0 then
        bytes current ++ bytes sibling
      else bytes sibling ++ bytes current) ∈
      queries hash (recoverBottom (height + 1) address index
        (.step inner sibling)) := by
  by_cases bit : index / 2 ^ height % 2 = 0
  · simp only [recoverBottom, if_pos bit, queries_bind,
      eval_recoverBottom, queries_node,
      List.mem_append, List.mem_singleton]
    exact Or.inr trivial
  · simp only [recoverBottom, if_neg bit, queries_bind,
      eval_recoverBottom, queries_node,
      List.mem_append, List.mem_singleton]
    exact Or.inr trivial

theorem mem_recoverUpper_node (hash : Hash) (base height address index : Nat)
    (message : Reference.Digest)
    (inner : GroupedBalancedUpperTree67.Witness height)
    (sibling : Reference.Digest) :
    let child := if index / 2 ^ height % 2 = 0 then 2 * address
      else 2 * address + 1
    let current := GroupedBalancedUpperTree67.recover hash base height
      child index message inner
    SecurityRandomOracle.addressedInput 4 (base + height) address 0 0 0
      (if index / 2 ^ height % 2 = 0 then
        bytes current ++ bytes sibling
      else bytes sibling ++ bytes current) ∈
      queries hash (recoverUpper base (height + 1) address index message
        (.step inner sibling)) := by
  by_cases bit : index / 2 ^ height % 2 = 0
  · simp only [recoverUpper, if_pos bit, queries_bind,
      eval_recoverUpper, queries_node,
      List.mem_append, List.mem_singleton]
    exact Or.inr trivial
  · simp only [recoverUpper, if_neg bit, queries_bind,
      eval_recoverUpper, queries_node,
      List.mem_append, List.mem_singleton]
    exact Or.inr trivial

theorem mem_recoverLayers_head (hash : Hash)
    (height : Nat) (rest : List Nat) (base index : Nat)
    (message : Reference.Digest)
    (head : GroupedBalancedUpperTree67.Witness height)
    (tail : GroupedBalancedScheme67.UpperWitnesses rest)
    (query : Query)
    (member : query ∈ queries hash
      (recoverUpper base height (index / 2 ^ height)
        index message head)) :
    query ∈ queries hash
      (recoverLayers (height :: rest) base index message
        (.cons head tail)) := by
  simp only [GroupedBalancedVerifyOracle67.recoverLayers,
    queries_bind, List.mem_append]
  exact Or.inl member

theorem mem_recoverLayers_tail (hash : Hash)
    (height : Nat) (rest : List Nat) (base index : Nat)
    (message : Reference.Digest)
    (head : GroupedBalancedUpperTree67.Witness height)
    (tail : GroupedBalancedScheme67.UpperWitnesses rest)
    (query : Query)
    (member : query ∈ queries hash
      (recoverLayers rest (base + height) (index / 2 ^ height)
        (GroupedBalancedUpperTree67.recover hash base height
          (index / 2 ^ height) index message head) tail)) :
    query ∈ queries hash
      (recoverLayers (height :: rest) base index message
        (.cons head tail)) := by
  simp only [GroupedBalancedVerifyOracle67.recoverLayers,
    queries_bind, eval_recoverUpper,
    List.mem_append]
  exact Or.inr member

theorem queries_verify (hash : Hash) (pk : PublicKey)
    (message : Message) (signature : GroupedBalancedScheme67.Signature) :
    let index := Reference.indexOf hash message signature.randomizer
    let bottomTree := GroupedMixedIndex.bottomTree index
    let bottom := GroupedBottomTree.recover hash 10 bottomTree index.toNat
      signature.bottom
    queries hash (GroupedBalancedVerifyOracle67.verify pk message signature) =
      SecurityRandomOracle.indexInput message signature.randomizer ::
        (queries hash
          (recoverBottom 10 bottomTree index.toNat signature.bottom) ++
        queries hash
          (recoverLayers GroupedBalancedScheme67.Heights 10 bottomTree
            bottom signature.upper)) := by
  simp only [GroupedBalancedVerifyOracle67.verify, queries_bind, SecurityVerifyTrace.queries_ask,
    SecurityReference.eval_ask, eval_recoverBottom,
    SecurityVerifyTrace.queries_pure, List.append_nil]
  rfl

theorem mem_verify_index (hash : Hash) (pk : PublicKey)
    (message : Message) (signature : GroupedBalancedScheme67.Signature) :
    SecurityRandomOracle.indexInput message signature.randomizer ∈
      queries hash (GroupedBalancedVerifyOracle67.verify pk message signature) := by
  rw [queries_verify]
  exact List.mem_cons_self

theorem mem_verify_bottom (hash : Hash) (pk : PublicKey)
    (message : Message) (signature : GroupedBalancedScheme67.Signature)
    (query : Query)
    (member : query ∈ queries hash
      (recoverBottom 10
        (GroupedMixedIndex.bottomTree
          (Reference.indexOf hash message signature.randomizer))
        (Reference.indexOf hash message signature.randomizer).toNat
        signature.bottom)) :
    query ∈ queries hash (GroupedBalancedVerifyOracle67.verify pk message signature) := by
  rw [queries_verify]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ member)

theorem mem_verify_upper (hash : Hash) (pk : PublicKey)
    (message : Message) (signature : GroupedBalancedScheme67.Signature)
    (query : Query)
    (member : query ∈ queries hash
      (recoverLayers GroupedBalancedScheme67.Heights 10
        (GroupedMixedIndex.bottomTree
          (Reference.indexOf hash message signature.randomizer))
        (GroupedBottomTree.recover hash 10
          (GroupedMixedIndex.bottomTree
            (Reference.indexOf hash message signature.randomizer))
          (Reference.indexOf hash message signature.randomizer).toNat
          signature.bottom)
        signature.upper)) :
    query ∈ queries hash (GroupedBalancedVerifyOracle67.verify pk message signature) := by
  rw [queries_verify]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ member)

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTrace67
