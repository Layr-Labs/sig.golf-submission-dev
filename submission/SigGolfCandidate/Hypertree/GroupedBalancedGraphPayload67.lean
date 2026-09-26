import SigGolfCandidate.Hypertree.GroupedBalancedSecurityGraph67

/-!
Canonical dependency payloads for the grouped public graph. The bottom source
is indexed by the full 160-bit leaf; the upper source is indexed by a group
base, full leaf address, and one of 34 paired chain seeds. All public query
addresses are inherited from `GroupedBalancedSecurityGraph67.Position`.
-/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphPayload67
open SigGolf Reference GroupedBalancedSecurityGraph67

abbrev Address := SecurityGraph.Address

structure PrivateAnswers where
  bottom : BitVec 160 → BitVec 256
  upper : Fin 150 → BitVec 160 → Fin 34 → BitVec 256

def lowOrHigh (answer : BitVec 256) (chain : Fin 67) : Digest :=
  if chain.val % 2 = 0 then answer.extractLsb' 0 128
  else answer.extractLsb' 128 128

def chainSource (privateAnswers : PrivateAnswers) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) : Digest :=
  lowOrHigh (privateAnswers.upper base leaf
    ⟨chain.val / 2, by have := chain.isLt; omega⟩) chain

def chainPayload (privateAnswers : PrivateAnswers) (labels : Labels)
    (address : Address) : List Byte :=
  if hbottom : address.level.val = 0 ∧ address.leaf.val = 0 ∧
      address.chain.val = 0 ∧ address.step.val = 0 then
    bytes (truncate (privateAnswers.bottom (BitVec.ofNat 160 address.tree.toNat)))
  else if hlevel : 10 ≤ address.level.val ∧ address.level.val < 160 then
    if hleaf : address.leaf.val = 0 then
      if hchain : address.chain.val < 67 then
        if hstep : address.step.val < 10 then
          let base : Fin 150 := ⟨address.level.val - 10, by omega⟩
          let leaf : BitVec 160 := BitVec.ofNat 160 address.tree.toNat
          let chain : Fin 67 := ⟨address.chain.val, hchain⟩
          if zero : address.step.val = 0 then
            bytes (chainSource privateAnswers base leaf chain)
          else
            bytes (truncate (labels (upperChain base leaf chain
              ⟨address.step.val - 1, by omega⟩)))
        else []
      else []
    else []
  else []

def leafPayload (labels : Labels) (address : Address) : List Byte :=
  if hlevel : 10 ≤ address.level.val ∧ address.level.val < 160 then
    if hleaf : address.leaf.val = 0 ∧ address.chain.val = 0 ∧ address.step.val = 0 then
      let base : Fin 150 := ⟨address.level.val - 10, by omega⟩
      let leaf : BitVec 160 := BitVec.ofNat 160 address.tree.toNat
      (List.ofFn (fun chain : Fin 67 =>
        truncate (labels (upperChain base leaf chain (endpointStep chain))))).flatMap bytes
    else []
  else []

def groupBase (level : Nat) : Nat :=
  if level < 100 then 10 + 3 * ((level - 10) / 3)
  else 100 + 4 * ((level - 100) / 4)

theorem groupBase_low (group offset : Nat) (groupBound : group < 30)
    (offsetBound : offset < 3) :
    groupBase (10 + 3 * group + offset) = 10 + 3 * group := by
  have levelBound : 10 + 3 * group + offset < 100 := by omega
  simp only [groupBase, if_pos levelBound]
  omega

theorem groupBase_high (group offset : Nat) (groupBound : group < 15)
    (offsetBound : offset < 4) :
    groupBase (100 + 4 * group + offset) = 100 + 4 * group := by
  have levelBound : ¬100 + 4 * group + offset < 100 := by omega
  simp only [groupBase, if_neg levelBound]
  omega

def nodeChildren (address : Address) : Position × Position :=
  let left : BitVec 160 := BitVec.ofNat 160 (2 * address.tree.toNat)
  let right : BitVec 160 := BitVec.ofNat 160 (2 * address.tree.toNat + 1)
  if lower : address.level.val < 10 then
    if zero : address.level.val = 0 then
      (bottomLeaf left, bottomLeaf right)
    else
      let previous : Fin 10 := ⟨address.level.val - 1, by omega⟩
      (bottomNode previous left, bottomNode previous right)
  else if upper : address.level.val < 160 then
    let base := groupBase address.level.val
    if atBase : address.level.val = base then
      let group : Fin 150 := Fin.ofNat 150 (base - 10)
      (upperLeaf group left, upperLeaf group right)
    else
      let previous : Fin 150 := Fin.ofNat 150 (address.level.val - 11)
      (upperNode previous left, upperNode previous right)
  else
    (bottomLeaf left, bottomLeaf right)

def nodePayload (labels : Labels) (address : Address) : List Byte :=
  let children := nodeChildren address
  bytes (truncate (labels children.1)) ++ bytes (truncate (labels children.2))

def payload (privateAnswers : PrivateAnswers) (labels : Labels)
    (position : Position) : List Byte :=
  if position.val.tag.val = 2 then
    chainPayload privateAnswers labels position.val
  else if position.val.tag.val = 3 then
    leafPayload labels position.val
  else if position.val.level.val < 160 then
    nodePayload labels position.val
  else []

theorem node_payload_of_tag_four (privateAnswers : PrivateAnswers)
    (labels : Labels) (position : Position)
    (tagFour : position.val.tag.val = 4)
    (small : position.val.level.val < 160) :
    payload privateAnswers labels position = nodePayload labels position.val := by
  have notTwo : position.val.tag.val ≠ 2 := by omega
  have notThree : position.val.tag.val ≠ 3 := by omega
  simp only [payload, if_neg notTwo, if_neg notThree, if_pos small]

private theorem roundtrip160 (value : BitVec 160) :
    BitVec.ofNat 160 ((BitVec.ofNat 192 value.toNat).toNat) = value := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field value),
    Nat.mod_eq_of_lt value.isLt]

theorem bottom_leaf_payload (privateAnswers : PrivateAnswers) (labels : Labels)
    (index : BitVec 160) :
    payload privateAnswers labels (bottomLeaf index) =
      bytes (truncate (privateAnswers.bottom index)) := by
  simp [payload, chainPayload, bottomLeaf]
  have bound := GroupedBottomIndex.index_fits_tree_field index
  norm_num at bound
  rw [Nat.mod_eq_of_lt bound]
  simp

theorem upper_chain_zero_payload (privateAnswers : PrivateAnswers) (labels : Labels)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) :
    payload privateAnswers labels (upperChain base leaf chain 0) =
      bytes (chainSource privateAnswers base leaf chain) := by
  have bound := base.isLt
  have chainBound := chain.isLt
  simp [payload, chainPayload, upperChain,
    show 10 ≤ base.val + 10 by omega,
    show base.val + 10 < 160 by omega,
    show chain.val < 67 by omega]
  have boundLeaf := GroupedBottomIndex.index_fits_tree_field leaf
  norm_num at boundLeaf
  rw [Nat.mod_eq_of_lt boundLeaf]
  simp

theorem upper_chain_step_payload (privateAnswers : PrivateAnswers) (labels : Labels)
    (base : Fin 150) (leaf : BitVec 160) (chain : Fin 67) (step : Fin 9) :
    payload privateAnswers labels
      (upperChain base leaf chain ⟨step.val + 1, by omega⟩) =
      bytes (truncate (labels (upperChain base leaf chain ⟨step.val, by omega⟩))) := by
  have bound := base.isLt
  have chainBound := chain.isLt
  have stepBound := step.isLt
  simp [payload, chainPayload, upperChain,
    show 10 ≤ base.val + 10 by omega,
    show base.val + 10 < 160 by omega,
    show chain.val < 67 by omega,
    show step.val + 1 < 10 by omega]
  simp only [Nat.mod_eq_of_lt leaf.isLt]
  simp only [BitVec.ofNat_toNat]

theorem upper_leaf_payload (privateAnswers : PrivateAnswers) (labels : Labels)
    (base : Fin 150) (leaf : BitVec 160) :
    payload privateAnswers labels (upperLeaf base leaf) =
      (List.ofFn (fun chain : Fin 67 =>
        truncate (labels (upperChain base leaf chain (endpointStep chain))))).flatMap bytes := by
  have tagTwo : (upperLeaf base leaf).val.tag.val ≠ 2 := by
    change (3 : Nat) ≠ 2
    decide
  have tagThree : (upperLeaf base leaf).val.tag.val = 3 := rfl
  simp only [payload, if_neg tagTwo, if_pos tagThree]
  have goodLevel : 10 ≤ (upperLeaf base leaf).val.level.val ∧
      (upperLeaf base leaf).val.level.val < 160 := by
    change 10 ≤ base.val + 10 ∧ base.val + 10 < 160
    have := base.isLt
    omega
  have cleanFields : (upperLeaf base leaf).val.leaf.val = 0 ∧
      (upperLeaf base leaf).val.chain.val = 0 ∧
      (upperLeaf base leaf).val.step.val = 0 := by
    change (0 : Nat) = 0 ∧ (0 : Nat) = 0 ∧ (0 : Nat) = 0
    decide
  simp only [leafPayload, dif_pos goodLevel, dif_pos cleanFields]
  have baseEq :
      (⟨(upperLeaf base leaf).val.level.val - 10, by omega⟩ : Fin 150) = base := by
    apply Fin.ext
    change base.val + 10 - 10 = base.val
    omega
  have leafEq : BitVec.ofNat 160 (upperLeaf base leaf).val.tree.toNat = leaf := by
    exact roundtrip160 leaf
  simp only [baseEq, leafEq]

theorem bottom_node_zero_children (tree : BitVec 160) :
    nodeChildren (bottomNode 0 tree).val =
      (bottomLeaf (BitVec.ofNat 160 (2 * tree.toNat)),
        bottomLeaf (BitVec.ofNat 160 (2 * tree.toNat + 1))) := by
  simp [nodeChildren, bottomNode, GroupedBalancedSecurityGraph67.bottomNode]
  have bound := GroupedBottomIndex.index_fits_tree_field tree
  norm_num at bound
  simp [Nat.mod_eq_of_lt bound]

theorem bottom_node_step_children (level : Fin 9) (tree : BitVec 160) :
    nodeChildren (bottomNode ⟨level.val + 1, by omega⟩ tree).val =
      (bottomNode ⟨level.val, by omega⟩ (BitVec.ofNat 160 (2 * tree.toNat)),
        bottomNode ⟨level.val, by omega⟩ (BitVec.ofNat 160 (2 * tree.toNat + 1))) := by
  have h := level.isLt
  simp [nodeChildren, bottomNode, GroupedBalancedSecurityGraph67.bottomNode,
    show level.val + 1 < 10 by omega,
    BitVec.toNat_ofNat]
  have bound := GroupedBottomIndex.index_fits_tree_field tree
  norm_num at bound
  simp [Nat.mod_eq_of_lt bound]

theorem bottom_node_zero_payload (privateAnswers : PrivateAnswers)
    (labels : Labels) (tree : BitVec 160) :
    payload privateAnswers labels (bottomNode 0 tree) =
      bytes (truncate (labels (bottomLeaf (BitVec.ofNat 160 (2 * tree.toNat))))) ++
      bytes (truncate (labels (bottomLeaf (BitVec.ofNat 160 (2 * tree.toNat + 1))))) := by
  rw [node_payload_of_tag_four privateAnswers labels (bottomNode 0 tree)
    (by rfl) (by change (0 : Nat) < 160; decide)]
  simp only [nodePayload, bottom_node_zero_children]

theorem bottom_node_step_payload (privateAnswers : PrivateAnswers)
    (labels : Labels) (level : Fin 9) (tree : BitVec 160) :
    payload privateAnswers labels (bottomNode ⟨level.val + 1, by omega⟩ tree) =
      bytes (truncate (labels
        (bottomNode ⟨level.val, by omega⟩ (BitVec.ofNat 160 (2 * tree.toNat))))) ++
      bytes (truncate (labels
        (bottomNode ⟨level.val, by omega⟩ (BitVec.ofNat 160 (2 * tree.toNat + 1))))) := by
  rw [node_payload_of_tag_four privateAnswers labels
    (bottomNode ⟨level.val + 1, by omega⟩ tree)
    (by rfl) (by change level.val + 1 < 160; have := level.isLt; omega)]
  simp only [nodePayload, bottom_node_step_children]

theorem upper_node_at_base_children (level : Fin 150) (tree : BitVec 160)
    (atBase : groupBase (level.val + 10) = level.val + 10) :
    nodeChildren (upperNode level tree).val =
      (upperLeaf level (BitVec.ofNat 160 (2 * tree.toNat)),
        upperLeaf level (BitVec.ofNat 160 (2 * tree.toNat + 1))) := by
  have levelBound := level.isLt
  have positive : ¬ level.val + 10 < 10 := by omega
  have upper : level.val + 10 < 160 := by omega
  simp [nodeChildren, upperNode, positive, upper, atBase]
  have treeBound := GroupedBottomIndex.index_fits_tree_field tree
  norm_num at treeBound
  simp [Nat.mod_eq_of_lt treeBound]

theorem upper_node_at_base_payload (privateAnswers : PrivateAnswers)
    (labels : Labels) (level : Fin 150) (tree : BitVec 160)
    (atBase : groupBase (level.val + 10) = level.val + 10) :
    payload privateAnswers labels (upperNode level tree) =
      bytes (truncate (labels
        (upperLeaf level (BitVec.ofNat 160 (2 * tree.toNat))))) ++
      bytes (truncate (labels
        (upperLeaf level (BitVec.ofNat 160 (2 * tree.toNat + 1))))) := by
  rw [node_payload_of_tag_four privateAnswers labels (upperNode level tree)
    (by rfl) (by change level.val + 10 < 160; have := level.isLt; omega)]
  simp only [nodePayload, upper_node_at_base_children level tree atBase]

theorem upper_node_inner_children (level : Fin 150) (tree : BitVec 160)
    (positive : 0 < level.val)
    (notBase : groupBase (level.val + 10) ≠ level.val + 10) :
    nodeChildren (upperNode level tree).val =
      (upperNode ⟨level.val - 1, by omega⟩ (BitVec.ofNat 160 (2 * tree.toNat)),
        upperNode ⟨level.val - 1, by omega⟩ (BitVec.ofNat 160 (2 * tree.toNat + 1))) := by
  have levelBound := level.isLt
  have notLower : ¬ level.val + 10 < 10 := by omega
  have upper : level.val + 10 < 160 := by omega
  simp [nodeChildren, upperNode, notLower, upper]
  have treeBound := GroupedBottomIndex.index_fits_tree_field tree
  norm_num at treeBound
  have notAtBase : level.val + 10 ≠ groupBase (level.val + 10) := Ne.symm notBase
  have previousBound : level.val - 1 < 150 := by omega
  simp [notAtBase, Nat.mod_eq_of_lt treeBound,
    Nat.mod_eq_of_lt previousBound]

theorem upper_node_inner_payload (privateAnswers : PrivateAnswers)
    (labels : Labels) (level : Fin 150) (tree : BitVec 160)
    (positive : 0 < level.val)
    (notBase : groupBase (level.val + 10) ≠ level.val + 10) :
    payload privateAnswers labels (upperNode level tree) =
      bytes (truncate (labels
        (upperNode ⟨level.val - 1, by omega⟩ (BitVec.ofNat 160 (2 * tree.toNat))))) ++
      bytes (truncate (labels
        (upperNode ⟨level.val - 1, by omega⟩ (BitVec.ofNat 160 (2 * tree.toNat + 1))))) := by
  rw [node_payload_of_tag_four privateAnswers labels (upperNode level tree)
    (by rfl) (by change level.val + 10 < 160; have := level.isLt; omega)]
  simp only [nodePayload, upper_node_inner_children level tree positive notBase]

end SigGolfCandidate.Hypertree.GroupedBalancedGraphPayload67
