import SigGolfCandidate.Hypertree.GroupedSecurityGraph
import SigGolfCandidate.Hypertree.GroupedBalancedChecksum67

/-! Public graph coordinates for the 67-chain mixed-checksum construction.
The address type and random-oracle separation lemmas are shared with the
52-chain graph; only the chain/step bounds and upper group partition change. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSecurityGraph67
open SigGolf SigGolfCandidate.Hypertree Reference SecurityRandomOracle

abbrev Position := GroupedSecurityGraph.Position
abbrev Labels := GroupedSecurityGraph.Labels

def upperChain (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (step : Fin 10) : Position :=
  ⟨⟨2, ⟨base.val + 10, by omega⟩, BitVec.ofNat 192 leaf.toNat,
    0, ⟨chain.val, by omega⟩, ⟨step.val, by omega⟩⟩, Or.inl rfl⟩

def upperLeaf (base : Fin 150) (leaf : BitVec 160) : Position :=
  ⟨⟨3, ⟨base.val + 10, by omega⟩, BitVec.ofNat 192 leaf.toNat,
    0, 0, 0⟩, Or.inr (Or.inl rfl)⟩

def upperNode (level : Fin 150) (tree : BitVec 160) : Position :=
  ⟨⟨4, ⟨level.val + 10, by omega⟩, BitVec.ofNat 192 tree.toNat,
    0, 0, 0⟩, Or.inr (Or.inr rfl)⟩

def bottomLeaf (index : BitVec 160) : Position :=
  ⟨⟨2, 0, BitVec.ofNat 192 index.toNat, 0, 0, 0⟩, Or.inl rfl⟩

def bottomNode (level : Fin 10) (tree : BitVec 160) : Position :=
  ⟨⟨4, ⟨level.val, by omega⟩, BitVec.ofNat 192 tree.toNat,
    0, 0, 0⟩, Or.inr (Or.inr rfl)⟩

private theorem lift160_toNat (value : BitVec 160) :
    (BitVec.ofNat 192 value.toNat).toNat = value.toNat := by
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field value)]

theorem upper_chain_input (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (step : Fin 10) (payload : List Byte) :
    (upperChain base leaf chain step).input payload =
      addressedInput 2 (base.val + 10) leaf.toNat 0 chain.val step.val payload := by
  simp only [GroupedSecurityGraph.Position.input, upperChain, SecurityGraph.Address.input]
  rw [lift160_toNat]
  rfl

theorem bottom_leaf_input (index : BitVec 160) (payload : List Byte) :
    (bottomLeaf index).input payload =
      addressedInput 2 0 index.toNat 0 0 0 payload := by
  simp only [GroupedSecurityGraph.Position.input, bottomLeaf, SecurityGraph.Address.input]
  rw [lift160_toNat]
  rfl

theorem upper_leaf_input (base : Fin 150) (leaf : BitVec 160)
    (payload : List Byte) :
    (upperLeaf base leaf).input payload =
      addressedInput 3 (base.val + 10) leaf.toNat 0 0 0 payload := by
  simp only [GroupedSecurityGraph.Position.input, upperLeaf, SecurityGraph.Address.input]
  rw [lift160_toNat]
  rfl

theorem bottom_node_input (level : Fin 10) (tree : BitVec 160)
    (payload : List Byte) :
    (bottomNode level tree).input payload =
      addressedInput 4 level.val tree.toNat 0 0 0 payload := by
  simp only [GroupedSecurityGraph.Position.input, bottomNode, SecurityGraph.Address.input]
  rw [lift160_toNat]
  rfl

theorem upper_node_input (level : Fin 150) (tree : BitVec 160)
    (payload : List Byte) :
    (upperNode level tree).input payload =
      addressedInput 4 (level.val + 10) tree.toNat 0 0 0 payload := by
  simp only [GroupedSecurityGraph.Position.input, upperNode, SecurityGraph.Address.input]
  rw [lift160_toNat]
  rfl

theorem upper_chain_separated (first second : Position)
    (different : first ≠ second) (firstPayload secondPayload : List Byte) :
    first.input firstPayload ≠ second.input secondPayload :=
  GroupedSecurityGraph.Position.input_separated first second different _ _

theorem max_digit_positive (chain : Fin 67) :
    0 < GroupedBalancedChecksum67.maxDigit chain := by
  unfold GroupedBalancedChecksum67.maxDigit
  split_ifs <;> omega

theorem max_digit_le_ten (chain : Fin 67) :
    GroupedBalancedChecksum67.maxDigit chain ≤ 10 := by
  unfold GroupedBalancedChecksum67.maxDigit
  split_ifs <;> omega

def endpointStep (chain : Fin 67) : Fin 10 :=
  ⟨GroupedBalancedChecksum67.maxDigit chain - 1, by
    have low := max_digit_positive chain
    have high := max_digit_le_ten chain
    omega⟩

def groupBase (level : Nat) : Nat :=
  if level < 100 then 10 + 3 * ((level - 10) / 3)
  else 100 + 4 * ((level - 100) / 4)

theorem group_base_low (group offset : Nat) (groupBound : group < 30)
    (offsetBound : offset < 3) :
    groupBase (10 + 3 * group + offset) = 10 + 3 * group := by
  have levelBound : 10 + 3 * group + offset < 100 := by omega
  simp only [groupBase, if_pos levelBound]
  omega

theorem group_base_high (group offset : Nat) (groupBound : group < 15)
    (offsetBound : offset < 4) :
    groupBase (100 + 4 * group + offset) = 100 + 4 * group := by
  have levelBound : ¬100 + 4 * group + offset < 100 := by omega
  simp only [groupBase, if_neg levelBound]
  omega

end SigGolfCandidate.Hypertree.GroupedBalancedSecurityGraph67
