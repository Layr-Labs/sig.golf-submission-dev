import SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedReference67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedLeaf67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedTree67. -/
section
/-! The functional grouped tree reads the planted public graph labels at its
canonical chain, leaf, and node queries. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedLeaf67
open SigGolf SigGolfCandidate.Hypertree Reference SecurityRandomOracle
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67 GroupedBalancedGraphReference67
open GroupedBalancedGraphProgrammedReference67 GroupedBalancedGraphProgramming67
set_option maxRecDepth 8192

private theorem walk_one {α : Type} (hash : Nat → α → α)
    (start : Nat) (value : α) : walk hash start 1 value = hash start value := rfl

theorem programmed_bottom_leaf (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (index : BitVec 160) :
    GroupedBottomTree.leafRoot (programmedGrouped residual secretKey labels)
      secretKey index.toNat = truncate (labels (bottomLeaf index)) := by
  rw [GroupedBottomTree.leafRoot, programmed_bottom_secret]
  change truncate (programmedGrouped residual secretKey labels
    (addressedInput 2 0 index.toNat 0 0 0
      (bytes (GroupedBottomTree.secret residual secretKey index.toNat)))) = _
  rw [← bottom_leaf_graph_input residual secretKey labels index]
  exact congrArg truncate
    (programmed_graph
      (payload (sourceAnswers residual secretKey) labels)
      labels residual (bottomLeaf index))

theorem programmed_upper_zero (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) :
    GroupedBalancedUpperTree67.chainHash (programmedGrouped residual secretKey labels)
      (base.val + 10) leaf.toNat chain 0
      (GroupedBalancedUpperTree67.secret (programmedGrouped residual secretKey labels)
        secretKey (base.val + 10) leaf.toNat chain) =
      truncate (labels (upperChain base leaf chain 0)) := by
  rw [programmed_upper_secret]
  change truncate (programmedGrouped residual secretKey labels
    (addressedInput 2 (base.val + 10) leaf.toNat 0 chain.val 0
      (bytes (GroupedBalancedUpperTree67.secret residual secretKey
        (base.val + 10) leaf.toNat chain)))) = _
  rw [← upper_chain_zero_graph_input residual secretKey labels base leaf chain]
  exact congrArg truncate
    (programmed_graph
      (payload (sourceAnswers residual secretKey) labels)
      labels residual (upperChain base leaf chain 0))

theorem programmed_upper_positive (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) (previous : Fin 9) :
    GroupedBalancedUpperTree67.chainHash (programmedGrouped residual secretKey labels)
      (base.val + 10) leaf.toNat chain (previous.val + 1)
      (truncate (labels (upperChain base leaf chain
        ⟨previous.val, by omega⟩))) =
      truncate (labels (upperChain base leaf chain
        ⟨previous.val + 1, by omega⟩)) := by
  change truncate (programmedGrouped residual secretKey labels
    (addressedInput 2 (base.val + 10) leaf.toNat 0 chain.val
      (previous.val + 1)
      (bytes (truncate (labels (upperChain base leaf chain
        ⟨previous.val, by omega⟩)))))) = _
  rw [← upper_chain_step_graph_input (sourceAnswers residual secretKey)
    labels base leaf chain previous]
  exact congrArg truncate
    (programmed_graph
      (payload (sourceAnswers residual secretKey) labels)
      labels residual
      (upperChain base leaf chain ⟨previous.val + 1, by omega⟩))

theorem programmed_upper_walk (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) (count : Nat)
    (bound : count < 10) :
    walk (GroupedBalancedUpperTree67.chainHash
      (programmedGrouped residual secretKey labels)
      (base.val + 10) leaf.toNat chain) 0 (count + 1)
      (GroupedBalancedUpperTree67.secret (programmedGrouped residual secretKey labels)
        secretKey (base.val + 10) leaf.toNat chain) =
      truncate (labels (upperChain base leaf chain ⟨count, by omega⟩)) := by
  induction count with
  | zero =>
      change GroupedBalancedUpperTree67.chainHash
        (programmedGrouped residual secretKey labels)
        (base.val + 10) leaf.toNat chain 0
        (GroupedBalancedUpperTree67.secret (programmedGrouped residual secretKey labels)
          secretKey (base.val + 10) leaf.toNat chain) = _
      exact programmed_upper_zero residual secretKey labels base leaf chain
  | succ count ih =>
      rw [walk_append _ 0 (count + 1) 1]
      rw [walk_one]
      simp only [Nat.zero_add]
      rw [ih (by omega)]
      exact programmed_upper_positive residual secretKey labels base leaf chain
        ⟨count, by omega⟩

theorem programmed_upper_endpoint (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) (chain : Fin 67) :
    GroupedBalancedUpperTree67.endpoint (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat chain =
      truncate (labels (upperChain base leaf chain (endpointStep chain))) := by
  have positive : 0 < GroupedBalancedUpperTree67.maxDigit chain :=
    GroupedBalancedSecurityGraph67.max_digit_positive chain
  have upper : GroupedBalancedUpperTree67.maxDigit chain ≤ 10 :=
    GroupedBalancedSecurityGraph67.max_digit_le_ten chain
  have bound : GroupedBalancedUpperTree67.maxDigit chain - 1 < 10 := by omega
  have walkEq := programmed_upper_walk residual secretKey labels base leaf
    chain (GroupedBalancedUpperTree67.maxDigit chain - 1) bound
  have countEq : GroupedBalancedUpperTree67.maxDigit chain - 1 + 1 =
      GroupedBalancedUpperTree67.maxDigit chain := by omega
  rw [countEq] at walkEq
  simpa only [GroupedBalancedUpperTree67.endpoint, endpointStep] using walkEq

theorem programmed_upper_leaf (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (leaf : BitVec 160) :
    GroupedBalancedUpperTree67.leafRoot (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat =
      truncate (labels (upperLeaf base leaf)) := by
  unfold GroupedBalancedUpperTree67.leafRoot
  have endpoints : GroupedBalancedUpperTree67.endpoint
      (programmedGrouped residual secretKey labels) secretKey
      (base.val + 10) leaf.toNat =
      fun chain => truncate (labels
        (upperChain base leaf chain (endpointStep chain))) := by
    funext chain
    exact programmed_upper_endpoint residual secretKey labels base leaf chain
  rw [endpoints]
  change truncate (programmedGrouped residual secretKey labels
    (addressedInput 3 (base.val + 10) leaf.toNat 0 0 0
      ((List.ofFn (fun chain : Fin 67 => truncate (labels
        (upperChain base leaf chain (endpointStep chain))))).flatMap bytes))) = _
  rw [← upper_leaf_graph_input (sourceAnswers residual secretKey) labels base leaf]
  exact congrArg truncate
    (programmed_graph
      (payload (sourceAnswers residual secretKey) labels)
      labels residual (upperLeaf base leaf))


end SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedLeaf67

end

/-! Planted-node and full-tree recovery for the direct 67-chain graph. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedTree67
open SigGolf SigGolfCandidate.Hypertree Reference SecurityRandomOracle
open GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67 GroupedBalancedGraphReference67
open GroupedBalancedGraphProgrammedReference67 GroupedBalancedGraphProgramming67
open GroupedBalancedGraphProgrammedLeaf67
set_option maxRecDepth 8192

theorem programmed_bottom_node (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (level : Fin 10)
    (tree : BitVec 160) :
    GroupedBottomTree.node (programmedGrouped residual secretKey labels)
      level.val tree.toNat
      (truncate (labels (nodeChildren (bottomNode level tree).val).1))
      (truncate (labels (nodeChildren (bottomNode level tree).val).2)) =
    truncate (labels (bottomNode level tree)) := by
  change truncate (programmedGrouped residual secretKey labels
    (addressedInput 4 level.val tree.toNat 0 0 0
      (bytes (truncate (labels (nodeChildren (bottomNode level tree).val).1)) ++
        bytes (truncate (labels (nodeChildren (bottomNode level tree).val).2))))) = _
  have inputEq :
      (bottomNode level tree).input
        (payload (sourceAnswers residual secretKey) labels (bottomNode level tree)) =
      addressedInput 4 level.val tree.toNat 0 0 0
        (bytes (truncate (labels (nodeChildren (bottomNode level tree).val).1)) ++
          bytes (truncate (labels (nodeChildren (bottomNode level tree).val).2))) := by
    rw [node_payload_of_tag_four (sourceAnswers residual secretKey) labels
      (bottomNode level tree) (by rfl)
      (by change level.val < 160; have := level.isLt; omega)]
    simp only [nodePayload, bottom_node_input]
  rw [← inputEq]
  exact congrArg truncate
    (programmed_graph
      (payload (sourceAnswers residual secretKey) labels)
      labels residual (bottomNode level tree))

theorem programmed_upper_node (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (level : Fin 150)
    (tree : BitVec 160) :
    GroupedBalancedUpperTree67.node (programmedGrouped residual secretKey labels)
      (level.val + 10) tree.toNat
      (truncate (labels (nodeChildren (upperNode level tree).val).1))
      (truncate (labels (nodeChildren (upperNode level tree).val).2)) =
    truncate (labels (upperNode level tree)) := by
  change truncate (programmedGrouped residual secretKey labels
    (addressedInput 4 (level.val + 10) tree.toNat 0 0 0
      (bytes (truncate (labels (nodeChildren (upperNode level tree).val).1)) ++
        bytes (truncate (labels (nodeChildren (upperNode level tree).val).2))))) = _
  have inputEq :
      (upperNode level tree).input
        (payload (sourceAnswers residual secretKey) labels (upperNode level tree)) =
      addressedInput 4 (level.val + 10) tree.toNat 0 0 0
        (bytes (truncate (labels (nodeChildren (upperNode level tree).val).1)) ++
          bytes (truncate (labels (nodeChildren (upperNode level tree).val).2))) := by
    rw [node_payload_of_tag_four (sourceAnswers residual secretKey) labels
      (upperNode level tree) (by rfl)
      (by change level.val + 10 < 160; have := level.isLt; omega)]
    simp only [nodePayload, upper_node_input]
  rw [← inputEq]
  exact congrArg truncate
    (programmed_graph
      (payload (sourceAnswers residual secretKey) labels)
      labels residual (upperNode level tree))

def upperRootPosition (base : Fin 150) : Nat → Nat → Position
  | 0, address => upperLeaf base (BitVec.ofNat 160 address)
  | height + 1, address =>
      upperNode (Fin.ofNat 150 (base.val + height)) (BitVec.ofNat 160 address)

theorem upperRootPosition_children (base : Fin 150) (height : Nat)
    (levelBound : base.val + height < 150)
    (aligned : GroupedBalancedGraphPayload67.groupBase (base.val + 10 + height) = base.val + 10)
    (tree : BitVec 160) :
    nodeChildren
      (upperNode (Fin.ofNat 150 (base.val + height)) tree).val =
      (upperRootPosition base height (2 * tree.toNat),
        upperRootPosition base height (2 * tree.toNat + 1)) := by
  cases height with
  | zero =>
      have same : Fin.ofNat 150 base.val = base := by
        apply Fin.ext
        simp [Fin.ofNat, Nat.mod_eq_of_lt base.isLt]
      simpa only [Nat.add_zero, same, upperRootPosition] using
        upper_node_at_base_children base tree (by simpa using aligned)
  | succ height =>
      let level : Fin 150 := Fin.ofNat 150 (base.val + (height + 1))
      have levelVal : level.val = base.val + (height + 1) := by
        simp [level, Fin.ofNat, Nat.mod_eq_of_lt levelBound]
      have positive : 0 < level.val := by omega
      have notBase : GroupedBalancedGraphPayload67.groupBase (level.val + 10) ≠ level.val + 10 := by
        rw [levelVal]
        rw [show base.val + (height + 1) + 10 =
          base.val + 10 + (height + 1) by omega, aligned]
        omega
      change nodeChildren (upperNode level tree).val = _
      rw [upper_node_inner_children level tree positive notBase]
      simp only [upperRootPosition]
      have previous : (⟨level.val - 1, by omega⟩ : Fin 150) =
          Fin.ofNat 150 (base.val + height) := by
        apply Fin.ext
        change level.val - 1 = (Fin.ofNat 150 (base.val + height)).val
        rw [levelVal]
        simp [Fin.ofNat,
          Nat.mod_eq_of_lt (show base.val + height < 150 by omega)]
      rw [previous]

theorem programmed_upper_root (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (base : Fin 150)
    (height address : Nat) (heightBound : height ≤ 4)
    (levelBound : base.val + height ≤ 150)
    (aligned : ∀ offset < height,
      GroupedBalancedGraphPayload67.groupBase (base.val + 10 + offset) = base.val + 10)
    (addressBound : address < 2 ^ (160 - height)) :
    GroupedBalancedUpperTree67.root (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) height address =
      truncate (labels (upperRootPosition base height address)) := by
  induction height generalizing address with
  | zero =>
      have addressFits : (BitVec.ofNat 160 address).toNat = address := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by simpa using addressBound)
      simpa only [GroupedBalancedUpperTree67.root, upperRootPosition, addressFits] using
        programmed_upper_leaf residual secretKey labels base
          (BitVec.ofNat 160 address)
  | succ height ih =>
      have childLevel : base.val + height ≤ 150 := by omega
      have childHeight : height ≤ 4 := by omega
      have childAligned : ∀ offset < height,
          GroupedBalancedGraphPayload67.groupBase (base.val + 10 + offset) = base.val + 10 := by
        intro offset bound
        exact aligned offset (by omega)
      have leftBound : 2 * address < 2 ^ (160 - height) := by
        have exponent : 160 - height = (160 - (height + 1)) + 1 := by omega
        rw [exponent, pow_succ]
        omega
      have rightBound : 2 * address + 1 < 2 ^ (160 - height) := by
        have exponent : 160 - height = (160 - (height + 1)) + 1 := by omega
        rw [exponent, pow_succ]
        omega
      have treeFits : (BitVec.ofNat 160 address).toNat = address := by
        rw [BitVec.toNat_ofNat]
        have wide : address < 2 ^ 160 := by
          have nonzero : 0 < 2 ^ (160 - (height + 1)) := pow_pos (by decide) _
          have powBound : 2 ^ (160 - (height + 1)) ≤ 2 ^ 160 :=
            pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 2)
              (Nat.sub_le 160 (height + 1))
          omega
        exact Nat.mod_eq_of_lt wide
      have levelFits : (Fin.ofNat 150 (base.val + height)).val =
          base.val + height := by
        simp [Fin.ofNat, Nat.mod_eq_of_lt
          (show base.val + height < 150 by omega)]
      have children := upperRootPosition_children base height
        (by omega : base.val + height < 150)
        (aligned height (by omega)) (BitVec.ofNat 160 address)
      rw [treeFits] at children
      have leftPosition :
          (nodeChildren
            (upperNode (Fin.ofNat 150 (base.val + height))
              (BitVec.ofNat 160 address)).val).1 =
          upperRootPosition base height (2 * address) :=
        congrArg Prod.fst children
      have rightPosition :
          (nodeChildren
            (upperNode (Fin.ofNat 150 (base.val + height))
              (BitVec.ofNat 160 address)).val).2 =
          upperRootPosition base height (2 * address + 1) :=
        congrArg Prod.snd children
      simp only [GroupedBalancedUpperTree67.root, upperRootPosition]
      rw [ih (2 * address) childHeight childLevel childAligned leftBound,
        ih (2 * address + 1) childHeight childLevel childAligned rightBound]
      rw [← leftPosition, ← rightPosition]
      have nodeEq := programmed_upper_node residual secretKey labels
        (Fin.ofNat 150 (base.val + height)) (BitVec.ofNat 160 address)
      rw [levelFits, treeFits] at nodeEq
      have levelSum : base.val + 10 + height = base.val + height + 10 := by omega
      rw [levelSum]
      exact nodeEq

theorem programmed_keygen (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) :
    GroupedBalancedScheme67.keygen (programmedGrouped residual secretKey labels)
      secretKey =
      truncate (labels (upperNode ⟨149, by decide⟩ 0)) := by
  have aligned : ∀ offset < 4,
      GroupedBalancedGraphPayload67.groupBase ((⟨146, by decide⟩ : Fin 150).val + 10 + offset) =
        (⟨146, by decide⟩ : Fin 150).val + 10 := by
    intro offset bound
    simpa only [show 100 + 4 * 14 = 156 by decide] using
      groupBase_high 14 offset (by decide) bound
  have result := programmed_upper_root residual secretKey labels
    (⟨146, by decide⟩ : Fin 150) 4 0
    (by decide) (by decide) aligned (by decide)
  simpa [GroupedBalancedScheme67.keygen, upperRootPosition] using result

def bottomRootPosition : Nat → Nat → Position
  | 0, address => bottomLeaf (BitVec.ofNat 160 address)
  | height + 1, address =>
      bottomNode (Fin.ofNat 10 height) (BitVec.ofNat 160 address)

theorem bottomRootPosition_children (height : Nat) (bound : height < 10)
    (tree : BitVec 160) :
    nodeChildren (bottomNode (Fin.ofNat 10 height) tree).val =
      (bottomRootPosition height (2 * tree.toNat),
        bottomRootPosition height (2 * tree.toNat + 1)) := by
  cases height with
  | zero =>
      have zeroEq : Fin.ofNat 10 0 = 0 := by decide
      rw [zeroEq]
      simpa only [bottomRootPosition] using bottom_node_zero_children tree
  | succ height =>
      let previous : Fin 9 := ⟨height, by omega⟩
      have current : Fin.ofNat 10 (height + 1) =
          (⟨previous.val + 1, by omega⟩ : Fin 10) := by
        apply Fin.ext
        simp [previous, Fin.ofNat,
          Nat.mod_eq_of_lt (show height + 1 < 10 by omega)]
      rw [current]
      rw [bottom_node_step_children previous tree]
      simp only [bottomRootPosition]
      have prior : (⟨previous.val, by omega⟩ : Fin 10) =
          Fin.ofNat 10 height := by
        apply Fin.ext
        simp [previous, Fin.ofNat,
          Nat.mod_eq_of_lt (show height < 10 by omega)]
      rw [prior]

theorem programmed_bottom_root (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (height address : Nat)
    (heightBound : height ≤ 10)
    (addressBound : address < 2 ^ (160 - height)) :
    GroupedBottomTree.root (programmedGrouped residual secretKey labels)
      secretKey height address =
      truncate (labels (bottomRootPosition height address)) := by
  induction height generalizing address with
  | zero =>
      have addressFits : (BitVec.ofNat 160 address).toNat = address := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by simpa using addressBound)
      simpa only [GroupedBottomTree.root, bottomRootPosition, addressFits] using
        programmed_bottom_leaf residual secretKey labels
          (BitVec.ofNat 160 address)
  | succ height ih =>
      have leftBound : 2 * address < 2 ^ (160 - height) := by
        have exponent : 160 - height = (160 - (height + 1)) + 1 := by omega
        rw [exponent, pow_succ]
        omega
      have rightBound : 2 * address + 1 < 2 ^ (160 - height) := by
        have exponent : 160 - height = (160 - (height + 1)) + 1 := by omega
        rw [exponent, pow_succ]
        omega
      have treeFits : (BitVec.ofNat 160 address).toNat = address := by
        rw [BitVec.toNat_ofNat]
        have wide : address < 2 ^ 160 := by
          have powBound : 2 ^ (160 - (height + 1)) ≤ 2 ^ 160 :=
            pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 2)
              (Nat.sub_le 160 (height + 1))
          omega
        exact Nat.mod_eq_of_lt wide
      have levelFits : (Fin.ofNat 10 height).val = height := by
        simp [Fin.ofNat, Nat.mod_eq_of_lt
          (show height < 10 by omega)]
      have children := bottomRootPosition_children height
        (by omega) (BitVec.ofNat 160 address)
      rw [treeFits] at children
      have leftPosition :
          (nodeChildren (bottomNode (Fin.ofNat 10 height)
            (BitVec.ofNat 160 address)).val).1 =
          bottomRootPosition height (2 * address) :=
        congrArg Prod.fst children
      have rightPosition :
          (nodeChildren (bottomNode (Fin.ofNat 10 height)
            (BitVec.ofNat 160 address)).val).2 =
          bottomRootPosition height (2 * address + 1) :=
        congrArg Prod.snd children
      simp only [GroupedBottomTree.root, bottomRootPosition]
      rw [ih (2 * address) (by omega) leftBound,
        ih (2 * address + 1) (by omega) rightBound]
      rw [← leftPosition, ← rightPosition]
      have nodeEq := programmed_bottom_node residual secretKey labels
        (Fin.ofNat 10 height) (BitVec.ofNat 160 address)
      rw [levelFits, treeFits] at nodeEq
      exact nodeEq

theorem programmed_bottom_sign_seed (residual : Hash) (secretKey : SecretKey)
    (labels : GroupedBalancedSecurityGraph67.Labels) (index : BitVec 160) :
    (GroupedBottomTree.build (programmedGrouped residual secretKey labels)
      secretKey 10 (GroupedMixedIndex.bottomTree index) index.toNat).witness.seedValue =
      GroupedBottomTree.secret residual secretKey index.toNat := by
  change (GroupedBottomTree.build (programmedGrouped residual secretKey labels)
      secretKey 10 (index.toNat / 2 ^ 10) index.toNat).witness.seedValue = _
  rw [GroupedBottomTree.build_seed_at_full_index]
  exact programmed_bottom_secret residual secretKey labels index

theorem programmed_upper_sign_fragment (residual : Hash)
    (secretKey : SecretKey) (labels : GroupedBalancedSecurityGraph67.Labels)
    (base : Fin 150) (leaf : BitVec 160) (message : Digest)
    (chain : Fin 67) :
    (GroupedBalancedUpperTree67.signValues (programmedGrouped residual secretKey labels)
      secretKey (base.val + 10) leaf.toNat message) chain =
      if zero : (GroupedBalancedUpperTree67.digit message chain).val = 0 then
        GroupedBalancedUpperTree67.secret residual secretKey
          (base.val + 10) leaf.toNat chain
      else
        truncate (labels (upperChain base leaf chain
          ⟨(GroupedBalancedUpperTree67.digit message chain).val - 1, by
            have := (GroupedBalancedUpperTree67.digit message chain).isLt
            omega⟩)) := by
  by_cases zero : (GroupedBalancedUpperTree67.digit message chain).val = 0
  · simp only [GroupedBalancedUpperTree67.signValues, zero, walk, dif_pos]
    exact programmed_upper_secret residual secretKey labels base leaf chain
  · have positive : 1 ≤ (GroupedBalancedUpperTree67.digit message chain).val := by omega
    have countBound : (GroupedBalancedUpperTree67.digit message chain).val - 1 < 10 := by
      have := (GroupedBalancedUpperTree67.digit message chain).isLt
      omega
    have fragment := programmed_upper_walk residual secretKey labels base leaf chain
      ((GroupedBalancedUpperTree67.digit message chain).val - 1) countBound
    have countEq : (GroupedBalancedUpperTree67.digit message chain).val - 1 + 1 =
        (GroupedBalancedUpperTree67.digit message chain).val := by omega
    rw [countEq] at fragment
    simpa only [GroupedBalancedUpperTree67.signValues, dif_neg zero] using fragment


end SigGolfCandidate.Hypertree.GroupedBalancedGraphProgrammedTree67
