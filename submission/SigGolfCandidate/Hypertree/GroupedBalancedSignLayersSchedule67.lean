import SigGolfCandidate.Hypertree.GroupedBalancedSignWireUpperFields67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperOuterInvariant67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperAllSelected67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedBoundary67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignLayersFields67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignLayersSchedule67. -/
section
/-! Project selected fields from the functional upper signing recursion. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignLayersFields67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedScheme67 GroupedBalancedSignWireUpperFields67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def afterPrefix (hash : Hash) (secretKey : SecretKey) :
    List Nat → Nat × Nat × Digest → Nat × Nat × Digest
  | [], state => state
  | height :: rest, (base,index,message) =>
      afterPrefix hash secretKey rest
        (base+height,index/2^height,
          GroupedBalancedUpperTree67.root hash secretKey base height
            (index/2^height))

theorem signLayers_leaf (hash : Hash) (secretKey : SecretKey)
    (heights : List Nat) (base index : Nat) (message : Digest)
    (k : Nat) (hk : k < heights.length)
    (chain : GroupedBalancedUpperTree67.ChainMixed) :
    GroupedBalancedSignWireUpperFields67.leafAt
      (GroupedBalancedScheme67.signLayers hash secretKey heights base index message) k chain =
      let state := afterPrefix hash secretKey (heights.take k)
        (base,index,message)
      GroupedBalancedUpperTree67.signValues hash secretKey
        state.1 state.2.1 state.2.2 chain := by
  induction heights generalizing base index message k with
  | nil => simp at hk
  | cons height rest ih =>
      cases k with
      | zero =>
          simpa only [GroupedBalancedScheme67.signLayers,
            GroupedBalancedSignWireUpperFields67.leafAt,
            List.take_zero, afterPrefix] using
            (GroupedBalancedUpperBuildSibling67.build_leaf hash secretKey
              base height index message chain)
      | succ k =>
          have low : k < rest.length := by simpa using hk
          have step := ih (base+height) (index/2^height)
            (GroupedBalancedUpperTree67.build hash secretKey base height
              (index/2^height) index message).root k low
          simpa only [GroupedBalancedScheme67.signLayers,
            GroupedBalancedSignWireUpperFields67.leafAt, List.take_succ_cons,
            afterPrefix, GroupedBalancedUpperTree67.build_root] using step

theorem signLayers_sibling (hash : Hash) (secretKey : SecretKey)
    (heights : List Nat) (base index : Nat) (message : Digest)
    (k level : Nat) (hk : k < heights.length)
    (lt : level < heights[k]'hk) :
    GroupedBalancedSignWireUpperFields67.siblingAt
      (GroupedBalancedScheme67.signLayers hash secretKey heights base index message) k level =
      let state := afterPrefix hash secretKey (heights.take k)
        (base,index,message)
      GroupedBalancedUpperTree67.root hash secretKey state.1 level
        (if state.2.1/2^level%2=0 then state.2.1/2^level+1
          else state.2.1/2^level-1) := by
  induction heights generalizing base index message k with
  | nil => simp at hk
  | cons height rest ih =>
      cases k with
      | zero =>
          simpa only [GroupedBalancedScheme67.signLayers,
            GroupedBalancedSignWireUpperFields67.siblingAt,
            List.take_zero, afterPrefix,
            List.getElem_cons_zero] using
            (GroupedBalancedUpperBuildSibling67.build_sibling hash secretKey
              base height index level message lt)
      | succ k =>
          have low : k < rest.length := by simpa using hk
          have step := ih (base+height) (index/2^height)
            (GroupedBalancedUpperTree67.build hash secretKey base height
              (index/2^height) index message).root k low lt
          simpa only [GroupedBalancedScheme67.signLayers,
            GroupedBalancedSignWireUpperFields67.siblingAt, List.take_succ_cons,
            afterPrefix, GroupedBalancedUpperTree67.build_root,
            List.getElem_cons_succ] using step

#print axioms signLayers_leaf
#print axioms signLayers_sibling
end SigGolfCandidate.Hypertree.GroupedBalancedSignLayersFields67

end

/-! Connect functional upper-layer recursion to the machine's fixed 45-group schedule. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignLayersSchedule67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedScheme67 GroupedBalancedSignLayersFields67
open GroupedBalancedSignUpperSchedule67
open GroupedBalancedSignUpperOuterInvariant67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem afterPrefix_append (hash : Hash) (secretKey : SecretKey)
    (first second : List Nat) (state : Nat × Nat × Digest) :
    afterPrefix hash secretKey (first ++ second) state =
      afterPrefix hash secretKey second (afterPrefix hash secretKey first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons h tail ih =>
      simp only [List.cons_append, afterPrefix]
      exact ih _

theorem fixed_height_get (k : Nat) (hk : k < Heights.length) :
    Heights[k]'hk = height k := by
  have bound : k<45 := by simpa [heights_length] using hk
  have h := GroupedBalancedSignWireUpperFields67.fixed_heights k bound
  simpa only [List.getElem?_eq_getElem hk, Option.some.injEq] using h

theorem fixed_state (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (message : Digest)
    (k : Nat) (hk : k ≤ 45) :
    afterPrefix hash secretKey (Heights.take k)
      (10,initialIndex.toNat,message) =
      (treeBase k, (indexAt initialIndex k).toNat,
        GroupedBalancedSignUpperAllSelected67.messageAfter hash secretKey
          initialIndex 0 message k) := by
  induction k with
  | zero =>
      simp [afterPrefix,treeBase,indexAt,prefixHeight,
        GroupedBalancedSignUpperAllSelected67.messageAfter]
  | succ k ih =>
      have hkl : k<Heights.length := by rw [heights_length]; omega
      have h45 : k<45 := by omega
      have next := List.take_succ_eq_append_getElem hkl
      rw [next, afterPrefix_append, ih (by omega)]
      rw [fixed_height_get k hkl]
      simp only [afterPrefix]
      have base := treeBase_next k
      have idxNat := congrArg BitVec.toNat (index_next initialIndex k)
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at idxNat
      rw [base, ←idxNat]
      simp only [GroupedBalancedSignUpperAllSelected67.messageAfter,
        Nat.zero_add, groupRoot]
      rw [←idxNat]

theorem leaf_scheduled (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (message : Digest)
    (k : Nat) (hk : k<45)
    (chain : GroupedBalancedUpperTree67.ChainMixed) :
    GroupedBalancedSignWireUpperFields67.leafAt
      (signLayers hash secretKey Heights 10 initialIndex.toNat message) k chain =
      GroupedBalancedUpperTree67.signValues hash secretKey
        (treeBase k) (indexAt initialIndex k).toNat
        (GroupedBalancedSignUpperAllSelected67.messageAfter hash secretKey
          initialIndex 0 message k) chain := by
  have hkl : k<Heights.length := by rw [heights_length]; omega
  have source := signLayers_leaf hash secretKey Heights 10
    initialIndex.toNat message k hkl chain
  rw [fixed_state hash secretKey initialIndex message k (by omega)] at source
  simpa only using source

theorem sibling_scheduled (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (message : Digest)
    (k level : Nat) (hk : k<45) (lt : level<height k) :
    GroupedBalancedSignWireUpperFields67.siblingAt
      (signLayers hash secretKey Heights 10 initialIndex.toNat message) k level =
      GroupedBalancedUpperTree67.root hash secretKey (treeBase k) level
        (if (indexAt initialIndex k).toNat/2^level%2=0 then
          (indexAt initialIndex k).toNat/2^level+1
         else (indexAt initialIndex k).toNat/2^level-1) := by
  have hkl : k<Heights.length := by rw [heights_length]; omega
  have lth : level<Heights[k]'hkl := by
    rw [fixed_height_get k hkl]
    exact lt
  have source := signLayers_sibling hash secretKey Heights 10
    initialIndex.toNat message k level hkl lth
  rw [fixed_state hash secretKey initialIndex message k (by omega)] at source
  simpa only using source

theorem node_scheduled (hash : Hash) (secretKey : SecretKey)
    (initialIndex : BitVec 192) (k level : Nat)
    (lt : level<height k) :
    GroupedBalancedSignUpperTreeModel67.nodeAt hash (treeBase k)
      ((indexAt initialIndex k).toNat/2^height k*2^height k)
      (fun x => GroupedBalancedUpperTree67.leafRoot hash secretKey
        (treeBase k)
        ((indexAt initialIndex k).toNat/2^height k*2^height k+x))
      level
      (Nat.xor (((indexAt initialIndex k).toNat%2^height k)/2^level) 1) =
    GroupedBalancedUpperTree67.root hash secretKey (treeBase k) level
      (if (indexAt initialIndex k).toNat/2^level%2=0 then
        (indexAt initialIndex k).toNat/2^level+1
       else (indexAt initialIndex k).toNat/2^level-1) := by
  let idx := (indexAt initialIndex k).toNat
  let h := height k
  let address := idx/2^h
  let selected := idx%2^h
  have recompose : address*2^h+selected=idx := by
    simpa only [address,selected,Nat.mul_comm,Nat.add_comm] using
      (Nat.mod_add_div idx (2^h))
  have built := GroupedBalancedUpperBuildSibling67.built_sibling_node
    hash secretKey (treeBase k) address h selected level 0 lt
  rw [recompose] at built
  rw [GroupedBalancedUpperBuildSibling67.build_sibling hash secretKey
    (treeBase k) h idx level 0 lt] at built
  simpa only [idx,h,address,selected] using built.symm

theorem initial_index_nat (hash : Hash) (secretKey : SecretKey)
    (message : Message) :
    (GroupedBalancedSignByteLoadedBoundary67.initialIndex
      hash secretKey message).toNat =
    GroupedMixedIndex.bottomTree (Reference.indexOf hash message
      (Reference.randomizer hash secretKey message)) := by
  let idx := Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)
  have bound : idx.toNat<2^192 := lt_trans idx.isLt (by decide)
  simp only [GroupedBalancedSignByteLoadedBoundary67.initialIndex,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, GroupedMixedIndex.bottomTree]
  rw [Nat.mod_eq_of_lt bound]

theorem bottom_root_eq (hash : Hash) (secretKey : SecretKey)
    (message : Message) :
    GroupedBalancedSignByteLoadedBoundary67.bottomRoot hash secretKey message =
    GroupedBottomTree.root hash secretKey 10
      (GroupedMixedIndex.bottomTree (Reference.indexOf hash message
        (Reference.randomizer hash secretKey message))) := by
  let idx := Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)
  have split := GroupedBalancedSignBottomIndexBounds67.leafIndex_plus_low idx
  have aligned := GroupedBalancedSignBottomIndexBounds67.leafIndex_align idx
  have low : (idx.extractLsb' 0 10).toNat=idx.toNat%1024 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      show 2^10=1024 by decide]
  have eq : GroupedBalancedSignBottomAddress67.leafIndex idx/1024 =
      idx.toNat/1024 := by
    rw [low] at split
    omega
  change GroupedBottomTree.root hash secretKey 10
    (GroupedBalancedSignBottomAddress67.leafIndex idx/1024) =
    GroupedBottomTree.root hash secretKey 10 (idx.toNat/2^10)
  rw [show 2^10=1024 by decide,eq]

theorem signed_upper_eq (hash : Hash) (secretKey : SecretKey)
    (message : Message) :
    (GroupedBalancedScheme67.sign hash secretKey message).upper =
    signLayers hash secretKey Heights 10
      (GroupedBalancedSignByteLoadedBoundary67.initialIndex
        hash secretKey message).toNat
      (GroupedBalancedSignByteLoadedBoundary67.bottomRoot
        hash secretKey message) := by
  let idx := Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)
  change signLayers hash secretKey Heights 10
    (GroupedMixedIndex.bottomTree idx)
    (GroupedBottomTree.build hash secretKey 10
      (GroupedMixedIndex.bottomTree idx) idx.toNat).root = _
  rw [GroupedBottomTree.build_root,
    ←bottom_root_eq hash secretKey message,
    ←initial_index_nat hash secretKey message]

theorem signed_upper_leaf_word (hash : Hash) (secretKey : SecretKey)
    (message : Message) (k : Nat) (hk : k<45)
    (chain : GroupedBalancedUpperTree67.ChainMixed) (i : Fin 2) :
    (GroupedBalancedWire67.wire
      (GroupedBalancedScheme67.sign hash secretKey message)).extractLsb'
        (8*(208+GroupedBalancedWireUpper67.upperSize (Heights.take k)+
          16*chain.val)+64*i.val) 64 =
      (GroupedBalancedUpperTree67.signValues hash secretKey
        (treeBase k)
        (indexAt (GroupedBalancedSignByteLoadedBoundary67.initialIndex
          hash secretKey message) k).toNat
        (GroupedBalancedSignUpperAllSelected67.messageAfter hash secretKey
          (GroupedBalancedSignByteLoadedBoundary67.initialIndex
            hash secretKey message) 0
          (GroupedBalancedSignByteLoadedBoundary67.bottomRoot
            hash secretKey message) k) chain).extractLsb'
          (64*i.val) 64 := by
  have hkl : k<Heights.length := by rw [heights_length]; omega
  have h := GroupedBalancedSignWireUpperFields67.wire_upper_leaf_word
    (GroupedBalancedScheme67.sign hash secretKey message) k hkl chain i
  rw [signed_upper_eq,
    leaf_scheduled hash secretKey
      (GroupedBalancedSignByteLoadedBoundary67.initialIndex
        hash secretKey message)
      (GroupedBalancedSignByteLoadedBoundary67.bottomRoot
        hash secretKey message) k hk chain] at h
  exact h

theorem signed_upper_sibling_word (hash : Hash) (secretKey : SecretKey)
    (message : Message) (k level : Nat)
    (hk : k<45) (lt : level<height k) (i : Fin 2) :
    (GroupedBalancedWire67.wire
      (GroupedBalancedScheme67.sign hash secretKey message)).extractLsb'
        (8*(208+GroupedBalancedWireUpper67.upperSize (Heights.take k)+
          16*(67+level))+64*i.val) 64 =
      (GroupedBalancedSignUpperTreeModel67.nodeAt hash (treeBase k)
        ((indexAt (GroupedBalancedSignByteLoadedBoundary67.initialIndex
          hash secretKey message) k).toNat/2^height k*2^height k)
        (fun x => GroupedBalancedUpperTree67.leafRoot hash secretKey
          (treeBase k)
          ((indexAt (GroupedBalancedSignByteLoadedBoundary67.initialIndex
            hash secretKey message) k).toNat/2^height k*2^height k+x))
        level
        (Nat.xor (((indexAt
          (GroupedBalancedSignByteLoadedBoundary67.initialIndex
            hash secretKey message) k).toNat%2^height k)/2^level) 1)
        ).extractLsb' (64*i.val) 64 := by
  have hkl : k<Heights.length := by rw [heights_length]; omega
  have lth : level<Heights[k]'hkl := by
    rw [fixed_height_get k hkl]
    exact lt
  have h := GroupedBalancedSignWireUpperFields67.wire_upper_sibling_word
    (GroupedBalancedScheme67.sign hash secretKey message) k hkl level lth i
  rw [signed_upper_eq,
    sibling_scheduled hash secretKey
      (GroupedBalancedSignByteLoadedBoundary67.initialIndex
        hash secretKey message)
      (GroupedBalancedSignByteLoadedBoundary67.bottomRoot
        hash secretKey message) k level hk lt] at h
  rw [node_scheduled hash secretKey
    (GroupedBalancedSignByteLoadedBoundary67.initialIndex
      hash secretKey message) k level lt]
  exact h

theorem signed_bottom_sibling_node_word (hash : Hash)
    (secretKey : SecretKey) (message : Message)
    (level : Nat) (lt : level<10) (i : Fin 2) :
    (GroupedBalancedWire67.wire
      (GroupedBalancedScheme67.sign hash secretKey message)).extractLsb'
        (8*(32+16*(level+1))+64*i.val) 64 =
      (GroupedBalancedSignBottomTreeModel67.levelNode hash secretKey
        (GroupedBalancedSignBottomAddress67.leafIndex
          (Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)))
        level (Nat.xor
          (((Reference.indexOf hash message
            (Reference.randomizer hash secretKey message)).extractLsb'
              0 10).toNat/2^level) 1)).extractLsb' (64*i.val) 64 := by
  let idx := Reference.indexOf hash message
    (Reference.randomizer hash secretKey message)
  have low : (idx.extractLsb' 0 10).toNat=idx.toNat%1024 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
      show 2^10=1024 by decide]
  have split := GroupedBalancedSignBottomIndexBounds67.leafIndex_plus_low idx
  rw [low] at split
  have base : GroupedBalancedSignBottomAddress67.leafIndex idx =
      idx.toNat/1024*1024 := by
    have h := Nat.mod_add_div idx.toNat 1024
    omega
  have recompose : idx.toNat/2^10*2^10+idx.toNat%2^10=idx.toNat := by
    have h := Nat.mod_add_div idx.toNat (2^10)
    omega
  have built := GroupedBalancedBottomBuildSibling67.built_sibling_node
    hash secretKey (idx.toNat/2^10) (idx.toNat%2^10) level lt
  rw [recompose] at built
  have word := GroupedBalancedSignWireFields67.bottom_sibling_word
    (GroupedBalancedScheme67.sign hash secretKey message) level lt i
  change _ = ((GroupedBalancedBottomBuildSibling67.siblingAt
    (GroupedBottomTree.build hash secretKey 10
      (idx.toNat/2^10) idx.toNat).witness level).extractLsb'
        (64*i.val) 64) at word
  rw [built] at word
  change _ = (GroupedBalancedSignBottomTreeModel67.levelNode hash secretKey
    (idx.toNat/2^10*2^10) level
    (Nat.xor ((idx.toNat%2^10)/2^level) 1)).extractLsb'
      (64*i.val) 64 at word
  simpa only [show 2^10=1024 by decide, ←base, ←low] using word

#print axioms afterPrefix_append
#print axioms fixed_height_get
#print axioms fixed_state
#print axioms leaf_scheduled
#print axioms sibling_scheduled
#print axioms node_scheduled
#print axioms initial_index_nat
#print axioms bottom_root_eq
#print axioms signed_upper_eq
#print axioms signed_upper_leaf_word
#print axioms signed_upper_sibling_word
#print axioms signed_bottom_sibling_node_word
end SigGolfCandidate.Hypertree.GroupedBalancedSignLayersSchedule67
