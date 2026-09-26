import SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoadedBoundary67
import SigGolfCandidate.Hypertree.GroupedBalancedScheme67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomIndexBounds67

/-! The signer’s aligned bottom-tree address is the scheme’s tree address. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignRootBridge67
open SigGolf SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomAddress67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem leaf_index_tree (index : BitVec 160) :
    leafIndex index / 1024 = GroupedMixedIndex.bottomTree index := by
  have aligned := GroupedBalancedSignBottomIndexBounds67.leafIndex_align index
  have sum := GroupedBalancedSignBottomIndexBounds67.leafIndex_plus_low index
  have lowBound := (index.extractLsb' 0 10).isLt
  unfold GroupedMixedIndex.bottomTree
  change leafIndex index / 1024 = index.toNat / 1024
  omega

theorem bottom_root_scheme (hash : Hash) (secretKey : SecretKey)
    (message : Message) :
    GroupedBalancedSignByteLoadedBoundary67.bottomRoot
      hash secretKey message =
    GroupedBottomTree.root hash secretKey 10
      (GroupedMixedIndex.bottomTree
        (Reference.indexOf hash message
          (Reference.randomizer hash secretKey message))) := by
  simp only [GroupedBalancedSignByteLoadedBoundary67.bottomRoot]
  rw [leaf_index_tree]

#print axioms leaf_index_tree
#print axioms bottom_root_scheme
end SigGolfCandidate.Hypertree.GroupedBalancedSignRootBridge67
