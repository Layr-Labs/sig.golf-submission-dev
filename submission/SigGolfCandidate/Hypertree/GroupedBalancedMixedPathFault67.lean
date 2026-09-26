import SigGolfCandidate.Hypertree.GroupedBalancedUpperPathFault67
import SigGolfCandidate.Hypertree.GroupedBalancedScheme67
import SigGolfCandidate.Hypertree.GroupedBottomExtraction

/-! Backward binding through the 45 direct 67-chain upper trees. If final recovery
reaches the canonical terminal root and no path fault occurs, the incoming
digest of every group is its canonical child-tree root. The first incoming
digest is therefore the canonical bottom root. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedMixedPathFault67
open SigGolf SigGolfCandidate.Hypertree
abbrev Digest := Reference.Digest
open GroupedBalancedScheme67

def PathFault (hash : Hash) (secretKey : SecretKey) :
    (heights : List Nat) → (base index : Nat) →
      (expected actual : Digest) → UpperWitnesses heights → Prop
  | [], _, _, _, _, .nil => False
  | height :: rest, base, index, expected, actual, .cons head tail =>
      let tree := index / 2 ^ height
      let actualRoot := GroupedBalancedUpperTree67.recover hash base height tree
        index actual head
      let canonicalRoot := GroupedBalancedUpperTree67.root hash secretKey base
        height tree
      GroupedBalancedUpperPathFault67.Bad hash secretKey base height index actual head ∨
        (expected ≠ actual ∧
          GroupedBalancedUpperPathFault67.EarlierPointExposure hash secretKey
            base index expected actual head) ∨
        PathFault hash secretKey rest (base + height) tree
          canonicalRoot actualRoot tail

theorem path_binding_no_fault (hash : Hash) (secretKey : SecretKey)
    (heights : List Nat) (base index : Nat)
    (expected actual : Digest) (witnesses : UpperWitnesses heights)
    (accepted : recoverLayers hash heights base index actual witnesses =
      rootsAfter hash secretKey heights base index expected)
    (clean : ¬PathFault hash secretKey heights base index
      expected actual witnesses) :
    actual = expected := by
  induction heights generalizing base index expected actual with
  | nil =>
      cases witnesses
      exact accepted
  | cons height rest ih =>
      cases witnesses with
      | cons head tail =>
          let tree := index / 2 ^ height
          let actualRoot := GroupedBalancedUpperTree67.recover hash base height tree
            index actual head
          let canonicalRoot := GroupedBalancedUpperTree67.root hash secretKey base
            height tree
          have tailAccepted :
              recoverLayers hash rest (base + height) tree actualRoot tail =
                rootsAfter hash secretKey rest (base + height) tree
                  canonicalRoot := by
            simpa only [recoverLayers, rootsAfter, tree,
              actualRoot, canonicalRoot] using accepted
          have cleanTail : ¬PathFault hash secretKey rest
              (base + height) tree canonicalRoot actualRoot tail := by
            intro fault
            apply clean
            change _ ∨ _ ∨ PathFault hash secretKey rest
              (base + height) tree canonicalRoot actualRoot tail
            exact Or.inr (Or.inr fault)
          have actualRootEq := ih (base + height) tree canonicalRoot
            actualRoot tail tailAccepted cleanTail
          by_cases different : expected ≠ actual
          · rcases GroupedBalancedUpperPathFault67.changed_message_exposes_point
              hash secretKey base height index expected actual head
              different actualRootEq with bad | exposure
            · exact False.elim (clean (by
                change _ ∨ _ ∨ PathFault hash secretKey rest
                  (base + height) tree canonicalRoot actualRoot tail
                exact Or.inl bad))
            · exact False.elim (clean (by
                change _ ∨ _ ∨ PathFault hash secretKey rest
                  (base + height) tree canonicalRoot actualRoot tail
                exact Or.inr (Or.inl ⟨different, exposure⟩)))
          · exact (Classical.not_not.mp different).symm

def UpperFault (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) (signature : Signature) : Prop :=
  PathFault hash secretKey Heights 10
    (GroupedMixedIndex.bottomTree index)
    (GroupedBottomTree.root hash secretKey 10
      (GroupedMixedIndex.bottomTree index))
    (GroupedBottomTree.recover hash 10
      (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
    signature.upper

theorem accepted_fault_or_bottom_source (hash : Hash)
    (secretKey : SecretKey) (index : BitVec 160)
    (signature : Signature)
    (accepted : recoverLayers hash Heights 10
      (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper = GroupedBalancedScheme67.keygen hash secretKey) :
    UpperFault hash secretKey index signature ∨
      signature.bottom.seedValue =
        GroupedBottomTree.secret hash secretKey index.toNat ∨
      GroupedBottomExtraction.Bad hash secretKey 10
        (GroupedMixedIndex.bottomTree index) index.toNat
        signature.bottom := by
  by_cases fault : UpperFault hash secretKey index signature
  · exact Or.inl fault
  · right
    have target : rootsAfter hash secretKey Heights 10
        (GroupedMixedIndex.bottomTree index)
        (GroupedBottomTree.root hash secretKey 10
          (GroupedMixedIndex.bottomTree index)) =
        GroupedBalancedScheme67.keygen hash secretKey := by
      simpa only [GroupedBalancedScheme67.keygen] using
        final_root hash secretKey index
          (GroupedBottomTree.root hash secretKey 10
            (GroupedMixedIndex.bottomTree index))
    have bottomRoot := path_binding_no_fault hash secretKey Heights 10
      (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.root hash secretKey 10
        (GroupedMixedIndex.bottomTree index))
      (GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper (accepted.trans target.symm) fault
    exact GroupedBottomExtraction.recover_full_index hash secretKey index
      signature.bottom bottomRoot

/-- info: 'SigGolfCandidate.Hypertree.GroupedBalancedMixedPathFault67.accepted_fault_or_bottom_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms accepted_fault_or_bottom_source

end SigGolfCandidate.Hypertree.GroupedBalancedMixedPathFault67
