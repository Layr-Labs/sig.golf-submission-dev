import SigGolfCandidate.Hypertree.GroupedBalancedWotsExtraction67
import SigGolfCandidate.Hypertree.GroupedBalancedUpperMerkleExtraction67
import SigGolfCandidate.Hypertree.GroupedBalancedChecksum67

/-! One accepted grouped upper tree either has canonical selected WOTS values
or a concrete Merkle, leaf, or chain collision. If its incoming digest differs
from the canonical child digest, fixed-weight coding then exposes an earlier
canonical chain point. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperPathFault67
open SigGolf SigGolfCandidate.Hypertree
abbrev Digest := Reference.Digest

def Bad (hash : Hash) (secretKey : SecretKey)
    (base height index : Nat) (message : Digest)
    (witness : GroupedBalancedUpperTree67.Witness height) : Prop :=
  GroupedBalancedUpperMerkleExtraction67.Bad hash secretKey base message height
    (index / 2 ^ height) index witness ∨
  GroupedBalancedWotsExtraction67.LeafCollision hash secretKey base index message
    (GroupedBalancedUpperIndex67.witnessValues witness)

theorem recover_full_index_canonical_or_fault (hash : Hash)
    (secretKey : SecretKey) (base height index : Nat)
    (message : Digest) (witness : GroupedBalancedUpperTree67.Witness height)
    (accepted : GroupedBalancedUpperTree67.recover hash base height
      (index / 2 ^ height) index message witness =
      GroupedBalancedUpperTree67.root hash secretKey base height
        (index / 2 ^ height)) :
    (∀ chain, GroupedBalancedUpperIndex67.witnessValues witness chain =
      (GroupedBalancedUpperTree67.signValues hash secretKey base index message) chain) ∨
    Bad hash secretKey base height index message witness := by
  rcases GroupedBalancedUpperMerkleExtraction67.recover_full_index hash secretKey
    base height index message witness accepted with leaf | merkle
  · rcases GroupedBalancedWotsExtraction67.leaf_canonical_or_collision hash secretKey
      base index message (GroupedBalancedUpperIndex67.witnessValues witness) leaf with
      canonical | collision
    · exact Or.inl canonical
    · exact Or.inr (Or.inr collision)
  · exact Or.inr (Or.inl merkle)

def EarlierPointExposure (hash : Hash) (secretKey : SecretKey)
    (base index : Nat) (signed forged : Digest)
    {height : Nat} (witness : GroupedBalancedUpperTree67.Witness height) : Prop :=
  ∃ chain : GroupedBalancedUpperTree67.ChainMixed,
    (GroupedBalancedUpperTree67.digit forged chain).val <
      (GroupedBalancedUpperTree67.digit signed chain).val ∧
    GroupedBalancedUpperIndex67.witnessValues witness chain =
      walk (GroupedBalancedUpperTree67.chainHash hash base index chain) 0
        (GroupedBalancedUpperTree67.digit forged chain).val
        (GroupedBalancedUpperTree67.secret hash secretKey base index chain)

theorem changed_message_exposes_point (hash : Hash)
    (secretKey : SecretKey) (base height index : Nat)
    (signed forged : Digest)
    (witness : GroupedBalancedUpperTree67.Witness height)
    (different : signed ≠ forged)
    (accepted : GroupedBalancedUpperTree67.recover hash base height
      (index / 2 ^ height) index forged witness =
      GroupedBalancedUpperTree67.root hash secretKey base height
        (index / 2 ^ height)) :
    Bad hash secretKey base height index forged witness ∨
      EarlierPointExposure hash secretKey base index signed forged witness := by
  rcases recover_full_index_canonical_or_fault hash secretKey
    base height index forged witness accepted with canonical | bad
  · right
    obtain ⟨chain, earlier⟩ :=
      GroupedBalancedChecksum67.distinct_digest_has_earlier_digit signed forged different
    exact ⟨chain, earlier, canonical chain⟩
  · exact Or.inl bad

end SigGolfCandidate.Hypertree.GroupedBalancedUpperPathFault67
