import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.Hypertree.SecurityExtraction

/-! Collision extraction for a changed direct 67-chain WOTS witness at one
fixed tree address. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedWotsExtraction67
open SigGolf SigGolfCandidate.Hypertree
open GroupedBalancedUpperTree67 SecurityExtraction SecurityPacking SignatureEncoding
abbrev Digest := Reference.Digest

theorem recover_chain (hash : Hash) (base leaf : Nat)
    (chain : ChainMixed) (secretValue : Digest) (digitValue : Fin 11)
    (bound : digitValue.val ≤ maxDigit chain) :
    walk (chainHash hash base leaf chain) digitValue.val
      (maxDigit chain - digitValue.val)
      (walk (chainHash hash base leaf chain) 0 digitValue.val secretValue) =
    walk (chainHash hash base leaf chain) 0 (maxDigit chain) secretValue := by
  simpa only [Nat.add_sub_of_le bound, Nat.zero_add] using
    (walk_append (chainHash hash base leaf chain) 0 digitValue.val
      (maxDigit chain - digitValue.val) secretValue).symm

theorem changed_fragment_collision (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (message : Digest) (chain : ChainMixed)
    (fragment : Digest)
    (different : fragment ≠
      walk (chainHash hash base leaf chain) 0
        (digit message chain).val
        (secret hash secretKey base leaf chain))
    (same : walk (chainHash hash base leaf chain)
      (digit message chain).val (maxDigit chain - (digit message chain).val)
        fragment = endpoint hash secretKey base leaf chain) :
    ∃ offset, offset < maxDigit chain - (digit message chain).val ∧
      CollisionAt hash 2 base leaf 0 chain.val
        ((digit message chain).val + offset)
        (bytes (walk (chainHash hash base leaf chain) 0
          ((digit message chain).val + offset)
          (secret hash secretKey base leaf chain)))
        (bytes (walk (chainHash hash base leaf chain)
          (digit message chain).val offset fragment)) := by
  have bound := GroupedBalancedChecksum67.digit_le_max message chain
  have canonical := recover_chain hash base leaf chain
    (secret hash secretKey base leaf chain) (digit message chain) bound
  obtain ⟨offset, offsetBound, ne, equal⟩ := walk_merge
    (chainHash hash base leaf chain) (digit message chain).val
    (maxDigit chain - (digit message chain).val)
    (walk (chainHash hash base leaf chain) 0
      (digit message chain).val (secret hash secretKey base leaf chain))
    fragment different (same.trans canonical.symm)
  refine ⟨offset, offsetBound, ?_⟩
  have splitWalk := walk_append (chainHash hash base leaf chain) 0
    (digit message chain).val offset
    (secret hash secretKey base leaf chain)
  simp only [Nat.zero_add] at splitWalk
  rw [splitWalk]
  exact collisionAt_of_payload_ne hash 2 base leaf 0 chain.val
    ((digit message chain).val + offset) _ _
    (fun sameBytes => ne (bytes_injective 16 sameBytes)) equal

theorem upper_leaf_binding (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (message : Digest)
    (values : ChainMixed → Digest)
    (same : recoverLeaf hash base leaf message values =
      leafRoot hash secretKey base leaf) :
    (∀ chain, walk (chainHash hash base leaf chain)
      (digit message chain).val
      (maxDigit chain - (digit message chain).val)
        (values chain) = endpoint hash secretKey base leaf chain) ∨
    CollisionAt hash 3 base leaf 0 0 0
      ((List.ofFn (endpoint hash secretKey base leaf)).flatMap bytes)
      ((List.ofFn (fun chain => walk (chainHash hash base leaf chain)
        (digit message chain).val
        (maxDigit chain - (digit message chain).val)
          (values chain))).flatMap bytes) := by
  classical
  simp only [recoverLeaf, leafRoot, compressLeaf] at same
  by_cases equalPayload :
      ((List.ofFn (fun chain => walk (chainHash hash base leaf chain)
        (digit message chain).val
        (maxDigit chain - (digit message chain).val)
          (values chain))).flatMap bytes) =
      ((List.ofFn (endpoint hash secretKey base leaf)).flatMap bytes)
  · left
    have words := flatMap_injective (bytes (n := 16)) 16
      (by decide) (fun _ => by simp) (bytes_injective 16) equalPayload
    exact congrFun (List.ofFn_injective words)
  · right
    exact collisionAt_of_payload_ne hash 3 base leaf 0 0 0
      _ _ equalPayload same

def LeafCollision (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (message : Digest) (values : ChainMixed → Digest) : Prop :=
  CollisionAt hash 3 base leaf 0 0 0
    ((List.ofFn (endpoint hash secretKey base leaf)).flatMap bytes)
    ((List.ofFn (fun chain => walk (chainHash hash base leaf chain)
      (digit message chain).val
      (maxDigit chain - (digit message chain).val)
        (values chain))).flatMap bytes) ∨
  ∃ chain offset, offset < maxDigit chain - (digit message chain).val ∧
    CollisionAt hash 2 base leaf 0 chain.val
      ((digit message chain).val + offset)
      (bytes (walk (chainHash hash base leaf chain) 0
        ((digit message chain).val + offset)
        (secret hash secretKey base leaf chain)))
      (bytes (walk (chainHash hash base leaf chain)
        (digit message chain).val offset (values chain)))

theorem leaf_canonical_or_collision (hash : Hash) (secretKey : SecretKey)
    (base leaf : Nat) (message : Digest)
    (values : ChainMixed → Digest)
    (same : recoverLeaf hash base leaf message values =
      leafRoot hash secretKey base leaf) :
    (∀ chain, values chain =
      (signValues hash secretKey base leaf message) chain) ∨
      LeafCollision hash secretKey base leaf message values := by
  rcases upper_leaf_binding hash secretKey base leaf message values same with
    endpoints | leafHit
  · by_cases canonical : ∀ chain, values chain =
        (signValues hash secretKey base leaf message) chain
    · exact Or.inl canonical
    · push Not at canonical
      obtain ⟨chain, different⟩ := canonical
      obtain ⟨offset, bound, hit⟩ := changed_fragment_collision
        hash secretKey base leaf message chain (values chain)
        (by simpa only [signValues] using different)
        (endpoints chain)
      exact Or.inr (Or.inr ⟨chain, offset, bound, hit⟩)
  · exact Or.inr (Or.inl leafHit)

end SigGolfCandidate.Hypertree.GroupedBalancedWotsExtraction67
