import SigGolfCandidate.Hypertree.GroupedBalancedUpperIndex67

/-! Merkle part of direct 67-chain upper-path extraction. An accepted upper witness
either recovers the canonical WOTS leaf at the selected index or contains a
same-address truncated-hash collision at an authentication node. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperMerkleExtraction67
open SigGolf SigGolfCandidate.Hypertree
open GroupedBalancedUpperTree67
abbrev Digest := Reference.Digest

def Bad (hash : Hash) (secretKey : SecretKey) (base : Nat) (message : Digest) :
    (height address index : Nat) → Witness height → Prop
  | 0, _, _, .leaf _ => False
  | height + 1, address, index, .step inner sibling =>
      if index / 2 ^ height % 2 = 0 then
        (((recover hash base height (2 * address) index message inner, sibling) ≠
            (root hash secretKey base height (2 * address),
              root hash secretKey base height (2 * address + 1))) ∧
          node hash (base + height) address
              (recover hash base height (2 * address) index message inner) sibling =
            node hash (base + height) address
              (root hash secretKey base height (2 * address))
              (root hash secretKey base height (2 * address + 1))) ∨
          Bad hash secretKey base message height (2 * address) index inner
      else
        (((sibling, recover hash base height (2 * address + 1) index message inner) ≠
            (root hash secretKey base height (2 * address),
              root hash secretKey base height (2 * address + 1))) ∧
          node hash (base + height) address sibling
              (recover hash base height (2 * address + 1) index message inner) =
            node hash (base + height) address
              (root hash secretKey base height (2 * address))
              (root hash secretKey base height (2 * address + 1))) ∨
          Bad hash secretKey base message height (2 * address + 1) index inner

theorem recover_extract (hash : Hash) (secretKey : SecretKey)
    (base height address index : Nat) (message : Digest)
    (witness : Witness height)
    (accepted : recover hash base height address index message witness =
      root hash secretKey base height address) :
    recoverLeaf hash base
      (GroupedBottomTree.selectedLeafAddress height address index) message
      (GroupedBalancedUpperIndex67.witnessValues witness) =
        leafRoot hash secretKey base
          (GroupedBottomTree.selectedLeafAddress height address index) ∨
      Bad hash secretKey base message height address index witness := by
  induction height generalizing address with
  | zero =>
      cases witness with
      | leaf values => exact Or.inl accepted
  | succ height ih =>
      cases witness with
      | step inner sibling =>
          by_cases bit : index / 2 ^ height % 2 = 0
          · have sameRoot :
                node hash (base + height) address
                  (recover hash base height (2 * address) index message inner) sibling =
                node hash (base + height) address
                  (root hash secretKey base height (2 * address))
                  (root hash secretKey base height (2 * address + 1)) := by
              simpa only [recover, root, if_pos bit] using accepted
            by_cases samePair :
                (recover hash base height (2 * address) index message inner, sibling) =
                  (root hash secretKey base height (2 * address),
                    root hash secretKey base height (2 * address + 1))
            · have childRoot := congrArg Prod.fst samePair
              rcases ih (2 * address) inner childRoot with leaf | bad
              · left
                simpa only [GroupedBottomTree.selectedLeafAddress,
                  GroupedBalancedUpperIndex67.witnessValues, if_pos bit] using leaf
              · right
                simp only [Bad, if_pos bit]
                exact Or.inr bad
            · right
              simp only [Bad, if_pos bit]
              exact Or.inl ⟨samePair, sameRoot⟩
          · have sameRoot :
                node hash (base + height) address sibling
                  (recover hash base height (2 * address + 1) index message inner) =
                node hash (base + height) address
                  (root hash secretKey base height (2 * address))
                  (root hash secretKey base height (2 * address + 1)) := by
              simpa only [recover, root, if_neg bit] using accepted
            by_cases samePair :
                (sibling, recover hash base height (2 * address + 1) index message inner) =
                  (root hash secretKey base height (2 * address),
                    root hash secretKey base height (2 * address + 1))
            · have childRoot := congrArg Prod.snd samePair
              rcases ih (2 * address + 1) inner childRoot with leaf | bad
              · left
                simpa only [GroupedBottomTree.selectedLeafAddress,
                  GroupedBalancedUpperIndex67.witnessValues, if_neg bit] using leaf
              · right
                simp only [Bad, if_neg bit]
                exact Or.inr bad
            · right
              simp only [Bad, if_neg bit]
              exact Or.inl ⟨samePair, sameRoot⟩

theorem recover_full_index (hash : Hash) (secretKey : SecretKey)
    (base height index : Nat) (message : Digest)
    (witness : Witness height)
    (accepted : recover hash base height (index / 2 ^ height)
      index message witness =
        root hash secretKey base height (index / 2 ^ height)) :
    recoverLeaf hash base index message
      (GroupedBalancedUpperIndex67.witnessValues witness) =
        leafRoot hash secretKey base index ∨
      Bad hash secretKey base message height (index / 2 ^ height)
        index witness := by
  have result := recover_extract hash secretKey base height
    (index / 2 ^ height) index message witness accepted
  simpa only [GroupedBottomTree.selectedLeafAddress_index] using result

end SigGolfCandidate.Hypertree.GroupedBalancedUpperMerkleExtraction67
