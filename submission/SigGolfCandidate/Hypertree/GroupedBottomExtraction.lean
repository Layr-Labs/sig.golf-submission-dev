import SigGolfCandidate.Hypertree.GroupedBottomTree
import SigGolfCandidate.Hypertree.GroupedMixedIndex

/-! Deterministic bottom authentication extraction. Any accepted bottom witness
either exposes the exact private seed at its selected full index or contains a
same-address truncated-hash collision on its Merkle path. -/

namespace SigGolfCandidate.Hypertree.GroupedBottomExtraction
open SigGolf SigGolfCandidate.Hypertree
open GroupedBottomTree

def Bad (hash : Hash) (secretKey : SecretKey) :
    (height address index : Nat) → Witness height → Prop
  | 0, address, _, .seed seed =>
      seed ≠ secret hash secretKey address ∧
        leafFromSeed hash address seed = leafRoot hash secretKey address
  | height + 1, address, index, .step inner sibling =>
      if index / 2 ^ height % 2 = 0 then
        (((recover hash height (2 * address) index inner, sibling) ≠
            (root hash secretKey height (2 * address),
              root hash secretKey height (2 * address + 1))) ∧
          node hash height address
              (recover hash height (2 * address) index inner) sibling =
            node hash height address
              (root hash secretKey height (2 * address))
              (root hash secretKey height (2 * address + 1))) ∨
          Bad hash secretKey height (2 * address) index inner
      else
        (((sibling, recover hash height (2 * address + 1) index inner) ≠
            (root hash secretKey height (2 * address),
              root hash secretKey height (2 * address + 1))) ∧
          node hash height address sibling
              (recover hash height (2 * address + 1) index inner) =
            node hash height address
              (root hash secretKey height (2 * address))
              (root hash secretKey height (2 * address + 1))) ∨
          Bad hash secretKey height (2 * address + 1) index inner

theorem recover_extract (hash : Hash) (secretKey : SecretKey)
    (height address index : Nat) (witness : Witness height)
    (accepted : recover hash height address index witness =
      root hash secretKey height address) :
    witness.seedValue =
      secret hash secretKey (selectedLeafAddress height address index) ∨
      Bad hash secretKey height address index witness := by
  induction height generalizing address with
  | zero =>
      cases witness with
      | seed seed =>
          by_cases exposed : seed = secret hash secretKey address
          · exact Or.inl exposed
          · exact Or.inr ⟨exposed, accepted⟩
  | succ height ih =>
      cases witness with
      | step inner sibling =>
          by_cases bit : index / 2 ^ height % 2 = 0
          · have sameRoot :
                node hash height address
                  (recover hash height (2 * address) index inner) sibling =
                node hash height address
                  (root hash secretKey height (2 * address))
                  (root hash secretKey height (2 * address + 1)) := by
              simpa only [recover, root, if_pos bit] using accepted
            by_cases samePair :
                (recover hash height (2 * address) index inner, sibling) =
                  (root hash secretKey height (2 * address),
                    root hash secretKey height (2 * address + 1))
            · have childRoot := congrArg Prod.fst samePair
              rcases ih (2 * address) inner childRoot with exposed | bad
              · left
                simpa only [Witness.seedValue, selectedLeafAddress, if_pos bit]
                  using exposed
              · right
                simpa only [Bad, if_pos bit] using
                  (Or.inr bad :
                    (((recover hash height (2 * address) index inner, sibling) ≠
                        (root hash secretKey height (2 * address),
                          root hash secretKey height (2 * address + 1))) ∧
                      node hash height address
                          (recover hash height (2 * address) index inner) sibling =
                        node hash height address
                          (root hash secretKey height (2 * address))
                          (root hash secretKey height (2 * address + 1))) ∨
                      Bad hash secretKey height (2 * address) index inner)
            · right
              simpa only [Bad, if_pos bit] using
                (Or.inl ⟨samePair, sameRoot⟩ :
                  (((recover hash height (2 * address) index inner, sibling) ≠
                      (root hash secretKey height (2 * address),
                        root hash secretKey height (2 * address + 1))) ∧
                    node hash height address
                        (recover hash height (2 * address) index inner) sibling =
                      node hash height address
                        (root hash secretKey height (2 * address))
                        (root hash secretKey height (2 * address + 1))) ∨
                    Bad hash secretKey height (2 * address) index inner)
          · have sameRoot :
                node hash height address sibling
                  (recover hash height (2 * address + 1) index inner) =
                node hash height address
                  (root hash secretKey height (2 * address))
                  (root hash secretKey height (2 * address + 1)) := by
              simpa only [recover, root, if_neg bit] using accepted
            by_cases samePair :
                (sibling, recover hash height (2 * address + 1) index inner) =
                  (root hash secretKey height (2 * address),
                    root hash secretKey height (2 * address + 1))
            · have childRoot := congrArg Prod.snd samePair
              rcases ih (2 * address + 1) inner childRoot with exposed | bad
              · left
                simpa only [Witness.seedValue, selectedLeafAddress, if_neg bit]
                  using exposed
              · right
                simpa only [Bad, if_neg bit] using
                  (Or.inr bad :
                    (((sibling, recover hash height (2 * address + 1) index inner) ≠
                        (root hash secretKey height (2 * address),
                          root hash secretKey height (2 * address + 1))) ∧
                      node hash height address sibling
                          (recover hash height (2 * address + 1) index inner) =
                        node hash height address
                          (root hash secretKey height (2 * address))
                          (root hash secretKey height (2 * address + 1))) ∨
                      Bad hash secretKey height (2 * address + 1) index inner)
            · right
              simpa only [Bad, if_neg bit] using
                (Or.inl ⟨samePair, sameRoot⟩ :
                  (((sibling, recover hash height (2 * address + 1) index inner) ≠
                      (root hash secretKey height (2 * address),
                        root hash secretKey height (2 * address + 1))) ∧
                    node hash height address sibling
                        (recover hash height (2 * address + 1) index inner) =
                      node hash height address
                        (root hash secretKey height (2 * address))
                        (root hash secretKey height (2 * address + 1))) ∨
                    Bad hash secretKey height (2 * address + 1) index inner)

theorem recover_full_index (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) (witness : Witness 10)
    (accepted : recover hash 10 (GroupedMixedIndex.bottomTree index)
      index.toNat witness =
        root hash secretKey 10 (GroupedMixedIndex.bottomTree index)) :
    witness.seedValue = secret hash secretKey index.toNat ∨
      Bad hash secretKey 10 (GroupedMixedIndex.bottomTree index)
        index.toNat witness := by
  have result := recover_extract hash secretKey 10
    (GroupedMixedIndex.bottomTree index) index.toNat witness accepted
  simpa only [GroupedMixedIndex.bottomTree,
    selectedLeafAddress_index] using result

/-- info: 'SigGolfCandidate.Hypertree.GroupedBottomExtraction.recover_full_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms recover_full_index

end SigGolfCandidate.Hypertree.GroupedBottomExtraction
