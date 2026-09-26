import SigGolfCandidate.Hypertree.GroupedBalancedUpperPathFault67
import SigGolfCandidate.Hypertree.GroupedBalancedMixedPathFault67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedUpperCanonicalOrBad67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedPathCanonicalOrFault67. -/
section
/-! An accepted direct67 upper witness is exactly the honest witness for its
incoming message, or its recovery contains an upper Merkle/WOTS collision. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperCanonicalOrBad67
open SigGolf SigGolfCandidate.Hypertree
open GroupedBalancedUpperTree67
open GroupedBalancedUpperMerkleExtraction67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem recover_exact_given_values_or_merkle_bad
    (hash : Hash) (secretKey : SecretKey) (base : Nat)
    (message : Reference.Digest) (height address index : Nat)
    (witness : Witness height)
    (accepted : recover hash base height address index message witness =
      root hash secretKey base height address)
    (values : GroupedBalancedUpperIndex67.witnessValues witness =
      signValues hash secretKey base
        (GroupedBottomTree.selectedLeafAddress height address index) message) :
    witness = (build hash secretKey base height address index message).witness ∨
      Bad hash secretKey base message height address index witness := by
  induction height generalizing address with
  | zero =>
      cases witness with
      | leaf actual =>
          left
          simpa only [build, GroupedBalancedUpperIndex67.witnessValues,
            GroupedBottomTree.selectedLeafAddress] using
            congrArg Witness.leaf values
  | succ height ih =>
      cases witness with
      | step inner sibling =>
          by_cases bit : index / 2 ^ height % 2 = 0
          · have sameRoot :
                node hash (base + height) address
                  (recover hash base height (2 * address) index message inner)
                  sibling =
                node hash (base + height) address
                  (root hash secretKey base height (2 * address))
                  (root hash secretKey base height (2 * address + 1)) := by
              simpa only [recover, root, if_pos bit] using accepted
            by_cases samePair :
                (recover hash base height (2 * address) index message inner,
                  sibling) =
                (root hash secretKey base height (2 * address),
                  root hash secretKey base height (2 * address + 1))
            · have childRoot := congrArg Prod.fst samePair
              have childValues : GroupedBalancedUpperIndex67.witnessValues inner =
                  signValues hash secretKey base
                    (GroupedBottomTree.selectedLeafAddress height (2 * address)
                      index) message := by
                simpa only [GroupedBalancedUpperIndex67.witnessValues,
                  GroupedBottomTree.selectedLeafAddress, if_pos bit] using values
              rcases ih (2 * address) inner childRoot childValues with
                canonical | childBad
              · left
                have siblingEq : sibling =
                    root hash secretKey base height (2 * address + 1) := by
                  simpa only using congrArg Prod.snd samePair
                simp only [build, if_pos bit]
                rw [canonical, siblingEq]
              · right
                simp only [Bad, if_pos bit]
                exact Or.inr childBad
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
                (sibling,
                  recover hash base height (2 * address + 1) index message inner) =
                (root hash secretKey base height (2 * address),
                  root hash secretKey base height (2 * address + 1))
            · have childRoot := congrArg Prod.snd samePair
              have childValues : GroupedBalancedUpperIndex67.witnessValues inner =
                  signValues hash secretKey base
                    (GroupedBottomTree.selectedLeafAddress height
                      (2 * address + 1) index) message := by
                simpa only [GroupedBalancedUpperIndex67.witnessValues,
                  GroupedBottomTree.selectedLeafAddress, if_neg bit] using values
              rcases ih (2 * address + 1) inner childRoot childValues with
                canonical | childBad
              · left
                have siblingEq : sibling =
                    root hash secretKey base height (2 * address) := by
                  simpa only using congrArg Prod.fst samePair
                simp only [build, if_neg bit]
                rw [canonical, siblingEq]
              · right
                simp only [Bad, if_neg bit]
                exact Or.inr childBad
            · right
              simp only [Bad, if_neg bit]
              exact Or.inl ⟨samePair, sameRoot⟩

theorem recover_full_index_canonical_or_bad
    (hash : Hash) (secretKey : SecretKey) (base height index : Nat)
    (message : Reference.Digest) (witness : Witness height)
    (accepted : recover hash base height (index / 2 ^ height)
      index message witness =
      root hash secretKey base height (index / 2 ^ height)) :
    witness = (build hash secretKey base height
      (index / 2 ^ height) index message).witness ∨
    GroupedBalancedUpperPathFault67.Bad hash secretKey base height
      index message witness := by
  rcases GroupedBalancedUpperPathFault67.recover_full_index_canonical_or_fault
    hash secretKey base height index message witness accepted with
    canonical | bad
  · have values : GroupedBalancedUpperIndex67.witnessValues witness =
        signValues hash secretKey base
          (GroupedBottomTree.selectedLeafAddress height
            (index / 2 ^ height) index) message := by
      funext chain
      simpa only [GroupedBottomTree.selectedLeafAddress_index] using
        canonical chain
    rcases recover_exact_given_values_or_merkle_bad hash secretKey base
      message height (index / 2 ^ height) index witness accepted values with
      exactWitness | merkle
    · exact Or.inl exactWitness
    · exact Or.inr (Or.inl merkle)
  · exact Or.inr bad

end SigGolfCandidate.Hypertree.GroupedBalancedUpperCanonicalOrBad67

end

/-! In an accepted, contact-free path, all upper witnesses are byte-for-byte
the honest witnesses for the canonical incoming digest. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPathCanonicalOrFault67
open SigGolf SigGolfCandidate.Hypertree
open GroupedBalancedScheme67 GroupedBalancedMixedPathFault67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem path_exact_no_fault (hash : Hash) (secretKey : SecretKey)
    (heights : List Nat) (base index : Nat)
    (expected actual : Reference.Digest)
    (witnesses : UpperWitnesses heights)
    (accepted : recoverLayers hash heights base index actual witnesses =
      rootsAfter hash secretKey heights base index expected)
    (clean : ¬PathFault hash secretKey heights base index
      expected actual witnesses) :
    actual = expected ∧
      witnesses = signLayers hash secretKey heights base index expected := by
  induction heights generalizing base index expected actual with
  | nil =>
      cases witnesses
      exact ⟨accepted, rfl⟩
  | cons height rest ih =>
      cases witnesses with
      | cons head tail =>
          let tree := index / 2 ^ height
          let actualRoot := GroupedBalancedUpperTree67.recover hash base
            height tree index actual head
          let canonicalRoot := GroupedBalancedUpperTree67.root hash
            secretKey base height tree
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
          obtain ⟨actualRootEq, tailExact⟩ := ih (base + height) tree
            canonicalRoot actualRoot tail tailAccepted cleanTail
          have actualEq : actual = expected :=
            path_binding_no_fault hash secretKey (height :: rest) base index
              expected actual (.cons head tail) accepted clean
          have headRoot : GroupedBalancedUpperTree67.recover hash base
              height tree index expected head = canonicalRoot := by
            rw [← actualEq]
            exact actualRootEq
          rcases GroupedBalancedUpperCanonicalOrBad67.recover_full_index_canonical_or_bad
            hash secretKey base height index expected head headRoot with
            headExact | headBad
          · refine ⟨actualEq, ?_⟩
            simp only [signLayers]
            rw [headExact,
              GroupedBalancedUpperTree67.build_root hash secretKey base
                height tree index expected]
            exact congrArg (UpperWitnesses.cons
              (GroupedBalancedUpperTree67.build hash secretKey base
                height tree index expected).witness) tailExact
          · exact False.elim (clean (by
              change GroupedBalancedUpperPathFault67.Bad hash secretKey
                  base height index actual head ∨ _ ∨ _
              exact Or.inl (actualEq ▸ headBad)))

end SigGolfCandidate.Hypertree.GroupedBalancedPathCanonicalOrFault67
