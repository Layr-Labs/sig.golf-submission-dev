import SigGolfCandidate.Hypertree.GroupedBalancedPathCanonicalOrFault67
import SigGolfCandidate.Hypertree.GroupedBottomExtraction

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBottomCanonicalOrBad67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignatureReplay67. -/
section
/-! Strong bottom-tree binding: an accepted witness is the complete honest
authentication witness, or one of its actual queries is a truncated-hash
collision. -/

namespace SigGolfCandidate.Hypertree.GroupedBottomCanonicalOrBad67
open SigGolf SigGolfCandidate.Hypertree
open GroupedBottomTree GroupedBottomExtraction
set_option maxRecDepth 8192

theorem recover_canonical_or_bad (hash : Hash) (secretKey : SecretKey)
    (height address index : Nat) (witness : Witness height)
    (accepted : recover hash height address index witness =
      root hash secretKey height address) :
    witness = (build hash secretKey height address index).witness ∨
      Bad hash secretKey height address index witness := by
  induction height generalizing address with
  | zero =>
      cases witness with
      | seed seed =>
          by_cases seedEq : seed = secret hash secretKey address
          · left
            simpa only [build] using congrArg Witness.seed seedEq
          · right
            exact ⟨seedEq, accepted⟩
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
              rcases ih (2 * address) inner childRoot with canonical | bad
              · left
                have siblingEq := congrArg Prod.snd samePair
                have siblingValue : sibling =
                    root hash secretKey height (2 * address + 1) := by
                  simpa only using siblingEq
                simp only [build, if_pos bit]
                rw [canonical, siblingValue,
                  GroupedBottomTree.build_root hash secretKey height
                    (2 * address + 1) index]
              · right
                simp only [Bad, if_pos bit]
                exact Or.inr bad
            · right
              simp only [Bad, if_pos bit]
              exact Or.inl ⟨samePair, sameRoot⟩
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
              rcases ih (2 * address + 1) inner childRoot with canonical | bad
              · left
                have siblingEq := congrArg Prod.fst samePair
                have siblingValue : sibling =
                    root hash secretKey height (2 * address) := by
                  simpa only using siblingEq
                simp only [build, if_neg bit]
                rw [canonical, siblingValue,
                  GroupedBottomTree.build_root hash secretKey height
                    (2 * address) index]
              · right
                simp only [Bad, if_neg bit]
                exact Or.inr bad
            · right
              simp only [Bad, if_neg bit]
              exact Or.inl ⟨samePair, sameRoot⟩

end SigGolfCandidate.Hypertree.GroupedBottomCanonicalOrBad67
end

/-! An accepted structured signature at one fixed index has exactly the
canonical bottom and upper witnesses unless a concrete path fault occurs. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignatureCanonicalOrFault67
open SigGolf SigGolfCandidate.Hypertree
open GroupedBalancedScheme67 GroupedBalancedMixedPathFault67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem accepted_canonical_or_fault (hash : Hash) (secretKey : SecretKey)
    (index : BitVec 160) (signature : GroupedBalancedScheme67.Signature)
    (accepted : recoverLayers hash Heights 10
      (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper = GroupedBalancedScheme67.keygen hash secretKey) :
    UpperFault hash secretKey index signature ∨
    GroupedBottomExtraction.Bad hash secretKey 10
      (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom ∨
    (signature.bottom =
        (GroupedBottomTree.build hash secretKey 10
          (GroupedMixedIndex.bottomTree index) index.toNat).witness ∧
      signature.upper = signLayers hash secretKey Heights 10
        (GroupedMixedIndex.bottomTree index)
        (GroupedBottomTree.root hash secretKey 10
          (GroupedMixedIndex.bottomTree index))) := by
  by_cases upper : UpperFault hash secretKey index signature
  · exact Or.inl upper
  · have target : rootsAfter hash secretKey Heights 10
        (GroupedMixedIndex.bottomTree index)
        (GroupedBottomTree.root hash secretKey 10
          (GroupedMixedIndex.bottomTree index)) =
        GroupedBalancedScheme67.keygen hash secretKey := by
      simpa only [GroupedBalancedScheme67.keygen] using final_root hash secretKey index
        (GroupedBottomTree.root hash secretKey 10
          (GroupedMixedIndex.bottomTree index))
    have path := GroupedBalancedPathCanonicalOrFault67.path_exact_no_fault
      hash secretKey Heights 10 (GroupedMixedIndex.bottomTree index)
      (GroupedBottomTree.root hash secretKey 10
        (GroupedMixedIndex.bottomTree index))
      (GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree index) index.toNat signature.bottom)
      signature.upper (accepted.trans target.symm) upper
    rcases GroupedBottomCanonicalOrBad67.recover_canonical_or_bad hash
      secretKey 10 (GroupedMixedIndex.bottomTree index) index.toNat
      signature.bottom path.1 with exactBottom | bottomBad
    · exact Or.inr (Or.inr ⟨exactBottom, path.2⟩)
    · exact Or.inr (Or.inl bottomBad)

end SigGolfCandidate.Hypertree.GroupedBalancedSignatureCanonicalOrFault67


/-! With the honest randomizer, an accepted signature is the exact honest
signature unless its bottom or upper path has a collision fault. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignatureReplay67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedScheme67 GroupedBalancedMixedPathFault67
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem accepted_same_randomizer_exact_or_fault
    (hash : Hash) (secretKey : SecretKey) (message : Message)
    (signature : GroupedBalancedScheme67.Signature)
    (randomizerEq : signature.randomizer =
      Reference.randomizer hash secretKey message)
    (accepted : GroupedBalancedScheme67.verify hash
      (GroupedBalancedScheme67.keygen hash secretKey)
      message signature) :
    UpperFault hash secretKey
        (Reference.indexOf hash message signature.randomizer) signature ∨
    GroupedBottomExtraction.Bad hash secretKey 10
      (GroupedMixedIndex.bottomTree
        (Reference.indexOf hash message signature.randomizer))
      (Reference.indexOf hash message signature.randomizer).toNat
      signature.bottom ∨
    signature = GroupedBalancedScheme67.sign hash secretKey message := by
  let index := Reference.indexOf hash message signature.randomizer
  rcases GroupedBalancedSignatureCanonicalOrFault67.accepted_canonical_or_fault
    hash secretKey index signature (by
      simpa only [GroupedBalancedScheme67.verify, index] using accepted) with
    upper | bottom | exactWitness
  · exact Or.inl upper
  · exact Or.inr (Or.inl bottom)
  · right
    right
    obtain ⟨bottomEq, upperEq⟩ := exactWitness
    have indexEq : index = Reference.indexOf hash message
        (Reference.randomizer hash secretKey message) := by
      simp only [index, randomizerEq]
    cases signature with
    | mk randomizer bottom upper =>
        simp only [GroupedBalancedScheme67.sign] at *
        subst randomizer
        rw [indexEq] at bottomEq upperEq
        have rootEq :
            (GroupedBottomTree.build hash secretKey 10
              (GroupedMixedIndex.bottomTree
                (Reference.indexOf hash message
                  (Reference.randomizer hash secretKey message)))
              (Reference.indexOf hash message
                (Reference.randomizer hash secretKey message)).toNat).root =
            GroupedBottomTree.root hash secretKey 10
              (GroupedMixedIndex.bottomTree
                (Reference.indexOf hash message
                  (Reference.randomizer hash secretKey message))) :=
          GroupedBottomTree.build_root hash secretKey 10 _ _
        rw [rootEq]
        cases bottomEq
        cases upperEq
        rfl

end SigGolfCandidate.Hypertree.GroupedBalancedSignatureReplay67
