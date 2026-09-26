import SigGolfCandidate.Hypertree.GroupedBalancedQueryClasses67

/-! Each direct67 bottom, paired upper, or randomizer source input is an
eligible legacy secret-key query. Thus the shared secret-key query meter covers
every concrete private-source guess made against this construction. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPrivateLegacyEligible67
open SigGolf SigGolfCandidate.Hypertree OracleSpec Reference
open GroupedBalancedPrivateDerivation67
open SecurityRandomOracle
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem bottom_legacy_input (secretKey : SecretKey)
    (index : BitVec 160) :
    GroupedBalancedPrivateDerivation67.input secretKey (.bottom index) =
      SecurityDerivation.input secretKey
        (.chain ⟨0, BitVec.ofNat 192 index.toNat, false, 0⟩) := by
  change GroupedBottomIndex.sourceInput secretKey index =
    addressedInput 1 0 ((BitVec.ofNat 192 index.toNat).toNat) 0 0 0
      (bytes secretKey)
  simp only [GroupedBottomIndex.sourceInput, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field index)]

theorem upper_legacy_input (secretKey : SecretKey)
    (base : Fin 150) (leaf : BitVec 160) (pair : Fin 34) :
    GroupedBalancedPrivateDerivation67.input secretKey
      (.upper base leaf pair) =
      SecurityDerivation.input secretKey
        (.chain ⟨GroupedBalancedPrivateDerivation67.baseLevel base,
          BitVec.ofNat 192 leaf.toNat, false,
          ⟨pair.val, by have := pair.isLt; omega⟩⟩) := by
  change GroupedBalancedAddressDomains67.upperInput secretKey
      (GroupedBalancedPrivateDerivation67.baseLevel base) leaf pair =
    addressedInput 1
      (GroupedBalancedPrivateDerivation67.baseLevel base).val
      ((BitVec.ofNat 192 leaf.toNat).toNat) 0 pair.val 0
      (bytes secretKey)
  simp only [GroupedBalancedAddressDomains67.upperInput,
    BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (GroupedBottomIndex.index_fits_tree_field leaf)]

theorem eligible_of_direct (secretKey : SecretKey)
    (slot : GroupedBalancedPrivateDerivation67.Slot) :
    SecuritySeparation.SecretKeyEligible
      (GroupedBalancedPrivateDerivation67.input secretKey slot) := by
  cases slot with
  | bottom index =>
      refine ⟨secretKey,
        .chain ⟨0, BitVec.ofNat 192 index.toNat, false, 0⟩, ?_⟩
      exact (bottom_legacy_input secretKey index).symm
  | upper base leaf pair =>
      refine ⟨secretKey,
        .chain ⟨GroupedBalancedPrivateDerivation67.baseLevel base,
          BitVec.ofNat 192 leaf.toNat, false,
          ⟨pair.val, by have := pair.isLt; omega⟩⟩, ?_⟩
      exact (upper_legacy_input secretKey base leaf pair).symm
  | randomizer message =>
      exact ⟨secretKey, .randomizer message, rfl⟩

theorem direct_eligible_implies_legacy (query : Query)
    (direct : GroupedBalancedQueryClasses67.SecretKeyEligible query) :
    SecuritySeparation.SecretKeyEligible query := by
  obtain ⟨secretKey, slot, same⟩ := direct
  rw [← same]
  exact eligible_of_direct secretKey slot

#print axioms eligible_of_direct
#print axioms direct_eligible_implies_legacy

end SigGolfCandidate.Hypertree.GroupedBalancedPrivateLegacyEligible67
