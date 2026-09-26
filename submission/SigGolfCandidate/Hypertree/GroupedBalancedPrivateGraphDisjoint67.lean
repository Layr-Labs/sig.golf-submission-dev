import SigGolfCandidate.Hypertree.GroupedBalancedPrivateDerivation67
import SigGolfCandidate.Hypertree.GroupedBalancedSecurityGraph67

/-! Every grouped private derivation input lies outside the public graph's
tag-2/3/4 address domain, regardless of payload bytes. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedPrivateGraphDisjoint67
open SigGolf SigGolfCandidate.Hypertree Reference SecurityGraph

private theorem private_tag_disjoint (address : Address)
    (tag : address.tag.val = 1 ∨ address.tag.val = 6)
    (position : GroupedBalancedSecurityGraph67.Position)
    (privatePayload publicPayload : List Byte) :
    address.input privatePayload ≠ position.input publicPayload := by
  intro same
  have addressEq : address = position.val := Address.eq_of_input_eq same
  have tags := congrArg (fun value : Address => value.tag.val) addressEq
  rcases tag with source | nonce <;>
    rcases position.property with chain | leaf | node <;> omega

theorem input_ne_public_graph (secretKey : SecretKey)
    (slot : GroupedBalancedPrivateDerivation67.Slot)
    (position : GroupedBalancedSecurityGraph67.Position) (payload : List Byte) :
    GroupedBalancedPrivateDerivation67.input secretKey slot ≠ position.input payload := by
  cases slot with
  | bottom index =>
      change GroupedBottomIndex.sourceInput secretKey index ≠ position.input payload
      rw [← GroupedBottomIndex.source_address_input]
      exact private_tag_disjoint (GroupedBottomIndex.sourceAddress index)
        (Or.inl rfl) position (bytes secretKey) payload
  | upper base leaf pair =>
      change GroupedBalancedAddressDomains67.upperInput secretKey
        (GroupedBalancedPrivateDerivation67.baseLevel base) leaf pair ≠ position.input payload
      rw [← GroupedBalancedAddressDomains67.upper_address_input]
      exact private_tag_disjoint
        (GroupedBalancedAddressDomains67.upperAddress
          (GroupedBalancedPrivateDerivation67.baseLevel base) leaf pair)
        (Or.inl rfl) position (bytes secretKey) payload
  | randomizer message =>
      change SecurityRandomOracle.randomizerInput secretKey message ≠
        position.input payload
      change (⟨6, 0, 0, 0, 0, 0⟩ : Address).input
        (bytes secretKey ++ bytes message) ≠ position.input payload
      exact private_tag_disjoint (⟨6, 0, 0, 0, 0, 0⟩ : Address)
        (Or.inr rfl) position (bytes secretKey ++ bytes message) payload

end SigGolfCandidate.Hypertree.GroupedBalancedPrivateGraphDisjoint67
