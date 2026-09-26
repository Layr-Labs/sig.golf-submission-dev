import SigGolfCandidate.Hypertree.GroupedPrivateDerivation
import SigGolfCandidate.Hypertree.GroupedSecurityGraph
import SigGolfCandidate.Hypertree.GroupedBalancedPrivateGraphDisjoint67


/-! Every grouped private derivation input lies outside the public graph's
tag-2/3/4 address domain, regardless of payload bytes. -/

namespace SigGolfCandidate.Hypertree.GroupedPrivateGraphDisjoint
open SigGolf SigGolfCandidate.Hypertree Reference SecurityGraph

private theorem private_tag_disjoint (address : Address)
    (tag : address.tag.val = 1 ∨ address.tag.val = 6)
    (position : GroupedSecurityGraph.Position)
    (privatePayload publicPayload : List Byte) :
    address.input privatePayload ≠ position.input publicPayload := by
  intro same
  have addressEq : address = position.val := Address.eq_of_input_eq same
  have tags := congrArg (fun value : Address => value.tag.val) addressEq
  rcases tag with source | nonce <;>
    rcases position.property with chain | leaf | node <;> omega

theorem input_ne_public_graph (secretKey : SecretKey)
    (slot : GroupedPrivateDerivation.Slot)
    (position : GroupedSecurityGraph.Position) (payload : List Byte) :
    GroupedPrivateDerivation.input secretKey slot ≠ position.input payload := by
  cases slot with
  | bottom index =>
      change GroupedBottomIndex.sourceInput secretKey index ≠ position.input payload
      rw [← GroupedBottomIndex.source_address_input]
      exact private_tag_disjoint (GroupedBottomIndex.sourceAddress index)
        (Or.inl rfl) position (bytes secretKey) payload
  | upper base leaf pair =>
      change GroupedAddressDomains.upperInput secretKey
        (GroupedPrivateDerivation.baseLevel base) leaf pair ≠ position.input payload
      rw [← GroupedAddressDomains.upper_address_input]
      exact private_tag_disjoint
        (GroupedAddressDomains.upperAddress
          (GroupedPrivateDerivation.baseLevel base) leaf pair)
        (Or.inl rfl) position (bytes secretKey) payload
  | randomizer message =>
      change SecurityRandomOracle.randomizerInput secretKey message ≠
        position.input payload
      change (⟨6, 0, 0, 0, 0, 0⟩ : Address).input
        (bytes secretKey ++ bytes message) ≠ position.input payload
      exact private_tag_disjoint (⟨6, 0, 0, 0, 0, 0⟩ : Address)
        (Or.inr rfl) position (bytes secretKey ++ bytes message) payload

end SigGolfCandidate.Hypertree.GroupedPrivateGraphDisjoint



/-! Plant one full-width output at each canonical grouped public graph input.
Private slot inputs remain exactly as in the residual oracle, independently of
the chosen graph payload recursion. -/

namespace SigGolfCandidate.Hypertree.GroupedGraphProgramming
open SigGolf SigGolfCandidate.Hypertree Reference GroupedSecurityGraph
open scoped Classical

noncomputable def programmed (payload : Position → List Byte)
    (labels : Labels) (residual : Hash) : Hash :=
  fun query => if found : ∃ position, position.input (payload position) = query
    then labels found.choose else residual query

theorem programmed_graph (payload : Position → List Byte)
    (labels : Labels) (residual : Hash) (position : Position) :
    programmed payload labels residual (position.input (payload position)) =
      labels position := by
  unfold programmed
  split
  next found =>
    have same : found.choose = position := by
      by_contra different
      exact Position.input_separated found.choose position different
        (payload found.choose) (payload position) found.choose_spec
    rw [same]
  next absent => exact False.elim (absent ⟨position, rfl⟩)

theorem programmed_private (payload : Position → List Byte)
    (labels : Labels) (residual : Hash) (secretKey : SecretKey)
    (slot : GroupedPrivateDerivation.Slot) :
    programmed payload labels residual
      (GroupedPrivateDerivation.input secretKey slot) =
      residual (GroupedPrivateDerivation.input secretKey slot) := by
  unfold programmed
  split
  next found =>
    obtain ⟨position, same⟩ := found
    exact False.elim ((GroupedPrivateGraphDisjoint.input_ne_public_graph
      secretKey slot position (payload position)) same.symm)
  next absent => rfl

end SigGolfCandidate.Hypertree.GroupedGraphProgramming


/-! The common public graph oracle planter preserves all 67-chain private
source queries because their concrete tags lie outside the public graph. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphProgramming67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedSecurityGraph67

noncomputable def programmed (payload : Position → List Byte)
    (labels : Labels) (residual : Hash) : Hash :=
  GroupedGraphProgramming.programmed payload labels residual

theorem programmed_graph (payload : Position → List Byte)
    (labels : Labels) (residual : Hash) (position : Position) :
    programmed payload labels residual
      (position.input (payload position)) = labels position :=
  GroupedGraphProgramming.programmed_graph payload labels residual position

theorem programmed_private (payload : Position → List Byte)
    (labels : Labels) (residual : Hash) (secretKey : SecretKey)
    (slot : GroupedBalancedPrivateDerivation67.Slot) :
    programmed payload labels residual
      (GroupedBalancedPrivateDerivation67.input secretKey slot) =
      residual (GroupedBalancedPrivateDerivation67.input secretKey slot) := by
  unfold programmed GroupedGraphProgramming.programmed
  split
  next found =>
    obtain ⟨position, same⟩ := found
    exact False.elim
      ((GroupedBalancedPrivateGraphDisjoint67.input_ne_public_graph
        secretKey slot position (payload position)) same.symm)
  next absent => rfl

end SigGolfCandidate.Hypertree.GroupedBalancedGraphProgramming67
