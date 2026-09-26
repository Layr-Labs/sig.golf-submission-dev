import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.Hypertree.GroupedBottomTree

/-! The WOTS witness selected in a grouped upper tree belongs to the exact
current index, when the builder is rooted at that index's quotient tree. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperIndex67
open SigGolf SigGolfCandidate.Hypertree Reference

def witnessValues : {height : Nat} → GroupedBalancedUpperTree67.Witness height →
    GroupedBalancedUpperTree67.ChainMixed → Digest
  | 0, .leaf values => values
  | _ + 1, .step inner _ => witnessValues inner

theorem build_witness_values (hash : Hash) (secretKey : SecretKey)
    (base height address index : Nat) (message : Digest) :
    witnessValues (GroupedBalancedUpperTree67.build hash secretKey base height address index message).witness =
      GroupedBalancedUpperTree67.signValues hash secretKey base
        (GroupedBottomTree.selectedLeafAddress height address index) message := by
  induction height generalizing address with
  | zero => rfl
  | succ height ih =>
      by_cases bit : index / 2 ^ height % 2 = 0
      · simp only [GroupedBalancedUpperTree67.build, witnessValues,
          GroupedBottomTree.selectedLeafAddress, if_pos bit]
        exact ih (2 * address)
      · simp only [GroupedBalancedUpperTree67.build, witnessValues,
          GroupedBottomTree.selectedLeafAddress, if_neg bit]
        exact ih (2 * address + 1)

theorem build_witness_values_at_index (hash : Hash) (secretKey : SecretKey)
    (base height index : Nat) (message : Digest) :
    witnessValues
      (GroupedBalancedUpperTree67.build hash secretKey base height (index / 2 ^ height)
        index message).witness =
      GroupedBalancedUpperTree67.signValues hash secretKey base index message := by
  rw [build_witness_values, GroupedBottomTree.selectedLeafAddress_index]

end SigGolfCandidate.Hypertree.GroupedBalancedUpperIndex67
