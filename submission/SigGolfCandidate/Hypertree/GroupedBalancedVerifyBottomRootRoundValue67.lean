import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootAt67

/-! The machine H4 query value is the next bottom authentication root. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootRoundValue67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedVerifyBottomRecoverRecurrence67
private abbrev wide := GroupedBalancedVerifyBottomIndexArithmetic67.wide
private abbrev rootAt := GroupedBalancedVerifyBottomRootAt67.rootAt
private abbrev siblings (witness : GroupedBottomTree.Witness 10) :=
  GroupedBalancedVerifyBottomRecoverRecurrence67.siblings witness

theorem round_value (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (k : Nat) (hk : k < 10) :
    Reference.node hash k (((wide index >>> k) >>> 1).toNat)
      (if ((wide index >>> k).extractLsb' 0 64 &&& (1 : BitVec 64)) = 0 then
        rootAt hash index witness k
       else (siblings witness)[k]'(by simpa [siblings_length] using hk))
      (if ((wide index >>> k).extractLsb' 0 64 &&& (1 : BitVec 64)) = 0 then
        (siblings witness)[k]'(by simpa [siblings_length] using hk)
       else rootAt hash index witness k) =
      rootAt hash index witness (k+1) := by
  have recurrence :=
    GroupedBalancedVerifyBottomRootAt67.rootAt_succ_machine
      hash index witness k hk
  rw [GroupedBalancedVerifyBottomIndexArithmetic67.shifted_parent index k]
  exact recurrence.symm

#print axioms round_value
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootRoundValue67
