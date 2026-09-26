import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRecoverRecurrence67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomIndexArithmetic67

/-! A ten-level root recurrence matching the order of the verifier H4 loop. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootAt67
open SigGolf SigGolfCandidate.Hypertree Reference
open GroupedBalancedVerifyBottomRecoverRecurrence67

def stateAt (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10) (k : Nat) : Nat × Digest :=
  ((siblings witness).take k).foldl (foldStep hash index.toNat)
    (0,GroupedBottomTree.leafFromSeed hash index.toNat witness.seedValue)

def rootAt (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10) (k : Nat) : Digest :=
  (stateAt hash index witness k).2

theorem stateAt_succ (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (k : Nat) (hk : k < 10) :
    stateAt hash index witness (k+1) =
      foldStep hash index.toNat (stateAt hash index witness k)
        ((siblings witness)[k]'(by simpa [siblings_length] using hk)) := by
  unfold stateAt
  rw [List.take_succ_eq_append_getElem (by simpa [siblings_length] using hk)]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem stateAt_level (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (k : Nat) (hk : k ≤ 10) :
    (stateAt hash index witness k).1 = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have klt : k < 10 := by omega
      rw [stateAt_succ hash index witness k klt]
      simp only [foldStep, ih (by omega)]

theorem rootAt_zero (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10) :
    rootAt hash index witness 0 =
      GroupedBottomTree.leafFromSeed hash index.toNat witness.seedValue := rfl

theorem rootAt_succ (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (k : Nat) (hk : k < 10) :
    rootAt hash index witness (k+1) =
      if index.toNat / 2^k % 2 = 0 then
        Reference.node hash k (index.toNat / 2^(k+1))
          (rootAt hash index witness k)
          ((siblings witness)[k]'(by simpa [siblings_length] using hk))
      else
        Reference.node hash k (index.toNat / 2^(k+1))
          ((siblings witness)[k]'(by simpa [siblings_length] using hk))
          (rootAt hash index witness k) := by
  unfold rootAt
  rw [stateAt_succ hash index witness k hk]
  simp only [foldStep,stateAt_level hash index witness k (by omega)]

theorem rootAt_ten (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10) :
    rootAt hash index witness 10 =
      GroupedBottomTree.recover hash 10
        (GroupedMixedIndex.bottomTree index) index.toNat witness := by
  have all : (siblings witness).take 10 = siblings witness := by
    apply List.take_of_length_le
    simpa [siblings_length]
  unfold rootAt stateAt
  rw [all]
  exact (recover_ten_steps hash index witness).2.symm

theorem rootAt_succ_machine (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10)
    (k : Nat) (hk : k < 10) :
    rootAt hash index witness (k+1) =
      Reference.node hash k (index.toNat / 2^(k+1))
        (if (BitVec.extractLsb' 0 64
            (GroupedBalancedVerifyBottomIndexArithmetic67.wide index >>> k)
              &&& (1 : BitVec 64)) = 0 then
          rootAt hash index witness k
        else (siblings witness)[k]'(by simpa [siblings_length] using hk))
        (if (BitVec.extractLsb' 0 64
            (GroupedBalancedVerifyBottomIndexArithmetic67.wide index >>> k)
              &&& (1 : BitVec 64)) = 0 then
          (siblings witness)[k]'(by simpa [siblings_length] using hk)
        else rootAt hash index witness k) := by
  rw [rootAt_succ hash index witness k hk]
  by_cases side : index.toNat / 2^k % 2 = 0
  · have side' :=
      (GroupedBalancedVerifyBottomIndexArithmetic67.bit_zero_iff index k).2 side
    rw [if_pos side', if_pos side']
    simp [side]
  · have side' :=
      (GroupedBalancedVerifyBottomIndexArithmetic67.bit_zero_iff index k).not.mpr side
    rw [if_neg side', if_neg side']
    simp [side]

#print axioms rootAt_succ
#print axioms rootAt_ten
#print axioms rootAt_succ_machine
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRootAt67
