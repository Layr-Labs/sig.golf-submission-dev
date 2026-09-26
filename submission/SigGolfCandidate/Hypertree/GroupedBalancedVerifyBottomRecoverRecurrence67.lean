import SigGolfCandidate.Hypertree.GroupedBottomTree
import SigGolfCandidate.Hypertree.GroupedMixedIndex

/-! The bottom authentication witness is a ten-step, bottom-up node fold. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRecoverRecurrence67
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 8192

def siblings : {height : Nat} → GroupedBottomTree.Witness height → List Digest
  | 0, .seed _ => []
  | _ + 1, .step inner sibling => siblings inner ++ [sibling]

def foldStep (hash : Hash) (index : Nat)
    (state : Nat × Digest) (sibling : Digest) : Nat × Digest :=
  let level := state.1
  let current := state.2
  (level + 1,
    if index / 2 ^ level % 2 = 0 then
      Reference.node hash level (index / 2 ^ (level + 1))
        current sibling
    else
      Reference.node hash level (index / 2 ^ (level + 1))
        sibling current)

private theorem child_address (index height : Nat) :
    (index / 2 ^ height % 2 = 0 →
      index / 2 ^ height = 2 * (index / 2 ^ (height + 1))) ∧
    (index / 2 ^ height % 2 ≠ 0 →
      index / 2 ^ height = 2 * (index / 2 ^ (height + 1)) + 1) := by
  have div : (index / 2 ^ height) / 2 =
      index / 2 ^ (height + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have recompose := Nat.mod_add_div (index / 2 ^ height) 2
  have small := Nat.mod_lt (index / 2 ^ height) (by decide : 0 < 2)
  constructor <;> intro bit <;> omega

theorem fold_recover (hash : Hash) (index : Nat)
    {height : Nat} (witness : GroupedBottomTree.Witness height) :
    (siblings witness).foldl (foldStep hash index)
      (0,GroupedBottomTree.leafFromSeed hash index witness.seedValue) =
    (height,GroupedBottomTree.recover hash height
      (index / 2 ^ height) index witness) := by
  induction witness with
  | seed seed =>
      simp [siblings,GroupedBottomTree.Witness.seedValue,
        GroupedBottomTree.recover]
  | @step height inner sibling ih =>
      simp only [siblings, List.foldl_append, List.foldl_cons,
        List.foldl_nil, GroupedBottomTree.Witness.seedValue]
      rw [ih]
      simp only [foldStep, GroupedBottomTree.recover]
      by_cases bit : index / 2 ^ height % 2 = 0
      · rw [if_pos bit, if_pos bit]
        rw [(child_address index height).1 bit]
        rfl
      · rw [if_neg bit, if_neg bit]
        rw [(child_address index height).2 bit]
        rfl

theorem siblings_length {height : Nat}
    (witness : GroupedBottomTree.Witness height) :
    (siblings witness).length = height := by
  induction witness with
  | seed _ => rfl
  | step inner sibling ih =>
      simp [siblings,ih]

theorem recover_ten_steps (hash : Hash) (index : BitVec 160)
    (witness : GroupedBottomTree.Witness 10) :
    (siblings witness).length = 10 ∧
    GroupedBottomTree.recover hash 10
      (GroupedMixedIndex.bottomTree index) index.toNat witness =
      ((siblings witness).foldl (foldStep hash index.toNat)
        (0,GroupedBottomTree.leafFromSeed hash index.toNat
          witness.seedValue)).2 := by
  constructor
  · exact siblings_length witness
  · have folded := fold_recover hash index.toNat witness
    simpa only [GroupedMixedIndex.bottomTree] using
      (congrArg Prod.snd folded.symm)

#print axioms recover_ten_steps
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomRecoverRecurrence67
