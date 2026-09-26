import SigGolfCandidate.Hypertree.GroupedBalancedGraphPayload67
import Mathlib.Data.List.Sort

/-! A small topological rank for the grouped public oracle graph. Bottom
leaves and paired chain starts have rank zero. All canonical dependencies
strictly precede the query that consumes them, and every rank is at most fourteen.
-/

namespace SigGolfCandidate.Hypertree.GroupedBalancedGraphOrder67
open SigGolf GroupedBalancedSecurityGraph67 GroupedBalancedGraphPayload67

private def addressCoordinates (address : SecurityGraph.Address) :
    Fin 256 × Fin 256 × BitVec 192 × Fin 256 × Fin 256 × Fin 256 :=
  (address.tag, address.level, address.tree,
    address.leaf, address.chain, address.step)

private theorem addressCoordinates_injective : Function.Injective addressCoordinates := by
  intro first second same
  cases first
  cases second
  simp only [addressCoordinates, Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

instance : Finite SecurityGraph.Address :=
  Finite.of_injective addressCoordinates addressCoordinates_injective

instance : Finite Position := Finite.of_injective Subtype.val Subtype.val_injective
noncomputable instance : Fintype Position := Fintype.ofFinite Position

theorem groupBase_bounds (level : Nat) (low : 10 ≤ level) (high : level < 160) :
    GroupedBalancedGraphPayload67.groupBase level ≤ level ∧ level < GroupedBalancedGraphPayload67.groupBase level + 4 := by
  by_cases below : level < 100
  · have remainder := Nat.mod_add_div (level - 10) 3
    have small := Nat.mod_lt (level - 10) (by decide : 0 < 3)
    simp only [GroupedBalancedGraphPayload67.groupBase, if_pos below]
    omega
  · have remainder := Nat.mod_add_div (level - 100) 4
    have small := Nat.mod_lt (level - 100) (by decide : 0 < 4)
    simp only [GroupedBalancedGraphPayload67.groupBase, if_neg below]
    omega

theorem groupBase_previous (level : Nat) (low : 10 < level) (high : level < 160)
    (notBase : GroupedBalancedGraphPayload67.groupBase level ≠ level) :
    GroupedBalancedGraphPayload67.groupBase (level - 1) = GroupedBalancedGraphPayload67.groupBase level := by
  by_cases below : level < 100
  · have previousBelow : level - 1 < 100 := by omega
    have remainder := Nat.mod_add_div (level - 10) 3
    have previousRemainder := Nat.mod_add_div (level - 1 - 10) 3
    have small := Nat.mod_lt (level - 10) (by decide : 0 < 3)
    have previousSmall := Nat.mod_lt (level - 1 - 10) (by decide : 0 < 3)
    simp only [GroupedBalancedGraphPayload67.groupBase, if_pos below] at notBase
    simp only [GroupedBalancedGraphPayload67.groupBase, if_pos previousBelow, if_pos below]
    omega
  · have strict : 100 < level := by
      by_contra notStrict
      have same : level = 100 := by omega
      subst level
      exact notBase (by decide)
    have previousHigh : ¬ level - 1 < 100 := by omega
    have remainder := Nat.mod_add_div (level - 100) 4
    have previousRemainder := Nat.mod_add_div (level - 1 - 100) 4
    have small := Nat.mod_lt (level - 100) (by decide : 0 < 4)
    have previousSmall := Nat.mod_lt (level - 1 - 100) (by decide : 0 < 4)
    simp only [GroupedBalancedGraphPayload67.groupBase, if_neg below] at notBase
    simp only [GroupedBalancedGraphPayload67.groupBase, if_neg previousHigh, if_neg below]
    omega

def rank (position : Position) : Nat :=
  let address := position.val
  if address.tag.val = 2 then min address.step.val 9
  else if address.tag.val = 3 then 10
  else if address.level.val < 10 then address.level.val + 1
  else if address.level.val < 160 then
    11 + address.level.val - GroupedBalancedGraphPayload67.groupBase address.level.val
  else 0

theorem rank_le_fourteen (position : Position) : rank position ≤ 14 := by
  simp only [rank]
  split_ifs with htagTwo htagThree hlevelLow hlevelHigh
  · omega
  · omega
  · omega
  · have bound := groupBase_bounds position.val.level.val (by omega) hlevelHigh
    omega
  · omega

theorem bottom_leaf_rank (index : BitVec 160) : rank (bottomLeaf index) = 0 := by
  simp [rank, bottomLeaf]

theorem bottom_node_rank (level : Fin 10) (tree : BitVec 160) :
    rank (bottomNode level tree) = level.val + 1 := by
  have := level.isLt
  simp [rank, bottomNode, show level.val < 10 by omega]

theorem upper_chain_rank (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (step : Fin 10) :
    rank (upperChain base leaf chain step) = step.val := by
  have := step.isLt
  simp [rank, upperChain]
  omega

theorem upper_leaf_rank (base : Fin 150) (leaf : BitVec 160) :
    rank (upperLeaf base leaf) = 10 := by
  simp [rank, upperLeaf]

theorem upper_node_rank (level : Fin 150) (tree : BitVec 160) :
    rank (upperNode level tree) =
      11 + (level.val + 10) - GroupedBalancedGraphPayload67.groupBase (level.val + 10) := by
  have high : level.val + 10 < 160 := by have := level.isLt; omega
  have low : ¬level.val + 10 < 10 := by omega
  simp [rank, upperNode, high, low]

theorem bottom_node_child_rank (level : Fin 10) (tree : BitVec 160) :
    rank (nodeChildren (bottomNode level tree).val).1 <
      rank (bottomNode level tree) ∧
    rank (nodeChildren (bottomNode level tree).val).2 <
      rank (bottomNode level tree) := by
  by_cases zero : level.val = 0
  · have same : level = 0 := Fin.ext zero
    subst level
    rw [bottom_node_zero_children]
    simp [bottom_leaf_rank, bottom_node_rank]
  · let previous : Fin 9 := ⟨level.val - 1, by have := level.isLt; omega⟩
    have same : (⟨previous.val + 1, by omega⟩ : Fin 10) = level := by
      apply Fin.ext
      dsimp [previous]
      omega
    conv_lhs => rw [← same]
    conv_rhs => rw [← same]
    rw [bottom_node_step_children]
    simp only [bottom_node_rank]
    dsimp [previous]
    omega

theorem upper_chain_previous_rank (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) (step : Fin 9) :
    rank (upperChain base leaf chain ⟨step.val, by omega⟩) <
      rank (upperChain base leaf chain ⟨step.val + 1, by omega⟩) := by
  rw [upper_chain_rank, upper_chain_rank]
  change step.val < step.val + 1
  omega

theorem upper_leaf_chain_rank (base : Fin 150) (leaf : BitVec 160)
    (chain : Fin 67) :
    rank (upperChain base leaf chain ⟨9, by decide⟩) <
      rank (upperLeaf base leaf) := by
  rw [upper_chain_rank, upper_leaf_rank]
  decide

theorem upper_node_at_base_child_rank (level : Fin 150) (tree : BitVec 160)
    (atBase : GroupedBalancedGraphPayload67.groupBase (level.val + 10) = level.val + 10) :
    rank (nodeChildren (upperNode level tree).val).1 <
      rank (upperNode level tree) ∧
    rank (nodeChildren (upperNode level tree).val).2 <
      rank (upperNode level tree) := by
  rw [upper_node_at_base_children level tree atBase]
  simp only [upper_leaf_rank, upper_node_rank]
  rw [atBase]
  omega

theorem upper_node_inner_child_rank (level : Fin 150) (tree : BitVec 160)
    (positive : 0 < level.val)
    (notBase : GroupedBalancedGraphPayload67.groupBase (level.val + 10) ≠ level.val + 10) :
    rank (nodeChildren (upperNode level tree).val).1 <
      rank (upperNode level tree) ∧
    rank (nodeChildren (upperNode level tree).val).2 <
      rank (upperNode level tree) := by
  have high : level.val + 10 < 160 := by have := level.isLt; omega
  have sameBase := groupBase_previous (level.val + 10) (by omega) high notBase
  rw [upper_node_inner_children level tree positive notBase]
  simp only [upper_node_rank]
  change
    11 + (level.val - 1 + 10) - GroupedBalancedGraphPayload67.groupBase (level.val - 1 + 10) <
      11 + (level.val + 10) - GroupedBalancedGraphPayload67.groupBase (level.val + 10) ∧
    11 + (level.val - 1 + 10) - GroupedBalancedGraphPayload67.groupBase (level.val - 1 + 10) <
      11 + (level.val + 10) - GroupedBalancedGraphPayload67.groupBase (level.val + 10)
  have previousArgument : level.val - 1 + 10 = level.val + 10 - 1 := by omega
  rw [previousArgument, sameBase]
  have bound := groupBase_bounds (level.val + 10) (by omega) high
  omega

theorem rank_tag_four (position : Position)
    (tagFour : position.val.tag.val = 4) :
    rank position =
      if position.val.level.val < 10 then position.val.level.val + 1
      else if position.val.level.val < 160 then
        11 + position.val.level.val - GroupedBalancedGraphPayload67.groupBase position.val.level.val
      else 0 := by
  have notTwo : position.val.tag.val ≠ 2 := by omega
  have notThree : position.val.tag.val ≠ 3 := by omega
  simp only [rank, notTwo, notThree, ↓reduceIte]

theorem node_children_rank (position : Position)
    (tagFour : position.val.tag.val = 4)
    (small : position.val.level.val < 160) :
    rank (nodeChildren position.val).1 < rank position ∧
    rank (nodeChildren position.val).2 < rank position := by
  have tagged : rank position =
      if position.val.level.val < 10 then position.val.level.val + 1
      else 11 + position.val.level.val - GroupedBalancedGraphPayload67.groupBase position.val.level.val := by
    rw [rank_tag_four position tagFour]
    simp [small]
  by_cases lower : position.val.level.val < 10
  · by_cases zero : position.val.level.val = 0
    ·
      simp only [nodeChildren, dif_pos lower, dif_pos zero, Prod.fst, Prod.snd]
      rw [tagged]
      simp [lower, zero, bottom_leaf_rank]
    · let previous : Fin 10 := ⟨position.val.level.val - 1, by omega⟩
      simp only [nodeChildren, dif_pos lower, dif_neg zero, Prod.fst, Prod.snd]
      rw [tagged]
      simp only [if_pos lower, bottom_node_rank]
      omega
  · have upper : position.val.level.val < 160 := small
    by_cases atBase : position.val.level.val = GroupedBalancedGraphPayload67.groupBase position.val.level.val
    ·
      simp only [nodeChildren, dif_neg lower, dif_pos upper, dif_pos atBase,
        Prod.fst, Prod.snd]
      rw [tagged]
      simp only [if_neg lower, upper_leaf_rank]
      omega
    · have positive : 10 < position.val.level.val := by
        have bound := groupBase_bounds position.val.level.val (by omega) small
        by_contra notPositive
        have levelTen : position.val.level.val = 10 := by omega
        exact atBase (by simpa [levelTen, GroupedBalancedGraphPayload67.groupBase])
      have basePrev := groupBase_previous position.val.level.val positive small
        (Ne.symm atBase)
      simp only [nodeChildren, dif_neg lower, dif_pos upper, dif_neg atBase,
        Prod.fst, Prod.snd]
      rw [tagged]
      simp only [if_neg lower, upper_node_rank]
      have previousBound : position.val.level.val - 11 < 150 := by omega
      have previousLevel :
          (Fin.ofNat 150 (position.val.level.val - 11)).val + 10 =
            position.val.level.val - 1 := by
        simp [Fin.ofNat, Nat.mod_eq_of_lt previousBound]
        omega
      rw [previousLevel]
      rw [basePrev]
      have bound := groupBase_bounds position.val.level.val (by omega) small
      omega

/-- Symbolic complete graph order. The enormous address space is never
enumerated by the kernel; the sort and coverage proofs use finite-type laws. -/
noncomputable def positions : List Position :=
  (Finset.univ : Finset Position).toList.mergeSort
    (fun first second => decide (rank first ≤ rank second))

theorem positions_perm : positions.Perm (Finset.univ : Finset Position).toList :=
  List.mergeSort_perm _ _

theorem positions_nodup : positions.Nodup :=
  positions_perm.nodup_iff.mpr (Finset.nodup_toList _)

theorem positions_complete (position : Position) : position ∈ positions := by
  rw [positions_perm.mem_iff]
  simp

theorem positions_ordered : positions.Pairwise
    (fun first second => rank first ≤ rank second) := by
  simpa only [positions, decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun first second : Position => decide (rank first ≤ rank second))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (Finset.univ : Finset Position).toList)

end SigGolfCandidate.Hypertree.GroupedBalancedGraphOrder67
