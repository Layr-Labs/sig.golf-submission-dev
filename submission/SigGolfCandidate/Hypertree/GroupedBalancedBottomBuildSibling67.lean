import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeModel67
import Mathlib.Data.Nat.Bitwise

/-! Functional bottom-tree witness words match the source tree's selected siblings. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedBottomBuildSibling67
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def siblingAt : {height : Nat} → GroupedBottomTree.Witness height → Nat → Digest
  | 0, .seed _, _ => 0
  | height + 1, .step inner sibling, level =>
      if level = height then sibling else siblingAt inner level

private theorem child_address (height index : Nat) :
    (if index / 2^height % 2 = 0 then
      2 * (index / 2^(height+1))
    else 2 * (index / 2^(height+1)) + 1) = index / 2^height := by
  have quotient : (index / 2^height) / 2 = index / 2^(height+1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have rem := Nat.mod_add_div (index / 2^height) 2
  have small := Nat.mod_lt (index / 2^height) (by decide : 0 < 2)
  by_cases bit : index / 2^height % 2 = 0
  · simp only [if_pos bit]
    omega
  · simp only [if_neg bit]
    omega

theorem build_sibling (hash : Hash) (secretKey : SecretKey)
    (height index level : Nat) (lt : level < height) :
    siblingAt (GroupedBottomTree.build hash secretKey height
      (index / 2^height) index).witness level =
      GroupedBottomTree.root hash secretKey level
        (if index / 2^level % 2 = 0 then index / 2^level + 1
          else index / 2^level - 1) := by
  induction height with
  | zero => omega
  | succ height ih =>
      by_cases bit : index / 2^height % 2 = 0
      · have child : 2 * (index / 2^(height+1)) = index / 2^height := by
          simpa only [if_pos bit] using child_address height index
        by_cases top : level = height
        · subst level
          simp only [GroupedBottomTree.build, if_pos bit,
            siblingAt, ite_true]
          rw [child]
          exact GroupedBottomTree.build_root hash secretKey height
            (index / 2^height + 1) index
        · have low : level < height := by omega
          simp only [GroupedBottomTree.build, if_pos bit,
            siblingAt, if_neg top]
          rw [child]
          exact ih low
      · have child : 2 * (index / 2^(height+1)) + 1 = index / 2^height := by
          simpa only [if_neg bit] using child_address height index
        by_cases top : level = height
        · subst level
          simp only [GroupedBottomTree.build, if_neg bit,
            siblingAt, ite_true]
          have opposite : 2 * (index / 2^(height+1)) = index / 2^height - 1 := by
            omega
          rw [opposite]
          exact GroupedBottomTree.build_root hash secretKey height
            (index / 2^height - 1) index
        · have low : level < height := by omega
          simp only [GroupedBottomTree.build, if_neg bit,
            siblingAt, if_neg top]
          rw [child]
          exact ih low

private theorem quotient_relative (rootAddress height level selected : Nat)
    (levelBound : level ≤ height) :
    (rootAddress * 2^height + selected) / 2^level =
      rootAddress * 2^(height-level) + selected / 2^level := by
  have factor : 2^height = 2^(height-level) * 2^level := by
    rw [← pow_add]
    congr 1
    omega
  rw [factor]
  calc
    (rootAddress * (2^(height-level) * 2^level) + selected) / 2^level =
      ((rootAddress * 2^(height-level)) * 2^level + selected) / 2^level := by
        rw [mul_assoc]
    _ = rootAddress * 2^(height-level) + selected / 2^level := by
      rw [Nat.mul_comm (rootAddress * 2^(height-level)) (2^level),
        Nat.mul_add_div (pow_pos (by decide) level)]

private theorem sibling_address (rootAddress height selected level : Nat)
    (lt : level < height) :
    rootAddress * 2^(height-level) + Nat.xor (selected / 2^level) 1 =
      (if (rootAddress * 2^height + selected) / 2^level % 2 = 0 then
        (rootAddress * 2^height + selected) / 2^level + 1
      else (rootAddress * 2^height + selected) / 2^level - 1) := by
  have q := quotient_relative rootAddress height level selected (by omega)
  have factor : 2 ∣ 2^(height-level) :=
    pow_dvd_pow 2 (by omega : 1 ≤ height-level)
  have baseEven : (rootAddress * 2^(height-level)) % 2 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact dvd_mul_of_dvd_right factor rootAddress
  have parity :
      ((rootAddress * 2^height + selected) / 2^level) % 2 =
        (selected / 2^level) % 2 := by
    rw [q, Nat.add_mod, baseEven]
    simp
  by_cases even : (selected / 2^level) % 2 = 0
  · have even' : Even (selected / 2^level) := Nat.even_iff.mpr even
    change rootAddress * 2^(height-level) +
      ((selected / 2^level) ^^^ 1) = _
    rw [Nat.xor_one_of_even even', if_pos (by rw [parity]; exact even)]
    omega
  · have odd' : Odd (selected / 2^level) := Nat.odd_iff.mpr (by
      have rem := Nat.mod_lt (selected / 2^level) (by decide : 0 < 2)
      omega)
    have positive : 0 < selected / 2^level := by
      by_contra h
      have zero : selected / 2^level = 0 := Nat.eq_zero_of_not_pos h
      simp [zero] at even
    change rootAddress * 2^(height-level) +
      ((selected / 2^level) ^^^ 1) = _
    rw [Nat.xor_one_of_odd odd', if_neg (by rw [parity]; exact even)]
    omega

theorem built_sibling_node (hash : Hash) (secretKey : SecretKey)
    (rootAddress selected level : Nat) (lt : level < 10) :
    siblingAt (GroupedBottomTree.build hash secretKey 10
      ((rootAddress * 2^10 + selected) / 2^10)
      (rootAddress * 2^10 + selected)).witness level =
      GroupedBalancedSignBottomTreeModel67.levelNode hash secretKey
        (rootAddress * 2^10) level
        (Nat.xor (selected / 2^level) 1) := by
  rw [GroupedBalancedSignBottomTreeModel67.levelNode]
  rw [build_sibling hash secretKey 10
    (rootAddress * 2^10 + selected) level lt]
  have baseQ : (rootAddress * 2^10) / 2^level =
      rootAddress * 2^(10-level) := by
    simpa using quotient_relative rootAddress 10 level 0 (by omega)
  rw [baseQ]
  exact congrArg (GroupedBottomTree.root hash secretKey level)
    (sibling_address rootAddress 10 selected level lt).symm

#print axioms build_sibling
#print axioms built_sibling_node
end SigGolfCandidate.Hypertree.GroupedBalancedBottomBuildSibling67
