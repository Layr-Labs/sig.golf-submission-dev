import SigGolfCandidate.Hypertree.GroupedBalancedUpperTree67
import SigGolfCandidate.Hypertree.GroupedBottomTree

/-! A local leaf-array model for the reused upper Merkle callee. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeModel67
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def nodeAt (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Digest) : Nat → Nat → Digest
  | 0, j => leaves j
  | h+1, j =>
      GroupedBottomTree.node hash (treeBase+h) (leafBase/2^(h+1)+j)
        (nodeAt hash treeBase leafBase leaves h (2*j))
        (nodeAt hash treeBase leafBase leaves h (2*j+1))

theorem parent (hash : Hash) (treeBase leafBase : Nat)
    (leaves : Nat → Digest) (h j : Nat) :
    nodeAt hash treeBase leafBase leaves (h+1) j =
      GroupedBottomTree.node hash (treeBase+h) (leafBase/2^(h+1)+j)
        (nodeAt hash treeBase leafBase leaves h (2*j))
        (nodeAt hash treeBase leafBase leaves h (2*j+1)) := rfl

theorem node_eq_upper (hash : Hash) (secretKey : SecretKey)
    (treeBase leafBase h j : Nat)
    (aligned : leafBase % 2^h = 0) :
    nodeAt hash treeBase leafBase
      (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (leafBase+k)) h j =
      GroupedBalancedUpperTree67.root hash secretKey treeBase h
        (leafBase/2^h+j) := by
  revert aligned
  induction h generalizing j with
  | zero =>
      intro _
      simp [nodeAt,GroupedBalancedUpperTree67.root]
  | succ h ih =>
      intro aligned
      have subAlign : leafBase % 2^h = 0 := by
        have div : 2^h ∣ 2^(h+1) := pow_dvd_pow 2 (by omega)
        exact Nat.mod_eq_zero_of_dvd (dvd_trans div
          (Nat.dvd_of_mod_eq_zero aligned))
      have split : leafBase / 2^h = 2 * (leafBase / 2^(h+1)) := by
        have div : 2^(h+1) ∣ leafBase := Nat.dvd_of_mod_eq_zero aligned
        obtain ⟨q,hq⟩ := div
        subst leafBase
        rw [pow_succ]
        calc
          (2^h * 2 * q) / 2^h = 2*q := by simp [mul_assoc]
          _ = 2 * ((2^h * 2 * q) / (2^h * 2)) := by simp
      simp only [nodeAt,GroupedBalancedUpperTree67.root]
      rw [ih (2*j) subAlign, ih (2*j+1) subAlign]
      rw [split]
      have sameNode : GroupedBottomTree.node = GroupedBalancedUpperTree67.node := rfl
      rw [sameNode]
      have left : 2 * (leafBase/2^(h+1)+j) =
          2*(leafBase/2^(h+1)) + 2*j := by omega
      rw [left]
      simp only [Nat.add_assoc]

theorem node_eq_upper_root (hash : Hash) (secretKey : SecretKey)
    (treeBase rootAddress height : Nat) :
    nodeAt hash treeBase (rootAddress*2^height)
      (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey treeBase
        (rootAddress*2^height+k)) height 0 =
      GroupedBalancedUpperTree67.root hash secretKey treeBase height
        rootAddress := by
  have aligned : (rootAddress*2^height) % 2^height = 0 := by simp
  have h := node_eq_upper hash secretKey treeBase (rootAddress*2^height)
    height 0 aligned
  simpa using h

#print axioms node_eq_upper_root
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeModel67
