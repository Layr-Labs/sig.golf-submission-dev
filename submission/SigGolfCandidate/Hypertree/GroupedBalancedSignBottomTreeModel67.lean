import SigGolfCandidate.Hypertree.GroupedBottomTree
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeModel67
open SigGolf SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
def levelNode (hash : Hash) (secretKey : SecretKey)
    (base height address : Nat) : Reference.Digest :=
  GroupedBottomTree.root hash secretKey height (base / 2^height + address)
private theorem half_base (base height : Nat)
    (aligned : base % 2^10 = 0) (bound : height < 10) :
    base / 2^height = 2 * (base / 2^(height+1)) := by
  have divisor : 2^(height+1) ∣ 2^10 :=
    pow_dvd_pow 2 (by omega)
  have divides : 2^(height+1) ∣ base :=
    dvd_trans divisor (Nat.dvd_of_mod_eq_zero aligned)
  obtain ⟨k,hk⟩ := divides
  subst base
  have left : (2^(height+1) * k) / 2^height = 2 * k := by
    rw [pow_succ]
    calc
      (2^height * 2 * k) / 2^height =
          (2^height * (2*k)) / 2^height := by ring
      _ = 2*k := by simp
  have right : (2^(height+1) * k) / 2^(height+1) = k := by simp
  rw [left,right]
theorem parent_node (hash : Hash) (secretKey : SecretKey)
    (base height address : Nat)
    (aligned : base % 2^10 = 0) (bound : height < 10) :
    levelNode hash secretKey base (height+1) address =
      GroupedBottomTree.node hash height (base / 2^(height+1) + address)
        (levelNode hash secretKey base height (2*address))
        (levelNode hash secretKey base height (2*address+1)) := by
  have half := half_base base height aligned bound
  have leftAddress :
      2 * (base / 2^(height+1) + address) =
        base / 2^height + 2*address := by rw [half]; omega
  simp only [levelNode,GroupedBottomTree.root]
  rw [leftAddress]
  simp only [Nat.add_assoc]
#print axioms parent_node
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeModel67
