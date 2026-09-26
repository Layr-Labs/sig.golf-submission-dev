import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeModel67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedTreeSiblingAllData67

/-! The functional upper-tree builder selects exactly the sibling at each
Merkle level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedUpperBuildSibling67
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def siblingAt : {height : Nat} →
    GroupedBalancedUpperTree67.Witness height → Nat → Digest
  | 0, .leaf _, _ => 0
  | height+1, .step inner sibling, level =>
      if level=height then sibling else siblingAt inner level

def leafAt : {height : Nat} →
    GroupedBalancedUpperTree67.Witness height →
    GroupedBalancedUpperTree67.ChainMixed → Digest
  | 0, .leaf values, chain => values chain
  | _+1, .step inner _, chain => leafAt inner chain

private theorem child_address (height index : Nat) :
    (if index / 2^height % 2=0 then
      2*(index/2^(height+1))
    else 2*(index/2^(height+1))+1)=index/2^height := by
  have quotient : (index/2^height)/2=index/2^(height+1) := by
    rw [Nat.div_div_eq_div_mul,pow_succ]
  have rem := Nat.mod_add_div (index/2^height) 2
  have small := Nat.mod_lt (index/2^height) (by decide : 0<2)
  by_cases bit : index/2^height%2=0
  · simp only [if_pos bit]
    omega
  · simp only [if_neg bit]
    omega

theorem build_sibling (hash : Hash) (secretKey : SecretKey)
    (base height index level : Nat) (message : Digest) (lt : level<height) :
    siblingAt (GroupedBalancedUpperTree67.build hash secretKey base height
      (index/2^height) index message).witness level =
      GroupedBalancedUpperTree67.root hash secretKey base level
        (if index/2^level%2=0 then index/2^level+1
          else index/2^level-1) := by
  induction height with
  | zero => omega
  | succ height ih =>
      by_cases bit : index/2^height%2=0
      · have child : 2*(index/2^(height+1))=index/2^height := by
          simpa only [if_pos bit] using child_address height index
        by_cases top : level=height
        · subst level
          simp only [GroupedBalancedUpperTree67.build,if_pos bit,
            siblingAt,ite_true]
          rw [child]
        · have low : level<height := by omega
          simp only [GroupedBalancedUpperTree67.build,if_pos bit,
            siblingAt,if_neg top]
          rw [child]
          exact ih low
      · have child : 2*(index/2^(height+1))+1=index/2^height := by
          simpa only [if_neg bit] using child_address height index
        by_cases top : level=height
        · subst level
          simp only [GroupedBalancedUpperTree67.build,if_neg bit,
            siblingAt,ite_true]
          have opposite : 2*(index/2^(height+1))=index/2^height-1 := by
            omega
          rw [opposite]
        · have low : level<height := by omega
          simp only [GroupedBalancedUpperTree67.build,if_neg bit,
            siblingAt,if_neg top]
          rw [child]
          exact ih low

theorem build_leaf (hash : Hash) (secretKey : SecretKey)
    (base height index : Nat) (message : Digest)
    (chain : GroupedBalancedUpperTree67.ChainMixed) :
    leafAt (GroupedBalancedUpperTree67.build hash secretKey base height
      (index/2^height) index message).witness chain =
      GroupedBalancedUpperTree67.signValues hash secretKey base index
        message chain := by
  induction height with
  | zero => simp [GroupedBalancedUpperTree67.build,leafAt]
  | succ height ih =>
      by_cases bit : index/2^height%2=0
      · have child : 2*(index/2^(height+1))=index/2^height := by
          simpa only [if_pos bit] using child_address height index
        simp only [GroupedBalancedUpperTree67.build,if_pos bit,leafAt]
        rw [child]
        exact ih
      · have child : 2*(index/2^(height+1))+1=index/2^height := by
          simpa only [if_neg bit] using child_address height index
        simp only [GroupedBalancedUpperTree67.build,if_neg bit,leafAt]
        rw [child]
        exact ih

private theorem quotient_relative (rootAddress height level selected : Nat)
    (levelBound : level≤height) :
    (rootAddress*2^height+selected)/2^level =
      rootAddress*2^(height-level)+selected/2^level := by
  have factor : 2^height=2^(height-level)*2^level := by
    rw [←pow_add]
    congr 1
    omega
  rw [factor]
  calc
    (rootAddress*(2^(height-level)*2^level)+selected)/2^level =
      ((rootAddress*2^(height-level))*2^level+selected)/2^level := by
        rw [mul_assoc]
    _ = rootAddress*2^(height-level)+selected/2^level := by
      rw [Nat.mul_comm (rootAddress*2^(height-level)) (2^level),
        Nat.mul_add_div (pow_pos (by decide) level)]

private theorem sibling_address (rootAddress height selected level : Nat)
    (lt : level<height) :
    rootAddress*2^(height-level)+Nat.xor (selected/2^level) 1 =
      (if (rootAddress*2^height+selected)/2^level%2=0 then
        (rootAddress*2^height+selected)/2^level+1
      else (rootAddress*2^height+selected)/2^level-1) := by
  have q := quotient_relative rootAddress height level selected (by omega)
  have factor : 2 ∣ 2^(height-level) :=
    pow_dvd_pow 2 (by omega : 1≤height-level)
  have baseEven : (rootAddress*2^(height-level))%2=0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact dvd_mul_of_dvd_right factor rootAddress
  have parity :
      ((rootAddress*2^height+selected)/2^level)%2 =
        (selected/2^level)%2 := by
    rw [q,Nat.add_mod,baseEven]
    simp
  by_cases even : (selected/2^level)%2=0
  · have even' : Even (selected/2^level) := Nat.even_iff.mpr even
    change rootAddress*2^(height-level)+((selected/2^level) ^^^ 1) = _
    rw [Nat.xor_one_of_even even',if_pos (by rw [parity]; exact even)]
    omega
  · have odd' : Odd (selected/2^level) := Nat.odd_iff.mpr (by
      have rem := Nat.mod_lt (selected/2^level) (by decide : 0<2)
      omega)
    have qpos : 0 < selected/2^level := by
      by_contra h
      have zero : selected/2^level=0 := Nat.eq_zero_of_not_pos h
      simp [zero] at even
    change rootAddress*2^(height-level)+((selected/2^level) ^^^ 1) = _
    rw [Nat.xor_one_of_odd odd',if_neg (by rw [parity]; exact even)]
    omega

theorem built_sibling_node (hash : Hash) (secretKey : SecretKey)
    (base rootAddress height selected level : Nat) (message : Digest)
    (lt : level<height) :
    siblingAt (GroupedBalancedUpperTree67.build hash secretKey base height
      ((rootAddress*2^height+selected)/2^height)
      (rootAddress*2^height+selected) message).witness level =
      GroupedBalancedSignUpperTreeModel67.nodeAt hash base
        (rootAddress*2^height)
        (fun k => GroupedBalancedUpperTree67.leafRoot hash secretKey base
          (rootAddress*2^height+k)) level
        (Nat.xor (selected/2^level) 1) := by
  have aligned : (rootAddress*2^height)%2^level=0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact dvd_mul_of_dvd_right (pow_dvd_pow 2 (by omega)) rootAddress
  rw [GroupedBalancedSignUpperTreeModel67.node_eq_upper hash secretKey base
    (rootAddress*2^height) level (Nat.xor (selected/2^level) 1) aligned]
  rw [build_sibling hash secretKey base height
    (rootAddress*2^height+selected) level message lt]
  have baseQ : (rootAddress*2^height)/2^level=
      rootAddress*2^(height-level) := by
    simpa using quotient_relative rootAddress height level 0 (by omega)
  rw [baseQ]
  exact congrArg (GroupedBalancedUpperTree67.root hash secretKey base level)
    (sibling_address rootAddress height selected level lt).symm

#print axioms build_sibling
#print axioms build_leaf
#print axioms built_sibling_node
end SigGolfCandidate.Hypertree.GroupedBalancedUpperBuildSibling67
