import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperGroupComplete67

/-! Numeric schedule for thirty height-three and fifteen height-four groups. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSchedule67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree

def height (k : Nat) : Nat := if k<30 then 3 else 4

def prefixHeight (k : Nat) : Nat :=
  if k≤30 then 3*k else 90+4*(k-30)

def treeBase (k : Nat) : Nat := 10+prefixHeight k

def currentWitness (k : Nat) : Nat :=
  0x20130+16*(67*k+prefixHeight k)

def witnessBase (k : Nat) : Nat := currentWitness k+1072

def calls (k : Nat) : Nat := if k<30 then 1991 else 3983

def blocks (k : Nat) : Nat := if k<30 then 2127 else 4255

def postCost (k : Nat) : Nat :=
  if k=29 then 147 else if k<30 then 143 else 179

theorem prefix_zero : prefixHeight 0=0 := by decide
theorem prefix_thirty : prefixHeight 30=90 := by decide
theorem prefix_forty_four : prefixHeight 44=146 := by decide
theorem prefix_forty_five : prefixHeight 45=150 := by decide
theorem base_forty_four : treeBase 44=156 := by decide
theorem base_forty_five : treeBase 45=160 := by decide

theorem prefix_next (k : Nat) :
    prefixHeight (k+1)=prefixHeight k+height k := by
  unfold prefixHeight height
  by_cases h29 : k<30
  · have hk : k≤30 := by omega
    have hk1 : k+1≤30 := by omega
    simp [h29,hk,hk1]
    omega
  · have hk1 : ¬k+1≤30 := by omega
    by_cases h30 : k≤30
    · have keq : k=30 := by omega
      subst k
      decide
    · simp [h29,hk1,h30]
      omega

theorem prefix_bound (k : Nat) (hk : k≤45) : prefixHeight k≤150 := by
  unfold prefixHeight
  split_ifs <;> omega

theorem height_cases (k : Nat) : height k=3 ∨ height k=4 := by
  unfold height
  split_ifs <;> simp

theorem height_switch (k : Nat) :
    height (k+1) = if k=29 then 4 else height k := by
  unfold height
  split_ifs <;> omega

theorem treeBase_next (k : Nat) :
    treeBase (k+1)=treeBase k+height k := by
  simp [treeBase,prefix_next]
  omega

theorem witness_next (k : Nat) :
    currentWitness (k+1)=witnessBase k+16*height k := by
  simp [currentWitness,witnessBase,prefix_next]
  omega

theorem witness_current_lower (k : Nat) :
    0x20060≤currentWitness k := by
  unfold currentWitness
  omega

theorem witness_current_upper (k : Nat) (hk : k≤45) :
    currentWitness k+16*67≤0x80000 := by
  have hp := prefix_bound k hk
  unfold currentWitness
  omega

theorem witness_current_aligned (k : Nat) : currentWitness k%8=0 := by
  unfold currentWitness
  omega

theorem witness_base_lower (k : Nat) : 0x20060≤witnessBase k := by
  unfold witnessBase
  have h := witness_current_lower k
  omega

theorem witness_base_bound (k : Nat) (hk : k<45) :
    witnessBase k+16*height k+16≤0x80000 := by
  have hp := prefix_bound k (by omega : k≤45)
  have hh := height_cases k
  rcases hh with h|h <;> rw [h] <;>
    unfold witnessBase currentWitness <;> omega

theorem witness_base_aligned (k : Nat) : witnessBase k%8=0 := by
  unfold witnessBase
  have h := witness_current_aligned k
  omega

theorem tree_bound (k : Nat) (hk : k<45) :
    treeBase k+height k<2^64 := by
  have hp := prefix_bound k (by omega : k≤45)
  have hh := height_cases k
  rcases hh with h|h <;> rw [h] <;> unfold treeBase <;> omega

theorem base_bound (k : Nat) (hk : k<45) : treeBase k<256 := by
  have hp := prefix_bound k (by omega : k≤45)
  unfold treeBase
  omega

theorem total_calls : (∑ k ∈ Finset.range 45, calls k)=119475 := by decide
theorem total_blocks : (∑ k ∈ Finset.range 45, blocks k)=127635 := by decide
theorem total_post_cost : (∑ k ∈ Finset.range 45, postCost k)=6979 := by decide

#print axioms prefix_next
#print axioms witness_next
#print axioms total_calls
#print axioms total_blocks
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSchedule67
