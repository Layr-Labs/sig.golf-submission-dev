import SigGolfCandidate.Hypertree.GroupedUniformCapacity
import Mathlib.Tactic.IntervalCases
namespace SigGolfCandidate.Hypertree.GroupedUniformTableBound
open Finset SigGolfCandidate.Hypertree.GroupedUniformCapacity
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def rows : List (List Nat) := [
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 3, 6, 10, 15, 21, 25, 27, 27, 25, 21, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 4, 10, 20, 35, 56, 80, 104, 125, 140, 146, 140, 125, 104, 80, 56, 35, 20, 10, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 5, 15, 35, 70, 126, 205, 305, 420, 540, 651, 735, 780, 780, 735, 651, 540, 420, 305, 205, 126, 70, 35, 15, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 6, 21, 56, 126, 252, 456, 756, 1161, 1666, 2247, 2856, 3431, 3906, 4221, 4332, 4221, 3906, 3431, 2856, 2247, 1666, 1161, 756, 456, 252, 126, 56, 21, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 7, 28, 84, 210, 462, 917, 1667, 2807, 4417, 6538, 9142, 12117, 15267, 18327, 20993, 22967, 24017, 24017, 22967, 20993, 18327, 15267, 12117, 9142, 6538, 4417, 2807, 1667, 917, 462, 210, 84, 28, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 8, 36, 120, 330, 792, 1708, 3368, 6147, 10480, 16808, 25488, 36688, 50288, 65808, 82384, 98813, 113688, 125588, 133288, 135954, 133288, 125588, 113688, 98813, 82384, 65808, 50288, 36688, 25488, 16808, 10480, 6147, 3368, 1708, 792, 330, 120, 36, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 9, 45, 165, 495, 1287, 2994, 6354, 12465, 22825, 39303, 63999, 98979, 145899, 205560, 277464, 359469, 447669, 536569, 619569, 689715, 740619, 767394, 767394, 740619, 689715, 619569, 536569, 447669, 359469, 277464, 205560, 145899, 98979, 63999, 39303, 22825, 12465, 6354, 2994, 1287, 495, 165, 45, 9, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 10, 55, 220, 715, 2002, 4995, 11340, 23760, 46420, 85228, 147940, 243925, 383470, 576565, 831204, 1151370, 1535040, 1972630, 2446300, 2930455, 3393610, 3801535, 4121260, 4325310, 4395456, 4325310, 4121260, 3801535, 3393610, 2930455, 2446300, 1972630, 1535040, 1151370, 831204, 576565, 383470, 243925, 147940, 85228, 46420, 23760, 11340, 4995, 2002, 715, 220, 55, 10, 1, 0, 0, 0, 0, 0],
  [1, 11, 66, 286, 1001, 3003, 7997, 19327, 43032, 89232, 173745, 319683, 558613, 930743, 1483548, 2268332, 3334474, 4721574, 6450279, 8513109, 10866999, 13429405, 16079570, 18665790, 21018470, 22967626, 24362481, 25090131, 25090131, 24362481, 22967626, 21018470, 18665790, 16079570, 13429405, 10866999, 8513109, 6450279, 4721574, 3334474, 2268332, 1483548, 930743, 558613, 319683, 173745, 89232, 43032, 19327, 7997, 3003, 1001, 286, 66, 11, 1]
]

def table (n s : Nat) : Nat := (rows.getD n []).getD s 0

theorem table_step_0 (s : Fin 56) :
    table 1 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 0 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_1 (s : Fin 56) :
    table 2 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 1 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_2 (s : Fin 56) :
    table 3 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 2 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_3 (s : Fin 56) :
    table 4 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 3 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_4 (s : Fin 56) :
    table 5 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 4 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_5 (s : Fin 56) :
    table 6 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 5 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_6 (s : Fin 56) :
    table 7 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 6 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_7 (s : Fin 56) :
    table 8 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 7 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_8 (s : Fin 56) :
    table 9 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 8 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_9 (s : Fin 56) :
    table 10 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 9 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem table_step_10 (s : Fin 56) :
    table 11 s.val = ∑ d ∈ Finset.range 6, if d ≤ s.val then table 10 (s.val-d) else 0 := by
  fin_cases s <;> decide

theorem row11_max (s : Fin 56) : table 11 s.val ≤ 25090131 := by
  fin_cases s <;> decide



theorem table_base (s : Fin 56) : table 0 s.val = if s.val = 0 then 1 else 0 := by
  fin_cases s <;> decide

theorem table_step (n : Fin 11) (s : Fin 56) :
    table (n.val+1) s.val =
      ∑ d ∈ Finset.range 6, if d ≤ s.val then table n.val (s.val-d) else 0 := by
  fin_cases n
  · exact table_step_0 s
  · exact table_step_1 s
  · exact table_step_2 s
  · exact table_step_3 s
  · exact table_step_4 s
  · exact table_step_5 s
  · exact table_step_6 s
  · exact table_step_7 s
  · exact table_step_8 s
  · exact table_step_9 s
  · exact table_step_10 s

theorem count_succ_six (n s : Nat) :
    count (n+1) s = ∑ d ∈ Finset.range 6, if d ≤ s then count n (s-d) else 0 := by
  rw [count]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem count_eq_table (n s : Nat) (hn : n ≤ 11) (hs : s ≤ 55) : count n s = table n s := by
  induction n generalizing s with
  | zero =>
      simpa only [count] using (table_base ⟨s, by omega⟩).symm
  | succ n ih =>
      rw [count_succ_six]
      rw [show table (n+1) s =
        ∑ d ∈ Finset.range 6, if d ≤ s then table n (s-d) else 0 from
          table_step ⟨n, by omega⟩ ⟨s, by omega⟩]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hds : d ≤ s
      · simp only [if_pos hds]
        exact ih (s-d) (by omega) (by omega)
      · simp [hds]

private theorem count_zero_above (n s : Nat) (h : 5 * n < s) : count n s = 0 := by
  induction n generalizing s with
  | zero =>
      simp [count]
      omega
  | succ n ih =>
      rw [count_succ_six]
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hds : d ≤ s
      · simp only [if_pos hds]
        apply ih
        have hd6 : d < 6 := by simpa using hd
        omega
      · simp [hds]

theorem count11_max (s : Nat) : count 11 s ≤ 25090131 := by
  by_cases hs : s ≤ 55
  · rw [count_eq_table 11 s (by decide) hs]
    exact row11_max ⟨s, by omega⟩
  · rw [count_zero_above 11 s (by omega)]
    omega

private theorem count_le_pow (n s : Nat) : count n s ≤ 6 ^ n := by
  induction n generalizing s with
  | zero =>
      simp [count]
      split_ifs <;> omega
  | succ n ih =>
      rw [count_succ_six]
      calc
        _ ≤ ∑ _d ∈ Finset.range 6, 6 ^ n := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hds : d ≤ s
          · simpa only [if_pos hds] using ih (s-d)
          · simp [hds]
        _ = 6 ^ (n+1) := by simp [pow_succ, mul_comm]

private theorem count_after11 (k s : Nat) : count (11+k) s ≤ 25090131 * 6 ^ k := by
  induction k generalizing s with
  | zero => simpa using count11_max s
  | succ k ih =>
      rw [show 11 + (k+1) = (11+k)+1 by omega, count_succ_six]
      calc
        _ ≤ ∑ _d ∈ Finset.range 6, 25090131 * 6 ^ k := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hds : d ≤ s
          · simpa only [if_pos hds] using ih (s-d)
          · simp [hds]
        _ = 25090131 * 6 ^ (k+1) := by simp [pow_succ, mul_comm, mul_assoc]

/-- Every dense child-count entry queried by a 52-digit decoder fits in 128 bits. -/
theorem child_count_fits (n s : Nat) (hn : n ≤ 51) : count n s < 2 ^ 128 := by
  by_cases hsmall : n ≤ 10
  · have h := count_le_pow n s
    have hpow : 6 ^ n ≤ 6 ^ 10 := pow_le_pow_right₀ (by decide : (1:Nat) ≤ 6) hsmall
    have hnum : 6 ^ 10 < 2 ^ 128 := by norm_num
    omega
  · have h11 : 11 ≤ n := by omega
    let k := n - 11
    have hnk : 11 + k = n := by dsimp [k]; omega
    have hk : k ≤ 40 := by dsimp [k]; omega
    have h := count_after11 k s
    rw [hnk] at h
    have hpow : 6 ^ k ≤ 6 ^ 40 := pow_le_pow_right₀ (by decide : (1:Nat) ≤ 6) hk
    have hnum : 25090131 * 6 ^ 40 < 2 ^ 128 := by norm_num
    omega


end SigGolfCandidate.Hypertree.GroupedUniformTableBound
