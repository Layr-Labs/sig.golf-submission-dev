import SigGolfCandidate.Hypertree.GroupedBalancedQuaternary

/-! A 67-chain direct code. The 64 base-four payload digits and one flip
digit use radix four. A two-digit checksum uses radices nine and eleven.
Its exact suffix bound is 98, and a full endpoint takes 213 chain steps. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedChecksum67
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 4096

abbrev Chain := Fin 67

def maxDigit (chain : Chain) : Nat :=
  if chain.val < 65 then 3 else if chain.val = 65 then 8 else 10

def digit (message : Digest) (chain : Chain) : Fin 11 :=
  if h : chain.val < 64 then
    ⟨GroupedBalancedQuaternary.payloadDigit message ⟨chain.val, h⟩,
      by have := GroupedBalancedQuaternary.payloadDigit_lt_four message ⟨chain.val, h⟩; omega⟩
  else if chain.val = 64 then
    ⟨GroupedBalancedQuaternary.flagDigit message,
      by have := GroupedBalancedQuaternary.flagDigit_lt_four message; omega⟩
  else if chain.val = 65 then
    ⟨GroupedBalancedQuaternary.checksum message % 9, by omega⟩
  else
    ⟨GroupedBalancedQuaternary.checksum message / 9,
      by have := GroupedBalancedQuaternary.checksum_le message; omega⟩

theorem digit_le_max (message : Digest) (chain : Chain) :
    (digit message chain).val ≤ maxDigit chain := by
  by_cases h : chain.val < 64
  · simp only [digit, dif_pos h, maxDigit, if_pos (by omega : chain.val < 65)]
    have := GroupedBalancedQuaternary.payloadDigit_lt_four message ⟨chain.val, h⟩
    omega
  · by_cases h64 : chain.val = 64
    · simp only [digit, dif_neg h, if_pos h64, maxDigit,
        if_pos (by omega : chain.val < 65)]
      have := GroupedBalancedQuaternary.flagDigit_lt_four message
      omega
    · by_cases h65 : chain.val = 65
      · simp only [digit, dif_neg h, if_neg h64, maxDigit,
          if_neg (by omega : ¬chain.val < 65), if_pos h65]
        have := Nat.mod_lt (GroupedBalancedQuaternary.checksum message) (by decide : 0 < 9)
        omega
      · simp only [digit, dif_neg h, if_neg h64, maxDigit,
          if_neg (by omega : ¬chain.val < 65), if_neg h65]
        have := GroupedBalancedQuaternary.checksum_le message
        omega

private theorem digit_payload (message : Digest) (i : Fin 64) :
    (digit message ⟨i.val, by omega⟩).val =
      GroupedBalancedQuaternary.payloadDigit message i := by
  simp only [digit, dif_pos i.isLt]

private theorem digit_flag (message : Digest) :
    (digit message ⟨64, by decide⟩).val =
      GroupedBalancedQuaternary.flagDigit message := by
  simp only [digit, dif_neg (show ¬(64 : Nat) < 64 by decide), if_true,
    Fin.val_mk]

private theorem digit_checksum0 (message : Digest) :
    (digit message ⟨65, by decide⟩).val =
      GroupedBalancedQuaternary.checksum message % 9 := by
  simp only [digit, dif_neg (show ¬(65 : Nat) < 64 by decide),
    if_neg (show (65 : Nat) ≠ 64 by decide), if_true, Fin.val_mk]

private theorem digit_checksum1 (message : Digest) :
    (digit message ⟨66, by decide⟩).val =
      GroupedBalancedQuaternary.checksum message / 9 := by
  simp only [digit, dif_neg (show ¬(66 : Nat) < 64 by decide),
    if_neg (show (66 : Nat) ≠ 64 by decide),
    if_neg (show (66 : Nat) ≠ 65 by decide), Fin.val_mk]

theorem digits_antichain (x y : Digest)
    (ordered : ∀ i : Chain, (digit x i).val ≤ (digit y i).val) : x = y := by
  have payloads : ∀ i : Fin 64,
      GroupedBalancedQuaternary.payloadDigit x i ≤
        GroupedBalancedQuaternary.payloadDigit y i := by
    intro i
    simpa only [digit_payload] using ordered ⟨i.val, by omega⟩
  have flags : GroupedBalancedQuaternary.flagDigit x ≤
      GroupedBalancedQuaternary.flagDigit y := by
    simpa only [digit_flag] using ordered ⟨64, by decide⟩
  have sums : GroupedBalancedQuaternary.payloadSum x +
      GroupedBalancedQuaternary.flagDigit x ≤
      GroupedBalancedQuaternary.payloadSum y +
      GroupedBalancedQuaternary.flagDigit y := by
    unfold GroupedBalancedQuaternary.payloadSum
    exact Nat.add_le_add (Finset.sum_le_sum (fun i _ => payloads i)) flags
  have checksum_le : GroupedBalancedQuaternary.checksum x ≤
      GroupedBalancedQuaternary.checksum y := by
    have low : GroupedBalancedQuaternary.checksum x % 9 ≤
        GroupedBalancedQuaternary.checksum y % 9 := by
      simpa only [digit_checksum0] using ordered ⟨65, by decide⟩
    have high : GroupedBalancedQuaternary.checksum x / 9 ≤
        GroupedBalancedQuaternary.checksum y / 9 := by
      simpa only [digit_checksum1] using ordered ⟨66, by decide⟩
    have hx := Nat.mod_add_div (GroupedBalancedQuaternary.checksum x) 9
    have hy := Nat.mod_add_div (GroupedBalancedQuaternary.checksum y) 9
    omega
  have totalsX := GroupedBalancedQuaternary.checksum_add_payload x
  have totalsY := GroupedBalancedQuaternary.checksum_add_payload y
  have sameTotal : GroupedBalancedQuaternary.payloadSum x +
      GroupedBalancedQuaternary.flagDigit x =
      GroupedBalancedQuaternary.payloadSum y +
      GroupedBalancedQuaternary.flagDigit y := by omega
  have payload_le : GroupedBalancedQuaternary.payloadSum x ≤
      GroupedBalancedQuaternary.payloadSum y := by
    unfold GroupedBalancedQuaternary.payloadSum
    exact Finset.sum_le_sum (fun i _ => payloads i)
  have samePayload : GroupedBalancedQuaternary.payloadSum x =
      GroupedBalancedQuaternary.payloadSum y := by omega
  have sameFlag : GroupedBalancedQuaternary.flagDigit x =
      GroupedBalancedQuaternary.flagDigit y := by omega
  have same := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 64))) =>
    payloads i)).mp (by simpa only [GroupedBalancedQuaternary.payloadSum] using samePayload)
  apply GroupedBalancedQuaternary.raw_of_payload_same_flag x y sameFlag
  intro i
  exact same i (by simp)

theorem distinct_digest_has_earlier_digit (x y : Digest) (different : x ≠ y) :
    ∃ i : Chain, (digit y i).val < (digit x i).val := by
  by_contra h
  push Not at h
  exact different (digits_antichain x y h)

def suffixCost (message : Digest) : Nat :=
  ∑ i : Chain, (maxDigit i - (digit message i).val)

private def prefixCost (message : Digest) (count : Nat) : Nat :=
  ∑ i ∈ Finset.range count,
    (maxDigit ⟨i % 67, Nat.mod_lt _ (by decide)⟩ -
      (digit message ⟨i % 67, Nat.mod_lt _ (by decide)⟩).val)

private theorem prefix_succ (message : Digest) (count : Nat) (bound : count < 67) :
    prefixCost message (count + 1) = prefixCost message count +
      (maxDigit ⟨count, bound⟩ - (digit message ⟨count, bound⟩).val) := by
  simp [prefixCost, Finset.sum_range_succ, Nat.mod_eq_of_lt bound]

private theorem prefix_payload (message : Digest) :
    prefixCost message 64 = 192 - GroupedBalancedQuaternary.payloadSum message := by
  unfold prefixCost
  rw [← Fin.sum_univ_eq_sum_range]
  have terms :
      (∑ i : Fin 64, (maxDigit ⟨i.val % 67, Nat.mod_lt _ (by decide)⟩ -
        (digit message ⟨i.val % 67, Nat.mod_lt _ (by decide)⟩).val)) =
      ∑ i : Fin 64, (3 - GroupedBalancedQuaternary.payloadDigit message i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.mod_eq_of_lt (by omega : i.val < 67), maxDigit,
      show i.val < 65 by omega, digit_payload]
  rw [terms, Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      GroupedBalancedQuaternary.payloadSum]
    rfl
  · intro i _
    have hi := GroupedBalancedQuaternary.payloadDigit_lt_four message i
    omega

private theorem prefix_payload_flag (message : Digest) :
    prefixCost message 65 = GroupedBalancedQuaternary.checksum message := by
  rw [prefix_succ message 64 (by decide), prefix_payload, digit_flag]
  have hf := GroupedBalancedQuaternary.flagDigit_lt_four message
  have hp := GroupedBalancedQuaternary.payloadSum_le message
  have h := GroupedBalancedQuaternary.checksum_add_payload message
  simp only [maxDigit, if_pos (by decide : (64 : Nat) < 65)]
  omega

theorem suffix_cost_le (message : Digest) : suffixCost message ≤ 98 := by
  have qbound := GroupedBalancedQuaternary.checksum_le message
  have hprefix : suffixCost message = prefixCost message 67 := by
    unfold suffixCost prefixCost
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.mod_eq_of_lt i.isLt]
  rw [hprefix, prefix_succ message 66 (by decide),
    prefix_succ message 65 (by decide), prefix_payload_flag]
  rw [digit_checksum0, digit_checksum1]
  norm_num [maxDigit]
  have modBound := Nat.mod_lt (GroupedBalancedQuaternary.checksum message)
    (by decide : 0 < 9)
  have decomposition := Nat.mod_add_div (GroupedBalancedQuaternary.checksum message) 9
  omega

theorem full_chain_steps : (∑ chain : Chain, maxDigit chain) = 213 := by decide

end SigGolfCandidate.Hypertree.GroupedBalancedChecksum67
