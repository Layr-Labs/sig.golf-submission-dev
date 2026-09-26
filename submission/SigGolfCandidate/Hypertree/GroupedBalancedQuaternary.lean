import SigGolfCandidate.Hypertree.Reference

/-!
A direct 69-chain quaternary WOTS code for 128-bit digests. The first 64
digits are the ordinary base-four expansion, complemented when its digit sum
is below 96. Digit 64 records that choice. Four trailing digits encode the
checksum of all 65 payload digits. This uses only simple arithmetic on the
digest and has a uniform 105-hash verifier suffix bound.

This module is an isolated design study and is not imported by `Solution`.
-/

namespace SigGolfCandidate.Hypertree.GroupedBalancedQuaternary
open SigGolf SigGolfCandidate.Hypertree Reference
set_option maxRecDepth 4096
set_option maxHeartbeats 0

abbrev Chain4 := Fin 69

def rawDigit (message : Digest) (i : Fin 64) : Nat :=
  message.toNat / 4 ^ i.val % 4

def rawSum (message : Digest) : Nat :=
  ∑ i : Fin 64, rawDigit message i

abbrev needsFlip (message : Digest) : Prop := rawSum message < 96

def payloadDigit (message : Digest) (i : Fin 64) : Nat :=
  if needsFlip message then 3 - rawDigit message i else rawDigit message i

def payloadSum (message : Digest) : Nat :=
  ∑ i : Fin 64, payloadDigit message i

def flagDigit (message : Digest) : Nat :=
  if needsFlip message then 0 else 3

theorem flagDigit_lt_four (message : Digest) : flagDigit message < 4 := by
  unfold flagDigit
  split_ifs <;> omega

def checksum (message : Digest) : Nat :=
  195 - (payloadSum message + flagDigit message)

def digit (message : Digest) (i : Chain4) : Fin 4 :=
  if i.val < 64 then
    ⟨payloadDigit message ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩ % 4,
      Nat.mod_lt _ (by decide)⟩
  else if i.val = 64 then
    ⟨flagDigit message, flagDigit_lt_four message⟩
  else
    ⟨checksum message / 4 ^ (i.val - 65) % 4,
      Nat.mod_lt _ (by decide)⟩

private theorem base4_le (count m n : Nat) (hm : m < 4 ^ count) (hn : n < 4 ^ count)
    (digits : ∀ i, i < count → m / 4 ^ i % 4 ≤ n / 4 ^ i % 4) : m ≤ n := by
  induction count generalizing m n with
  | zero => simp only [pow_zero] at hm hn; omega
  | succ count ih =>
    have hm' : m / 4 < 4 ^ count := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ] using hm
    have hn' : n / 4 < 4 ^ count := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ] using hn
    have tails : m / 4 ≤ n / 4 := ih _ _ hm' hn' (by
      intro i hi
      have h := digits (i + 1) (by omega)
      simpa only [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using h)
    have heads := digits 0 (by omega)
    simp only [pow_zero, Nat.div_one] at heads
    omega

private theorem raw_digits_injective (x y : Digest)
    (same : ∀ i : Fin 64, rawDigit x i = rawDigit y i) : x = y := by
  have xb : x.toNat < 4 ^ 64 := by simpa only [show 4 ^ 64 = 2 ^ 128 by decide] using x.isLt
  have yb : y.toNat < 4 ^ 64 := by simpa only [show 4 ^ 64 = 2 ^ 128 by decide] using y.isLt
  apply BitVec.eq_of_toNat_eq
  apply Nat.le_antisymm
  · apply base4_le 64 _ _ xb yb
    intro i hi
    exact (same ⟨i, hi⟩).le
  · apply base4_le 64 _ _ yb xb
    intro i hi
    exact (same ⟨i, hi⟩).ge

private theorem rawDigit_lt_four (message : Digest) (i : Fin 64) :
    rawDigit message i < 4 := by
  unfold rawDigit
  exact Nat.mod_lt _ (by decide)

theorem rawSum_le (message : Digest) : rawSum message ≤ 192 := by
  unfold rawSum
  calc
    _ ≤ ∑ _i : Fin 64, (3 : Nat) := Finset.sum_le_sum (fun i _ => by
      have hi := rawDigit_lt_four message i
      omega)
    _ = 192 := by simp

theorem payloadDigit_lt_four (message : Digest) (i : Fin 64) :
    payloadDigit message i < 4 := by
  unfold payloadDigit
  split_ifs
  · have hi := rawDigit_lt_four message i
    omega
  · exact rawDigit_lt_four message i

theorem payloadSum_le (message : Digest) : payloadSum message ≤ 192 := by
  unfold payloadSum
  calc
    _ ≤ ∑ _i : Fin 64, (3 : Nat) := Finset.sum_le_sum (fun i _ => by
      have hi := payloadDigit_lt_four message i
      omega)
    _ = 192 := by simp

theorem payloadSum_flip (message : Digest) (flip : needsFlip message) :
    payloadSum message = 192 - rawSum message := by
  unfold payloadSum
  simp only [payloadDigit, if_pos flip]
  rw [Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rfl
  · intro i _
    have hi := rawDigit_lt_four message i
    omega

theorem payloadSum_ge (message : Digest) : 96 ≤ payloadSum message := by
  by_cases h : needsFlip message
  · rw [payloadSum_flip message h]
    have hs : rawSum message < 96 := h
    have hb := rawSum_le message
    omega
  · have hs : 96 ≤ rawSum message := by change ¬ rawSum message < 96 at h; omega
    simpa only [payloadSum, payloadDigit, if_neg h, rawSum] using hs

theorem payload_total_bounds (message : Digest) :
    97 ≤ payloadSum message + flagDigit message ∧
      payloadSum message + flagDigit message ≤ 195 := by
  have upper := payloadSum_le message
  by_cases h : needsFlip message
  · have hs := payloadSum_flip message h
    have hr := rawSum_le message
    simp only [flagDigit, if_pos h]
    have hf : rawSum message < 96 := h
    omega
  · have hs : 96 ≤ payloadSum message := payloadSum_ge message
    simp only [flagDigit, if_neg h]
    omega

theorem checksum_le (message : Digest) : checksum message ≤ 98 := by
  unfold checksum
  have h := payload_total_bounds message
  omega

theorem checksum_add_payload (message : Digest) :
    checksum message + (payloadSum message + flagDigit message) = 195 := by
  unfold checksum
  have h := payload_total_bounds message
  omega

private theorem digit_payload (message : Digest) (i : Fin 64) :
    (digit message ⟨i.val, by omega⟩).val = payloadDigit message i := by
  simp only [digit, if_pos i.isLt, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt (payloadDigit_lt_four message i)]

private theorem digit_flag (message : Digest) :
    (digit message ⟨64, by decide⟩).val = flagDigit message := by
  simp only [digit, if_neg (show ¬(64 : Nat) < 64 by decide), if_true,
    Fin.val_mk]

theorem raw_of_payload_same_flag (x y : Digest)
    (flag : flagDigit x = flagDigit y)
    (same : ∀ i : Fin 64, payloadDigit x i = payloadDigit y i) : x = y := by
  by_cases hx : needsFlip x
  · have hy : needsFlip y := by
      by_contra h
      simp [flagDigit, hx, h] at flag
    apply raw_digits_injective
    intro i
    have hi := same i
    simp only [payloadDigit, if_pos hx, if_pos hy] at hi
    have xb := rawDigit_lt_four x i
    have yb := rawDigit_lt_four y i
    omega
  · have hy : ¬needsFlip y := by
      intro h
      simp [flagDigit, hx, h] at flag
    apply raw_digits_injective
    intro i
    simpa only [payloadDigit, if_neg hx, if_neg hy] using same i

private theorem checksum_digits_le (x y : Nat) (hx : x ≤ 98) (hy : y ≤ 98)
    (digits : ∀ i, i < 4 → x / 4 ^ i % 4 ≤ y / 4 ^ i % 4) : x ≤ y := by
  exact base4_le 4 x y (by omega) (by omega) digits

theorem digits_antichain (x y : Digest)
    (ordered : ∀ i : Chain4, (digit x i).val ≤ (digit y i).val) : x = y := by
  have payloads : ∀ i : Fin 64, payloadDigit x i ≤ payloadDigit y i := by
    intro i
    have h := ordered ⟨i.val, by omega⟩
    simpa only [digit_payload] using h
  have flags : flagDigit x ≤ flagDigit y := by
    simpa only [digit_flag] using ordered ⟨64, by decide⟩
  have sum_le : payloadSum x + flagDigit x ≤ payloadSum y + flagDigit y := by
    unfold payloadSum
    exact Nat.add_le_add (Finset.sum_le_sum (fun i _ => payloads i)) flags
  have checksum_le' : checksum x ≤ checksum y := by
    apply checksum_digits_le _ _ (checksum_le x) (checksum_le y)
    intro i hi
    have h := ordered ⟨65 + i, by omega⟩
    simpa [digit, show ¬ 65 + i < 64 by omega,
      show 65 + i ≠ 64 by omega] using h
  have totals_x := checksum_add_payload x
  have totals_y := checksum_add_payload y
  have same_total : payloadSum x + flagDigit x = payloadSum y + flagDigit y := by omega
  have payload_sum_le : payloadSum x ≤ payloadSum y := by
    unfold payloadSum
    exact Finset.sum_le_sum (fun i _ => payloads i)
  have same_payload_sum : payloadSum x = payloadSum y := by omega
  have same_flag : flagDigit x = flagDigit y := by omega
  have same := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 64))) =>
    payloads i)).mp (by simpa only [payloadSum] using same_payload_sum)
  apply raw_of_payload_same_flag x y same_flag
  intro i
  exact same i (by simp)

theorem distinct_digest_has_earlier_digit (x y : Digest) (different : x ≠ y) :
    ∃ i : Chain4, (digit y i).val < (digit x i).val := by
  by_contra h
  push Not at h
  exact different (digits_antichain x y h)

def suffixCost (message : Digest) : Nat :=
  ∑ i : Chain4, (3 - (digit message i).val)

private theorem checksum_work_le (q : Nat) (hq : q ≤ 98) :
    q + 12 - (q % 4 + q / 4 % 4 + q / 16 % 4 + q / 64 % 4) ≤ 105 := by
  interval_cases q <;> decide

private def prefixCost (message : Digest) (count : Nat) : Nat :=
  ∑ i ∈ Finset.range count,
    (3 - (digit message ⟨i % 69, Nat.mod_lt _ (by decide)⟩).val)

private theorem prefix_succ (message : Digest) (count : Nat) (bound : count < 69) :
    prefixCost message (count + 1) = prefixCost message count +
      (3 - (digit message ⟨count, bound⟩).val) := by
  simp [prefixCost, Finset.sum_range_succ, Nat.mod_eq_of_lt bound]

private theorem prefix_payload (message : Digest) :
    prefixCost message 64 = 192 - payloadSum message := by
  unfold prefixCost
  rw [← Fin.sum_univ_eq_sum_range]
  have terms :
      (∑ i : Fin 64, (3 - (digit message ⟨i.val % 69, Nat.mod_lt _ (by decide)⟩).val)) =
      ∑ i : Fin 64, (3 - payloadDigit message i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.mod_eq_of_lt (by omega : i.val < 69), digit_payload]
  rw [terms, Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, payloadSum]
    rfl
  · intro i _
    have hi := payloadDigit_lt_four message i
    omega

private theorem prefix_payload_flag (message : Digest) :
    prefixCost message 65 = checksum message := by
  rw [prefix_succ message 64 (by decide), prefix_payload, digit_flag]
  have hf : flagDigit message ≤ 3 := by unfold flagDigit; split_ifs <;> decide
  have hp := payloadSum_le message
  have h := checksum_add_payload message
  omega

theorem suffix_cost_le (message : Digest) : suffixCost message ≤ 105 := by
  have qbound := checksum_le message
  have hprefix : suffixCost message = prefixCost message 69 := by
    unfold suffixCost prefixCost
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.mod_eq_of_lt i.isLt]
  rw [hprefix, prefix_succ message 68 (by decide), prefix_succ message 67 (by decide),
    prefix_succ message 66 (by decide), prefix_succ message 65 (by decide),
    prefix_payload_flag]
  have h0 : (digit message ⟨65, by decide⟩).val = checksum message % 4 := by
    simp [digit, checksum]
  have h1 : (digit message ⟨66, by decide⟩).val = checksum message / 4 % 4 := by
    simp [digit, checksum]
  have h2 : (digit message ⟨67, by decide⟩).val = checksum message / 16 % 4 := by
    simp [digit, checksum]
  have h3 : (digit message ⟨68, by decide⟩).val = checksum message / 64 % 4 := by
    simp [digit, checksum]
  rw [h0, h1, h2, h3]
  have hcost := checksum_work_le (checksum message) qbound
  have hmod0 := Nat.mod_lt (checksum message) (by decide : 0 < 4)
  have hmod1 := Nat.mod_lt (checksum message / 4) (by decide : 0 < 4)
  have hmod2 := Nat.mod_lt (checksum message / 16) (by decide : 0 < 4)
  have hmod3 := Nat.mod_lt (checksum message / 64) (by decide : 0 < 4)
  omega

end SigGolfCandidate.Hypertree.GroupedBalancedQuaternary
