import SigGolfCandidate.Hypertree.Reference

namespace SigGolfCandidate.Hypertree.Balanced
open SigGolf Reference
set_option maxRecDepth 4096

def rawSum (message : Digest) : Nat :=
  ∑ i : Fin 43, messageDigit message i

abbrev needsFlip (message : Digest) : Prop := rawSum message < 151

def payloadDigit (message : Digest) (i : Fin 43) : Nat :=
  if needsFlip message then 7 - messageDigit message i else messageDigit message i

def payloadSum (message : Digest) : Nat :=
  ∑ i : Fin 43, payloadDigit message i

def checksum (message : Digest) : Nat := 301 - payloadSum message

def digit (message : Digest) (i : Chain) : Fin 8 :=
  ⟨(if i.val < 43 then payloadDigit message ⟨i.val % 43, Nat.mod_lt _ (by decide)⟩
    else checksum message / 8 ^ (i.val - 43)) % 8,
    Nat.mod_lt _ (by decide)⟩

private theorem base8_le (count m n : Nat) (hm : m < 8 ^ count) (hn : n < 8 ^ count)
    (digits : ∀ i, i < count → m / 8 ^ i % 8 ≤ n / 8 ^ i % 8) : m ≤ n := by
  induction count generalizing m n with
  | zero => simp only [pow_zero] at hm hn; omega
  | succ count ih =>
    have hm' : m / 8 < 8 ^ count := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ] using hm
    have hn' : n / 8 < 8 ^ count := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa only [pow_succ] using hn
    have tails : m / 8 ≤ n / 8 := ih _ _ hm' hn' (by
      intro i hi
      have h := digits (i + 1) (by omega)
      simpa only [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using h)
    have heads := digits 0 (by omega)
    simp only [pow_zero, Nat.div_one] at heads
    omega

private theorem raw_digits_injective (x y : Digest)
    (same : ∀ i : Fin 43, messageDigit x i = messageDigit y i) : x = y := by
  have xb : x.toNat < 8 ^ 43 := lt_of_lt_of_le x.isLt (by decide)
  have yb : y.toNat < 8 ^ 43 := lt_of_lt_of_le y.isLt (by decide)
  apply BitVec.eq_of_toNat_eq
  apply Nat.le_antisymm
  · apply base8_le 43 _ _ xb yb
    intro i hi
    exact (same ⟨i, hi⟩).le
  · apply base8_le 43 _ _ yb xb
    intro i hi
    exact (same ⟨i, hi⟩).ge

private theorem raw_digit_lt_eight (message : Digest) (i : Fin 43) :
    messageDigit message i < 8 := by
  unfold messageDigit
  exact Nat.mod_lt _ (by decide)

theorem raw_sum_le (message : Digest) : rawSum message ≤ 301 := by
  unfold rawSum
  calc
    _ ≤ ∑ _i : Fin 43, (7 : Nat) := Finset.sum_le_sum (fun i _ => by
      have hi := raw_digit_lt_eight message i
      omega)
    _ = 301 := by simp

theorem top_digit_lt_four (message : Digest) :
    messageDigit message ⟨42, by decide⟩ < 4 := by
  have h : message.toNat / 8 ^ 42 < 4 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    have eq : 8 ^ 42 * 4 = 2 ^ 128 := by decide
    rw [Nat.mul_comm 4, eq]
    exact message.isLt
  change message.toNat / 8 ^ 42 % 8 < 4
  exact lt_of_le_of_lt (Nat.mod_le _ _) h

theorem payload_injective (x y : Digest)
    (same : ∀ i : Fin 43, payloadDigit x i = payloadDigit y i) : x = y := by
  by_cases hx : needsFlip x
  · by_cases hy : needsFlip y
    · apply raw_digits_injective
      intro i
      have hi := same i
      simp only [payloadDigit, if_pos hx, if_pos hy] at hi
      have xb := raw_digit_lt_eight x i
      have yb := raw_digit_lt_eight y i
      omega
    · have hi := same ⟨42, by decide⟩
      simp only [payloadDigit, if_pos hx, if_neg hy] at hi
      have xb := top_digit_lt_four x
      have yb := top_digit_lt_four y
      omega
  · by_cases hy : needsFlip y
    · have hi := same ⟨42, by decide⟩
      simp only [payloadDigit, if_neg hx, if_pos hy] at hi
      have xb := top_digit_lt_four x
      have yb := top_digit_lt_four y
      omega
    · apply raw_digits_injective
      intro i
      have hi := same i
      simpa only [payloadDigit, if_neg hx, if_neg hy] using hi

theorem payload_digit_lt_eight (message : Digest) (i : Fin 43) :
    payloadDigit message i < 8 := by
  unfold payloadDigit
  split_ifs
  · have hi := raw_digit_lt_eight message i
    omega
  · exact raw_digit_lt_eight message i

theorem payload_sum_le (message : Digest) : payloadSum message ≤ 301 := by
  unfold payloadSum
  calc
    _ ≤ ∑ _i : Fin 43, (7 : Nat) := Finset.sum_le_sum (fun i _ => by
      have hi := payload_digit_lt_eight message i
      omega)
    _ = 301 := by simp

theorem payload_sum_flip (message : Digest) (flip : needsFlip message) :
    payloadSum message = 301 - rawSum message := by
  unfold payloadSum
  simp only [payloadDigit, if_pos flip]
  rw [Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rfl
  · intro i _
    have hi := raw_digit_lt_eight message i
    omega

theorem payload_sum_ge (message : Digest) : 151 ≤ payloadSum message := by
  by_cases h : needsFlip message
  · rw [payload_sum_flip message h]
    have hs : rawSum message < 151 := h
    omega
  · have hs : 151 ≤ rawSum message := by change ¬ rawSum message < 151 at h; omega
    simpa only [payloadSum, payloadDigit, if_neg h, rawSum] using hs

theorem checksum_le (message : Digest) : checksum message ≤ 150 := by
  unfold checksum
  have h := payload_sum_ge message
  omega

theorem digits_antichain (x y : Digest)
    (ordered : ∀ i : Chain, (digit x i).val ≤ (digit y i).val) : x = y := by
  have messages : ∀ i : Fin 43, payloadDigit x i ≤ payloadDigit y i := by
    intro i
    have h := ordered ⟨i.val, by omega⟩
    simpa only [digit, i.isLt, ↓reduceIte, Nat.mod_eq_of_lt
      (payload_digit_lt_eight x i), Nat.mod_eq_of_lt
      (payload_digit_lt_eight y i), Nat.mod_eq_of_lt i.isLt] using h
  have sum_le : payloadSum x ≤ payloadSum y := by
    unfold payloadSum
    exact Finset.sum_le_sum (fun i _ => messages i)
  have checksum_le' : checksum x ≤ checksum y := by
    apply base8_le 3
    · have := checksum_le x; omega
    · have := checksum_le y; omega
    · intro i hi
      have h := ordered ⟨43 + i, by omega⟩
      simpa [digit, show ¬ 43 + i < 43 by omega] using h
  have xbound := payload_sum_le x
  have ybound := payload_sum_le y
  have same_sum : payloadSum x = payloadSum y := by
    unfold checksum at checksum_le'
    omega
  have same := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 43))) =>
    messages i)).mp (by simpa only [payloadSum] using same_sum)
  apply payload_injective
  intro i
  exact same i (by simp)

theorem distinct_digest_has_earlier_digit (x y : Digest) (different : x ≠ y) :
    ∃ i : Chain, (digit y i).val < (digit x i).val := by
  by_contra h
  push Not at h
  exact different (digits_antichain x y h)

/-- For the balanced checksum q≤150, its three base-eight digits prevent
q's suffix work plus checksum suffix work from exceeding 161 hashes. -/
theorem checksum_work_le (q : Nat) (bound : q ≤ 150) :
    q + 21 - (q % 8 + q / 8 % 8 + q / 64 % 8) ≤ 161 := by
  have low := Nat.mod_lt q (by decide : 0 < 8)
  have mid := Nat.mod_lt (q / 8) (by decide : 0 < 8)
  have high : q / 64 < 8 := by omega
  rw [Nat.mod_eq_of_lt high]
  omega

def chainPrefix (message : Digest) (count : Nat) : Nat :=
  ∑ i ∈ Finset.range count,
    (7 - (digit message ⟨i % 46, Nat.mod_lt _ (by decide)⟩).val)

private theorem digit_payload (message : Digest) (i : Fin 43) :
    (digit message ⟨i.val, by omega⟩).val = payloadDigit message i := by
  simp [digit, i.isLt, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt (payload_digit_lt_eight message i)]

private theorem prefix_succ (message : Digest) (count : Nat) (bound : count < 46) :
    chainPrefix message (count + 1) = chainPrefix message count +
      (7 - (digit message ⟨count, bound⟩).val) := by
  simp [chainPrefix, Finset.sum_range_succ, Nat.mod_eq_of_lt bound]

private theorem prefix_message (message : Digest) :
    chainPrefix message 43 = checksum message := by
  unfold chainPrefix checksum
  rw [← Fin.sum_univ_eq_sum_range]
  have terms :
      (∑ i : Fin 43, (7 - (digit message ⟨i.val % 46, Nat.mod_lt _ (by decide)⟩).val)) =
      ∑ i : Fin 43, (7 - payloadDigit message i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.mod_eq_of_lt (by omega : i.val < 46), digit_payload]
  rw [terms, Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, payloadSum]
    rfl
  · intro i _
    have hi := payload_digit_lt_eight message i
    omega

theorem chain_prefix_bound (message : Digest) : chainPrefix message 46 ≤ 161 := by
  have qbound := checksum_le message
  rw [prefix_succ message 45 (by decide), prefix_succ message 44 (by decide),
    prefix_succ message 43 (by decide), prefix_message]
  have h0 : (digit message ⟨43, by decide⟩).val = checksum message % 8 := by
    simp [digit, checksum]
  have h1 : (digit message ⟨44, by decide⟩).val = checksum message / 8 % 8 := by
    simp [digit, checksum]
  have h2 : (digit message ⟨45, by decide⟩).val = checksum message / 64 % 8 := by
    simp [digit, checksum]
  rw [h0, h1, h2]
  have low := Nat.mod_lt (checksum message) (by decide : 0 < 8)
  have mid := Nat.mod_lt (checksum message / 8) (by decide : 0 < 8)
  have high := Nat.mod_lt (checksum message / 64) (by decide : 0 < 8)
  have hcost := checksum_work_le (checksum message) qbound
  omega

end SigGolfCandidate.Hypertree.Balanced
