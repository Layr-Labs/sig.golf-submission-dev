import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67

/-! Kernel-only arithmetic for the one-byte lookup decoder. Every lemma here uses ordinary Lean kernel checking, including the structural
bit-extraction identities. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteSum67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
open SigGolfCandidate.Hypertree.GroupedBalancedQuaternary
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private theorem extract_twice {w len : Nat} (x : BitVec w) (a b outLen : Nat)
    (hb : b + outLen ≤ len) :
  (x.extractLsb' a len).extractLsb' b outLen = x.extractLsb' (a+b) outLen := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_extractLsb']
  by_cases hi : i < outLen
  · have hinner : b + i < len := by omega
    simp [hi, hinner, Nat.add_assoc]
  · simp [hi]
private theorem digit_two {w : Nat} (x : BitVec w) (i : Nat) :
  (x.extractLsb' (2*i) 2).toNat = x.toNat /4^i %4 := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  congr 1
  rw [show 4^i = 2^(2*i) by simp [show (4:Nat) = 2^2 by decide, pow_mul]]

theorem byteSum_le (value : Nat) : byteSum value ≤ 12 := by
  unfold byteSum
  calc
    (∑ k : Fin 4, value / 4 ^ k.val % 4) ≤ ∑ _k : Fin 4, 3 := by
      apply Finset.sum_le_sum
      intro k _
      omega
    _ = 12 := by decide

theorem byteSum_byte (value : Nat) :
    (BitVec.ofNat 8 (byteSum value)).toNat = byteSum value := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have h := byteSum_le value; omega)

theorem byte_digit (message : BitVec 128) (j : Fin 16) (k : Fin 4) :
    (message.extractLsb' (8 * j.val) 8).toNat / 4 ^ k.val % 4 =
      message.toNat / 4 ^ (4 * j.val + k.val) % 4 := by
  have hleft :
      (message.extractLsb' (8 * j.val) 8).toNat / 4 ^ k.val % 4 =
      ((message.extractLsb' (8 * j.val) 8).extractLsb' (2 * k.val) 2).toNat := by
    exact (digit_two (message.extractLsb' (8 * j.val) 8) k.val).symm
  rw [hleft, extract_twice message (8 * j.val) (2 * k.val) 2 (by omega)]
  simpa only [show 8 * j.val + 2 * k.val = 2 * (4 * j.val + k.val) by omega] using
    digit_two message (4 * j.val + k.val)

def sumBytes (message : BitVec 128) : Nat :=
  ∑ j : Fin 16, byteSum (message.extractLsb' (8 * j.val) 8).toNat

theorem sumBytes_eq_rawSum (message : BitVec 128) :
    sumBytes message = rawSum message := by
  unfold sumBytes byteSum rawSum rawDigit
  calc
    (∑ j : Fin 16, ∑ k : Fin 4,
       (message.extractLsb' (8 * j.val) 8).toNat / 4 ^ k.val % 4) =
      ∑ p : Fin 16 × Fin 4,
        message.toNat / 4 ^ (4 * p.1.val + p.2.val) % 4 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact byte_digit message j k
    _ = ∑ i : Fin 64, message.toNat / 4 ^ i.val % 4 := by
      exact Fintype.sum_equiv (finProdFinEquiv : Fin 16 × Fin 4 ≃ Fin 64)
        (fun p => message.toNat / 4 ^ (4 * p.1.val + p.2.val) % 4)
        (fun i => message.toNat / 4 ^ i.val % 4)
        (by intro p; simp [finProdFinEquiv, Nat.add_comm])

#print axioms sumBytes_eq_rawSum

def decoderChecksum (message : BitVec 128) : Nat :=
  if sumBytes message < 96 then sumBytes message + 3
  else 192 - sumBytes message

theorem decoderChecksum_eq (message : BitVec 128) :
    decoderChecksum message = checksum message := by
  unfold decoderChecksum checksum
  rw [sumBytes_eq_rawSum]
  by_cases flip : rawSum message < 96
  · rw [if_pos flip, payloadSum_flip message flip]
    simp only [flagDigit, if_pos flip]
    have bound := rawSum_le message
    omega
  · rw [if_neg flip]
    have payload : payloadSum message = rawSum message := by
      simp only [payloadSum, payloadDigit, if_neg flip, rawSum]
    rw [payload]
    simp only [flagDigit, if_neg flip]
    omega

#print axioms decoderChecksum_eq

theorem selected_byte_digit (message : BitVec 128) (j : Fin 16) (k : Fin 4) :
    (if rawSum message < 96 then
      3 - rawByteDigit (message.extractLsb' (8*j.val) 8).toNat k.val
    else
      rawByteDigit (message.extractLsb' (8*j.val) 8).toNat k.val) =
      payloadDigit message ⟨4*j.val+k.val, by omega⟩ := by
  simp only [rawByteDigit, payloadDigit, rawDigit]
  rw [byte_digit message j k]

#print axioms selected_byte_digit


end SigGolfCandidate.Hypertree.GroupedBalancedByteSum67
