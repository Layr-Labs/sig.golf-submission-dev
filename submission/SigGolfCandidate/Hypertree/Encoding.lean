import SigGolfCandidate.Hypertree.GroupedBalanced
import RiscvZkvm.Rv64.Instructions

namespace SigGolfCandidate.Hypertree.Reference
open RiscvZkvm.Rv64

private theorem imm_neg151 :
    signExtend12 (-151 : BitVec 12) = (18446744073709551465 : Word) := by
  decide

private theorem nat_branch (c : Nat) (bound : c ≤ 301) :
    ((c + 18446744073709551465) % 18446744073709551616) / 9223372036854775808 =
      if c < 151 then 1 else 0 := by
  by_cases h : c < 151
  · rw [if_pos h, Nat.mod_eq_of_lt
      (by omega : c + 18446744073709551465 < 18446744073709551616)]
    omega
  · have heq : c + 18446744073709551465 = (c - 151) + 18446744073709551616 := by omega
    rw [if_neg h, heq, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : c - 151 < 18446744073709551616)]
    exact Nat.div_eq_of_lt (by omega)

private theorem branch_lhs_nat (c : Nat) (bound : c ≤ 301) :
    (((BitVec.ofNat 64 c + signExtend12 (-151 : BitVec 12)) >>> 63) : Word).toNat =
      ((c + 18446744073709551465) % 18446744073709551616) / 9223372036854775808 := by
  rw [imm_neg151, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add]
  have hc : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64)]
  have hm : (18446744073709551465 : Word).toNat = 18446744073709551465 := by decide
  rw [hc, hm]

/-- The signed ADDI/SRLI branch bit selects the balanced payload flip. -/
theorem rawChecksum_branchBit (c : Nat) (bound : c ≤ 301) :
    ((BitVec.ofNat 64 c + signExtend12 (-151 : BitVec 12)) >>> 63) =
      if c < 151 then (1 : Word) else (0 : Word) := by
  apply BitVec.eq_of_toNat_eq
  rw [branch_lhs_nat c bound, nat_branch c bound]
  split_ifs <;> decide

/-- info: 'SigGolfCandidate.Hypertree.Reference.rawChecksum_branchBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rawChecksum_branchBit

/-- The raw loop checksum crosses 150 exactly when the payload flips. -/
theorem needsFlip_iff_rawChecksum_gt_150 (message : Digest) :
    needsFlip message ↔ 150 < 301 - rawSum message := by
  have bound : rawSum message ≤ 301 := Balanced.raw_sum_le message
  change rawSum message < 151 ↔ 150 < 301 - rawSum message
  omega

/-- The retained raw message digits feed the balanced payload transform. -/
theorem payloadDigit_eq_balanced (message : Digest) (i : Fin 43) :
    payloadDigit message i = Balanced.payloadDigit message i := by
  rfl

theorem checksum_eq_balanced (message : Digest) :
    checksum message = Balanced.checksum message := by
  rfl

theorem checksum_le_balanced (message : Digest) : checksum message ≤ 150 := by
  exact Balanced.checksum_le message

theorem checksum_of_flip (message : Digest) (flip : needsFlip message) :
    checksum message = rawSum message := by
  have payload : payloadSum message = 301 - rawSum message :=
    Balanced.payload_sum_flip message flip
  have bound : rawSum message ≤ 301 := Balanced.raw_sum_le message
  unfold checksum
  omega

theorem checksum_of_no_flip (message : Digest) (flip : ¬ needsFlip message) :
    checksum message = 301 - rawSum message := by
  have same : payloadSum message = rawSum message := by
    unfold payloadSum
    simp only [payloadDigit, if_neg flip]
    rfl
  simp only [checksum, same]

/-- The bytecode reference and standalone balanced encoding use the same digits. -/
theorem digit_eq_balanced (message : Digest) (i : Chain) :
    digit message i = Balanced.digit message i := by
  rfl

/-- No different digest can be forged by advancing every revealed chain. -/
theorem digits_antichain (x y : Digest)
    (ordered : ∀ i : Chain, (digit x i).val ≤ (digit y i).val) : x = y := by
  apply Balanced.digits_antichain
  intro i
  simpa only [← digit_eq_balanced] using ordered i

theorem distinct_digest_has_earlier_digit (x y : Digest) (different : x ≠ y) :
    ∃ i : Chain, (digit y i).val < (digit x i).val := by
  by_contra h
  push Not at h
  exact different (digits_antichain x y h)

/-- info: 'SigGolfCandidate.Hypertree.Reference.digits_antichain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digits_antichain

end SigGolfCandidate.Hypertree.Reference
