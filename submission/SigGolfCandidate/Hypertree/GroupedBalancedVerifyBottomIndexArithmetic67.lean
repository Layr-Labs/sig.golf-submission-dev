import SigGolfCandidate.Hypertree.GroupedMixedIndex

/-! The verifier's 192-bit scratch index is the 160-bit signed index at each
bottom-tree level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomIndexArithmetic67
open SigGolf SigGolfCandidate.Hypertree

def wide (index : BitVec 160) : BitVec 192 :=
  BitVec.ofNat 192 index.toNat

theorem wide_nat (index : BitVec 160) :
    (wide index).toNat = index.toNat := by
  simp only [wide, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans index.isLt (by decide))

theorem shifted_nat (index : BitVec 160) (k : Nat) :
    (wide index >>> k).toNat = index.toNat / 2^k := by
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    wide_nat]

theorem shifted_low_bit (index : BitVec 160) (k : Nat) :
    ((wide index >>> k) &&& (1 : BitVec 192)).toNat =
      index.toNat / 2^k % 2 := by
  rw [BitVec.toNat_and]
  change (wide index >>> k).toNat &&& 1 = index.toNat / 2^k % 2
  rw [Nat.and_one_is_mod, shifted_nat]

theorem shifted_low_word_bit (index : BitVec 160) (k : Nat) :
    (((wide index >>> k).extractLsb' 0 64) &&& (1 : BitVec 64)).toNat =
      index.toNat / 2^k % 2 := by
  rw [BitVec.toNat_and]
  change ((wide index >>> k).extractLsb' 0 64).toNat &&& 1 =
    index.toNat / 2^k % 2
  rw [Nat.and_one_is_mod, BitVec.extractLsb'_toNat]
  rw [show (wide index >>> k).toNat >>> 0 = (wide index >>> k).toNat by simp]
  rw [shifted_nat]
  rw [Nat.mod_mod_of_dvd]
  exact ⟨2^63, by decide⟩

theorem bit_zero_iff (index : BitVec 160) (k : Nat) :
    (((wide index >>> k).extractLsb' 0 64) &&& (1 : BitVec 64) = 0) ↔
      index.toNat / 2^k % 2 = 0 := by
  constructor
  · intro h
    have same := congrArg BitVec.toNat h
    rw [shifted_low_word_bit] at same
    simpa using same
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [shifted_low_word_bit]
    simpa using h

theorem shifted_parent (index : BitVec 160) (k : Nat) :
    ((wide index >>> k) >>> 1).toNat =
      index.toNat / 2^(k+1) := by
  calc
    ((wide index >>> k) >>> 1).toNat =
        (wide index >>> k).toNat / 2 := by
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    _ = (index.toNat / 2^k) / 2 := by rw [shifted_nat]
    _ = index.toNat / 2^(k+1) := by
      rw [Nat.div_div_eq_div_mul]
      simp only [pow_succ]

theorem ten_shifted_tree (index : BitVec 160) :
    (wide index >>> 10).toNat = GroupedMixedIndex.bottomTree index := by
  simpa only [GroupedMixedIndex.bottomTree] using shifted_nat index 10

#print axioms shifted_nat
#print axioms shifted_low_word_bit
#print axioms bit_zero_iff
#print axioms shifted_parent
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyBottomIndexArithmetic67
