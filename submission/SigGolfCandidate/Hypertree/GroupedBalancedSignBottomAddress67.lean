import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomFirstLeaf67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddress67
open SigGolf SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

def maskIndex : BitVec 160 := BitVec.ofNat 160 (2^160 - 1024)
def leafIndex (index : BitVec 160) : Nat := (index &&& maskIndex).toNat

theorem widenedSlice (x : BitVec 160) (start : Nat) :
    (BitVec.ofNat 192 x.toNat).extractLsb' start 64 =
      x.extractLsb' start 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]
  have hbound : x.toNat < 2^192 := lt_trans x.isLt (by decide)
  have hmod : x.toNat % 6277101735386680763835789423207666416102355444464034512896 = x.toNat := by
    simpa using Nat.mod_eq_of_lt hbound
  rw [hmod]

theorem leafLow (index : BitVec 160) :
    (BitVec.ofNat 192 (leafIndex index)).extractLsb' 0 64 =
      index.extractLsb' 0 64 &&& 18446744073709550592#64 := by
  rw [show BitVec.ofNat 192 (leafIndex index) =
    BitVec.ofNat 192 (index &&& maskIndex).toNat from rfl]
  rw [widenedSlice]
  rw [BitVec.extractLsb'_and]
  congr 1

theorem leafMid (index : BitVec 160) :
    (BitVec.ofNat 192 (leafIndex index)).extractLsb' 64 64 =
      index.extractLsb' 64 64 := by
  rw [show BitVec.ofNat 192 (leafIndex index) =
    BitVec.ofNat 192 (index &&& maskIndex).toNat from rfl]
  rw [widenedSlice]
  rw [BitVec.extractLsb'_and]
  have hm : maskIndex.extractLsb' 64 64 = BitVec.allOnes 64 := by decide
  rw [hm,BitVec.and_allOnes]

theorem leafHigh (index : BitVec 160) :
    (BitVec.ofNat 192 (leafIndex index)).extractLsb' 128 64 =
      (index.zeroExtend 192).extractLsb' 128 64 := by
  have z : index.zeroExtend 192 = BitVec.ofNat 192 index.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  rw [z,widenedSlice]
  change (BitVec.ofNat 192 (index &&& maskIndex).toNat).extractLsb' 128 64 = _
  rw [widenedSlice,BitVec.extractLsb'_and]
  have hm : maskIndex.extractLsb' 128 64 = BitVec.ofNat 64 (2^32 - 1) := by decide
  rw [hm]
  have hi : (index.extractLsb' 128 64).toNat < 2^32 := by
    simp [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
    have hb := index.isLt
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  change (index.extractLsb' 128 64).toNat &&& 4294967295 = _
  simpa only [show 2^32 - 1 = 4294967295 by decide] using
    (Nat.and_two_pow_sub_one_of_lt_two_pow (n := 32) hi)

theorem answerLow (answer : BitVec 256) :
    answer.extractLsb' 0 64 =
      (answer.extractLsb' 0 160).extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat,BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]

theorem answerMid (answer : BitVec 256) :
    answer.extractLsb' 64 64 =
      (answer.extractLsb' 0 160).extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat,BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]

theorem answerHigh (answer : BitVec 256) :
    ((answer.extractLsb' 128 64 <<< 32) >>> 32) =
      ((answer.extractLsb' 0 160).zeroExtend 192).extractLsb' 128 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,
    BitVec.extractLsb'_toNat,BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
  omega

#print axioms widenedSlice
#print axioms leafLow
#print axioms leafMid
#print axioms leafHigh
#print axioms answerLow
#print axioms answerMid
#print axioms answerHigh
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddress67
