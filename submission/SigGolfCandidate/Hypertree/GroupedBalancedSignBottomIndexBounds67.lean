import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomAddress67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomIndexBounds67
open SigGolf SigGolfCandidate.Hypertree
open GroupedBalancedSignBottomAddress67

 theorem leafIndex_align (index : BitVec 160) : leafIndex index % 1024 = 0 := by
  have hlow : (index &&& maskIndex).extractLsb' 0 10 = (0 : BitVec 10) := by
    rw [BitVec.extractLsb'_and]
    have hmask : maskIndex.extractLsb' 0 10 = (0 : BitVec 10) := by decide
    rw [hmask]
    simp
  have hlowNat := congrArg BitVec.toNat hlow
  simpa [leafIndex,BitVec.extractLsb'_toNat] using hlowNat

 theorem leafIndex_bound (index : BitVec 160) : leafIndex index + 1024 ≤ 2^160 := by
  have ha := leafIndex_align index
  have hb := (index &&& maskIndex).isLt
  change leafIndex index < 2^160 at hb
  have hp : 2^160 % 1024 = 0 := by decide
  omega

theorem leafIndex_plus_low (index : BitVec 160) :
     leafIndex index + (index.extractLsb' 0 10).toNat = index.toNat := by
  have maskCompl : maskIndex = ~~~(1023 : BitVec 160) := by decide
  have lowBits : index &&& (1023 : BitVec 160) =
      (index.extractLsb' 0 10).zeroExtend 160 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.extractLsb'_toNat,
      BitVec.toNat_setWidth]
    change index.toNat &&& 1023 = (index.toNat % 1024) % 2^160
    rw [show 1023 = 2^10 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    have h : index.toNat % 1024 < 2^160 := by omega
    rw [Nat.mod_eq_of_lt h]
  have disjoint : (index &&& maskIndex) &&&
      (index &&& (1023 : BitVec 160)) = 0 := by
    calc
      _ = index &&& (index &&& (1023 &&& maskIndex)) := by ac_rfl
      _ = index &&& (index &&& (1023 &&& ~~~(1023 : BitVec 160))) := by rw [maskCompl]
      _ = 0 := by
        rw [BitVec.and_not_self]
        simp
  have covers : (index &&& maskIndex) |||
      (index &&& (1023 : BitVec 160)) = index := by
    have allOnes : maskIndex ||| (1023 : BitVec 160) = BitVec.allOnes 160 := by
      rw [maskCompl]
      exact BitVec.not_or_self _
    rw [← BitVec.and_or_distrib_left, allOnes, BitVec.and_allOnes]
  have split : index =
      (index &&& maskIndex) + (index.extractLsb' 0 10).zeroExtend 160 := by
    rw [← lowBits, BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, covers]
  have bound : leafIndex index + (index.extractLsb' 0 10).toNat < 2^160 := by
    have h := leafIndex_bound index
    have l := (index.extractLsb' 0 10).isLt
    omega
  have lowEq : ((index.extractLsb' 0 10).zeroExtend 160).toNat =
      (index.extractLsb' 0 10).toNat := by
    simp [BitVec.toNat_setWidth]
    have hi := index.isLt
    omega
  have eq := congrArg BitVec.toNat split
  simp only [BitVec.toNat_add] at eq
  rw [lowEq] at eq
  change index.toNat =
    (leafIndex index + (index.extractLsb' 0 10).toNat) % 2^160 at eq
  rw [Nat.mod_eq_of_lt bound] at eq
  exact eq.symm

theorem low_word_eq_low (index : BitVec 160) :
     ((index.extractLsb' 0 64) &&& (1023 : BitVec 64)).toNat =
       (index.extractLsb' 0 10).toNat := by
  simp only [BitVec.toNat_and, BitVec.extractLsb'_toNat]
  change (index.toNat % 2^64) &&& 1023 = index.toNat % 2^10
  rw [show 1023 = 2^10 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd]
  decide

#print axioms leafIndex_align
#print axioms leafIndex_bound
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomIndexBounds67
