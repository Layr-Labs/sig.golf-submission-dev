import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperBaseToInitial67

/-! A 192-bit selected index yields the concrete 8- or 16-leaf group fields. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexMask67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def mask3 : BitVec 192 := BitVec.ofNat 192 (2^192-8)
def mask4 : BitVec 192 := BitVec.ofNat 192 (2^192-16)

private theorem mask3_nat (n : Nat) (hn : n<2^192) :
    n &&& (2^192-8) = n/8*8 := by
  have hmod : (n &&& (2^192-8)) % 8 = 0 := by
    rw [show 8=2^3 from rfl,Nat.and_mod_two_pow,
      show (2^192-2^3)%2^3=0 from by decide]
    simp
  have hdiv : (n &&& (2^192-8)) / 8 = n/8 := by
    rw [show 8=2^3 from rfl,Nat.and_div_two_pow,
      show (2^192-2^3)/2^3=2^189-1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  have eucl := Nat.div_add_mod (n &&& (2^192-8)) 8
  omega

private theorem mask4_nat (n : Nat) (hn : n<2^192) :
    n &&& (2^192-16) = n/16*16 := by
  have hmod : (n &&& (2^192-16)) % 16 = 0 := by
    rw [show 16=2^4 from rfl,Nat.and_mod_two_pow,
      show (2^192-2^4)%2^4=0 from by decide]
    simp
  have hdiv : (n &&& (2^192-16)) / 16 = n/16 := by
    rw [show 16=2^4 from rfl,Nat.and_div_two_pow,
      show (2^192-2^4)/2^4=2^188-1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  have eucl := Nat.div_add_mod (n &&& (2^192-16)) 16
  omega

theorem mask3_value (index : BitVec 192) :
    (index &&& mask3).toNat=index.toNat/8*8 := by
  simp only [BitVec.toNat_and,mask3,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 2^192-8<2^192)]
  exact mask3_nat index.toNat index.isLt

theorem mask4_value (index : BitVec 192) :
    (index &&& mask4).toNat=index.toNat/16*16 := by
  simp only [BitVec.toNat_and,mask4,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 2^192-16<2^192)]
  exact mask4_nat index.toNat index.isLt

theorem mask3_low (index : BitVec 192) :
    (BitVec.ofNat 192 (index.toNat/8*8)).extractLsb' 0 64 =
      index.extractLsb' 0 64 &&& 18446744073709551608#64 := by
  rw [← mask3_value]
  rw [BitVec.ofNat_toNat]
  change (index &&& mask3).extractLsb' 0 64 = _
  rw [BitVec.extractLsb'_and]
  congr 1

theorem mask4_low (index : BitVec 192) :
    (BitVec.ofNat 192 (index.toNat/16*16)).extractLsb' 0 64 =
      index.extractLsb' 0 64 &&& 18446744073709551600#64 := by
  rw [← mask4_value]
  rw [BitVec.ofNat_toNat]
  change (index &&& mask4).extractLsb' 0 64 = _
  rw [BitVec.extractLsb'_and]
  congr 1

theorem mask3_upper (index : BitVec 192) (i : Fin 2) :
    (BitVec.ofNat 192 (index.toNat/8*8)).extractLsb' (64*(i.val+1)) 64 =
      index.extractLsb' (64*(i.val+1)) 64 := by
  rw [← mask3_value,BitVec.ofNat_toNat]
  change (index &&& mask3).extractLsb' (64*(i.val+1)) 64 = _
  rw [BitVec.extractLsb'_and]
  fin_cases i <;> simp [mask3]
  all_goals
    change _ &&& BitVec.allOnes 64 = _
    rw [BitVec.and_allOnes]

theorem mask4_upper (index : BitVec 192) (i : Fin 2) :
    (BitVec.ofNat 192 (index.toNat/16*16)).extractLsb' (64*(i.val+1)) 64 =
      index.extractLsb' (64*(i.val+1)) 64 := by
  rw [← mask4_value,BitVec.ofNat_toNat]
  change (index &&& mask4).extractLsb' (64*(i.val+1)) 64 = _
  rw [BitVec.extractLsb'_and]
  fin_cases i <;> simp [mask4]
  all_goals
    change _ &&& BitVec.allOnes 64 = _
    rw [BitVec.and_allOnes]

private theorem low_nat (index : BitVec 192) :
    (index.extractLsb' 0 64).toNat=index.toNat%2^64 := by
  simp [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

theorem selected3 (index : BitVec 192) :
    index.extractLsb' 0 64 &&& 7#64 =
      BitVec.ofNat 64 (index.toNat%8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,low_nat]
  simp only [BitVec.toNat_ofNat]
  have hm : 7%2^64=7 := by decide
  rw [hm]
  have hand := Nat.and_two_pow_sub_one_eq_mod (index.toNat%2^64) 3
  rw [show (7:Nat)=2^3-1 by decide,hand]
  have hdvd : 8 ∣ 2^64 := by decide
  rw [Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.mod_eq_of_lt (by omega : index.toNat%8<2^64)]

theorem selected4 (index : BitVec 192) :
    index.extractLsb' 0 64 &&& 15#64 =
      BitVec.ofNat 64 (index.toNat%16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,low_nat]
  simp only [BitVec.toNat_ofNat]
  have hm : 15%2^64=15 := by decide
  rw [hm]
  have hand := Nat.and_two_pow_sub_one_eq_mod (index.toNat%2^64) 4
  rw [show (15:Nat)=2^4-1 by decide,hand]
  have hdvd : 16 ∣ 2^64 := by decide
  rw [Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.mod_eq_of_lt (by omega : index.toNat%16<2^64)]

theorem h3_fields (s : MachineState) (index : BitVec 192)
    (words : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64) :
    s.getMem 0x81090 &&& 7#64 = BitVec.ofNat 64 (index.toNat%8) ∧
    s.getMem 0x81090 &&& 18446744073709551608#64 =
      (BitVec.ofNat 192 (index.toNat/8*8)).extractLsb' 0 64 ∧
    (∀ i, i<2 →
      s.getMem (Signing.wordAddress 0x81098 i)=
        (BitVec.ofNat 192 (index.toNat/8*8)).extractLsb' (64*(i+1)) 64) := by
  have low : s.getMem 0x81090=index.extractLsb' 0 64 := by
    simpa [Signing.wordAddress] using words (0 : Fin 3)
  refine ⟨by rw [low]; exact selected3 index,?_,?_⟩
  · rw [low]
    exact (mask3_low index).symm
  · intro i hi
    interval_cases i
    · have hword := words (1 : Fin 3)
      simpa [Signing.wordAddress] using hword.trans
        (mask3_upper index (0 : Fin 2)).symm
    · have hword := words (2 : Fin 3)
      simpa [Signing.wordAddress] using hword.trans
        (mask3_upper index (1 : Fin 2)).symm

theorem h4_fields (s : MachineState) (index : BitVec 192)
    (words : ∀ w : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 w.val)=
        index.extractLsb' (64*w.val) 64) :
    s.getMem 0x81090 &&& 15#64 = BitVec.ofNat 64 (index.toNat%16) ∧
    s.getMem 0x81090 &&& 18446744073709551600#64 =
      (BitVec.ofNat 192 (index.toNat/16*16)).extractLsb' 0 64 ∧
    (∀ i, i<2 →
      s.getMem (Signing.wordAddress 0x81098 i)=
        (BitVec.ofNat 192 (index.toNat/16*16)).extractLsb' (64*(i+1)) 64) := by
  have low : s.getMem 0x81090=index.extractLsb' 0 64 := by
    simpa [Signing.wordAddress] using words (0 : Fin 3)
  refine ⟨by rw [low]; exact selected4 index,?_,?_⟩
  · rw [low]
    exact (mask4_low index).symm
  · intro i hi
    interval_cases i
    · have hword := words (1 : Fin 3)
      simpa [Signing.wordAddress] using hword.trans
        (mask4_upper index (0 : Fin 2)).symm
    · have hword := words (2 : Fin 3)
      simpa [Signing.wordAddress] using hword.trans
        (mask4_upper index (1 : Fin 2)).symm

theorem h3_group_bounds (index : BitVec 192)
    (bound : index.toNat<2^160) :
    (index.toNat/8*8)%8=0 ∧
    index.toNat/8*8+8≤2^160 ∧
    index.toNat%8<8 := by
  have hm : 2^160%8=0 := by decide
  constructor
  · omega
  constructor
  · omega
  · omega

theorem h4_group_bounds (index : BitVec 192)
    (bound : index.toNat<2^160) :
    (index.toNat/16*16)%16=0 ∧
    index.toNat/16*16+16≤2^160 ∧
    index.toNat%16<16 := by
  have hm : 2^160%16=0 := by decide
  constructor
  · omega
  constructor
  · omega
  · omega

#print axioms mask3_value
#print axioms mask4_value
#print axioms mask3_low
#print axioms mask4_low
#print axioms mask3_upper
#print axioms mask4_upper
#print axioms selected3
#print axioms selected4
#print axioms h3_fields
#print axioms h4_fields
#print axioms h3_group_bounds
#print axioms h4_group_bounds
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexMask67
