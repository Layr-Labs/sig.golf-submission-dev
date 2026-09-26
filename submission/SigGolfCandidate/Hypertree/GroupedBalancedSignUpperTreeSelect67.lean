import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectData67

/-! The shared parent-tree callee accepts the moving upper signature pointer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeSelect67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev select := GroupedBalancedSignBottomTreeSelectPtr67.selectState
private abbrev copy := GroupedBalancedSignBottomTreeSelectCopy67.copyState

theorem destination_nat (s : MachineState) (level witnessBase : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000) :
    ((select s).getReg .x7).toNat = witnessBase + 16*level := by
  have small : witnessBase + 16*level < 2^64 := by omega
  rw [GroupedBalancedSignBottomTreeSelectData67.selected_destination,
    levelWord,witness,BitVec.toNat_add,BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq,BitVec.toNat_ofNat]
  simp only [show (2:Nat)^4 = 16 by decide]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : level < 2^64),
    Nat.mod_eq_of_lt (by omega : witnessBase < 2^64),
    Nat.mod_eq_of_lt (by omega : level*16 < 2^64),
    Nat.mod_eq_of_lt (by omega : level*16 + witnessBase < 2^64)]
  omega

theorem destination_access (s : MachineState) (level witnessBase k : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (aligned : witnessBase % 8 = 0)
    (offsetBound : k ≤ 8) (offsetAlign : k % 8 = 0) :
    accessValid ((select s).getReg .x7 + BitVec.ofNat 64 k) 8 = true := by
  have ptr := destination_nat s level witnessBase levelWord witness
    levelBound witnessBound
  have addr : ((select s).getReg .x7 + BitVec.ofNat 64 k).toNat =
      witnessBase + 16*level + k := by
    rw [BitVec.toNat_add,ptr,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k < 2^64),
      Nat.mod_eq_of_lt (by omega : witnessBase+16*level+k < 2^64)]
  simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
  rw [addr]
  constructor
  · change witnessBase + 16*level + k + 8 ≤ 16777216
    omega
  · omega

theorem destination_below_high (s : MachineState) (level witnessBase : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000) :
    ((select s).getReg .x7).toNat < 0x80000 ∧
    ((select s).getReg .x7 + 8).toNat < 0x80000 := by
  have ptr := destination_nat s level witnessBase levelWord witness
    levelBound witnessBound
  constructor
  · rw [ptr]; omega
  · rw [BitVec.toNat_add,ptr]
    change (witnessBase+16*level+8) % 2^64 < 0x80000
    rw [Nat.mod_eq_of_lt (by omega : witnessBase+16*level+8 < 2^64)]
    omega

theorem copied_high_frame (s : MachineState) (level witnessBase : Nat)
    (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witness : s.getMem 0x810f8 = BitVec.ofNat 64 witnessBase)
    (levelBound : level < 10)
    (witnessBound : witnessBase + 16*level + 16 ≤ 0x80000)
    (high : 0x80000 ≤ a.toNat) :
    (copy (select s)).getMem a = s.getMem a := by
  obtain ⟨low,upper⟩ := destination_below_high s level witnessBase
    levelWord witness levelBound witnessBound
  apply GroupedBalancedSignBottomTreeSelectData67.copied_frame s a
  · intro eq
    have h : a.toNat = ((select s).getReg .x7).toNat :=
      congrArg BitVec.toNat eq
    omega
  · intro eq
    have h : a.toNat = ((select s).getReg .x7 + 8).toNat :=
      congrArg BitVec.toNat eq
    omega

#print axioms destination_nat
#print axioms destination_access
#print axioms copied_high_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTreeSelect67
