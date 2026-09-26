import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectCopy67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev select := GroupedBalancedSignBottomTreeSelectPtr67.selectState
private abbrev copy := GroupedBalancedSignBottomTreeSelectCopy67.copyState
theorem selected_source (s : MachineState) :
    (select s).getReg .x6 =
      ((((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat % 64)) ^^^ 1) <<< 4) +
        s.getMem 0x810c0) := by
  simp [GroupedBalancedSignBottomTreeSelectPtr67.selectState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem selected_destination (s : MachineState) :
    (select s).getReg .x7 =
      (s.getMem 0x81050 <<< 4) + s.getMem 0x810f8 := by
  simp [GroupedBalancedSignBottomTreeSelectPtr67.selectState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem selected_index_bound (s : MachineState)
    (bounded : (s.getMem 0x810e8).toNat < 1024) :
    (((s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat % 64)) ^^^
      (1 : Word))).toNat < 1024 := by
  have shifted :
      (s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat % 64)).toNat <
        2^10 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have le := Nat.div_le_self (s.getMem 0x810e8).toNat
      (2 ^ ((s.getMem 0x81050).toNat % 64))
    omega
  rw [BitVec.toNat_xor]
  exact Nat.xor_lt_two_pow shifted (by decide)
private def siblingIndex (s : MachineState) : Word :=
  (s.getMem 0x810e8 >>> ((s.getMem 0x81050).toNat % 64)) ^^^ 1
theorem selected_source_nat (s : MachineState) (base : Nat)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000)
    (bounded : (s.getMem 0x810e8).toNat < 1024) :
    ((select s).getReg .x6).toNat = base + 16 * (siblingIndex s).toNat := by
  have indexBound : (siblingIndex s).toNat < 1024 :=
    selected_index_bound s bounded
  have shiftBound : 16 * (siblingIndex s).toNat < 2^64 := by omega
  have sumBound : base + 16 * (siblingIndex s).toNat < 2^64 := by
    rcases baseCase with rfl | rfl <;> omega
  rw [selected_source,source,BitVec.toNat_add,BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq,BitVec.toNat_ofNat]
  simp only [show (2:Nat)^4 = 16 by decide]
  change (((siblingIndex s).toNat * 16 % 2^64 + base % 2^64) % 2^64) = _
  rw [Nat.mul_comm (siblingIndex s).toNat 16]
  rw [Nat.mod_eq_of_lt (by omega : base < 2^64),
    Nat.mod_eq_of_lt shiftBound,
    Nat.add_comm (16 * (siblingIndex s).toNat) base,
    Nat.mod_eq_of_lt sumBound]
theorem source_access (s : MachineState) (base k : Nat)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000)
    (bounded : (s.getMem 0x810e8).toNat < 1024)
    (offsetBound : k ≤ 8) (offsetAlign : k % 8 = 0) :
    accessValid ((select s).getReg .x6 + BitVec.ofNat 64 k) 8 = true := by
  have idxBound : (siblingIndex s).toNat < 1024 :=
    selected_index_bound s bounded
  have ptrNat := selected_source_nat s base source baseCase bounded
  have noWrap : base + 16 * (siblingIndex s).toNat + k < 2^64 := by
    rcases baseCase with rfl | rfl <;> omega
  have addrNat :
      ((select s).getReg .x6 + BitVec.ofNat 64 k).toNat =
        base + 16 * (siblingIndex s).toNat + k := by
    rw [BitVec.toNat_add,ptrNat,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2^64),Nat.mod_eq_of_lt noWrap]
  simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
  rw [addrNat]
  constructor
  · change base + 16 * (siblingIndex s).toNat + k + 8 ≤ 16777216
    rcases baseCase with rfl | rfl <;> omega
  · rcases baseCase with rfl | rfl <;> omega
theorem selected_destination_nat (s : MachineState) (level : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10) :
    ((select s).getReg .x7).toNat = 0x20090 + 16 * level := by
  have levelSmall : level < 2^64 := by omega
  have shiftSmall : 16 * level < 2^64 := by omega
  have sumSmall : 0x20090 + 16 * level < 2^64 := by omega
  rw [selected_destination,levelWord,witnessBase,
    BitVec.toNat_add,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt levelSmall]
  change ((level * 16 % 2^64 + 0x20090) % 2^64) = _
  rw [Nat.mul_comm level 16,Nat.mod_eq_of_lt shiftSmall,
    Nat.add_comm (16 * level) 0x20090,Nat.mod_eq_of_lt sumSmall]
theorem destination_access (s : MachineState) (level k : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (offsetBound : k ≤ 8) (offsetAlign : k % 8 = 0) :
    accessValid ((select s).getReg .x7 + BitVec.ofNat 64 k) 8 = true := by
  have ptrNat := selected_destination_nat s level levelWord witnessBase levelBound
  have noWrap : 0x20090 + 16 * level + k < 2^64 := by omega
  have addrNat :
      ((select s).getReg .x7 + BitVec.ofNat 64 k).toNat =
        0x20090 + 16 * level + k := by
    rw [BitVec.toNat_add,ptrNat,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2^64),Nat.mod_eq_of_lt noWrap]
  simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
  rw [addrNat]
  constructor
  · change 0x20090 + 16 * level + k + 8 ≤ 16777216
    omega
  · omega
theorem destination_below_high (s : MachineState) (level : Nat)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10) :
    ((select s).getReg .x7).toNat < 0x80000 ∧
    ((select s).getReg .x7 + 8).toNat < 0x80000 := by
  have ptrNat := selected_destination_nat s level levelWord witnessBase levelBound
  constructor
  · rw [ptrNat]; omega
  · rw [BitVec.toNat_add,ptrNat]
    change (0x20090 + 16 * level + 8) % 2^64 < 0x80000
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
theorem select_frame (s : MachineState) (a : Word) :
    (select s).getMem a = s.getMem a := by
  simp [GroupedBalancedSignBottomTreeSelectPtr67.selectState,execInstrBr]
theorem copied_low (s : MachineState)
    (distinct : (select s).getReg .x7 ≠ (select s).getReg .x7 + 8) :
    (copy (select s)).getMem ((select s).getReg .x7) =
      s.getMem ((select s).getReg .x6) := by
  simp [GroupedBalancedSignBottomTreeSelectCopy67.copyState,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    distinct,select_frame]
theorem copied_high (s : MachineState) :
    (copy (select s)).getMem ((select s).getReg .x7 + 8) =
      s.getMem ((select s).getReg .x6 + 8) := by
  simp [GroupedBalancedSignBottomTreeSelectCopy67.copyState,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    select_frame]
theorem copied_frame (s : MachineState) (a : Word)
    (h0 : a ≠ (select s).getReg .x7)
    (h1 : a ≠ (select s).getReg .x7 + 8) :
    (copy (select s)).getMem a = s.getMem a := by
  have n0 : ¬ (select s).getReg .x7 = a := Ne.symm h0
  have n1 : ¬ (select s).getReg .x7 + 8 = a := Ne.symm h1
  rw [show (copy (select s)).getMem a = (select s).getMem a from by
    simp [GroupedBalancedSignBottomTreeSelectCopy67.copyState,execInstrBr,
      signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      h0,h1,n0,n1]
    intro heq
    exact False.elim (h1 heq)]
  exact select_frame s a
theorem copied_high_frame (s : MachineState) (level : Nat) (a : Word)
    (levelWord : s.getMem 0x81050 = BitVec.ofNat 64 level)
    (witnessBase : s.getMem 0x810f8 = 0x20090)
    (levelBound : level < 10)
    (high : 0x80000 ≤ a.toNat) :
    (copy (select s)).getMem a = s.getMem a := by
  obtain ⟨low,upper⟩ := destination_below_high s level levelWord witnessBase levelBound
  apply copied_frame s a
  · intro eq
    have := congrArg BitVec.toNat eq
    omega
  · intro eq
    have := congrArg BitVec.toNat eq
    omega
#print axioms selected_source
#print axioms selected_destination
#print axioms selected_index_bound
#print axioms selected_source_nat
#print axioms source_access
#print axioms selected_destination_nat
#print axioms destination_access
#print axioms destination_below_high
#print axioms select_frame
#print axioms copied_low
#print axioms copied_high
#print axioms copied_frame
#print axioms copied_high_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectData67
