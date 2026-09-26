import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentTick67
import SigGolfCandidate.Hypertree.KeygenDomain
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePointerData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
theorem pair_reg (s : MachineState) :
    (GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7 =
      (s.getMem 0x810d8 <<< 5) + s.getMem 0x810c0 := by
  simp [GroupedBalancedSignBottomTreePairPtrLoop67.pairState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem pair_frame (s : MachineState) (a : Word) :
    (GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getMem a =
      s.getMem a := by
  simp [GroupedBalancedSignBottomTreePairPtrLoop67.pairState,execInstrBr]
theorem store_reg (s : MachineState) :
    (GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7 =
      (s.getMem 0x810d8 <<< 4) + s.getMem 0x810c8 := by
  simp [GroupedBalancedSignBottomTreeHashStorePtr67.storeState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem pair_reg_nat (s : MachineState) (count base : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base) :
    (GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7 =
      BitVec.ofNat 64 (base + 32 * count) := by
  rw [pair_reg,counter,source,KeygenDomain.shift_ofNat]
  simp [BitVec.ofNat_add,BitVec.ofNat_mul,mul_comm] <;> ac_rfl
theorem store_reg_nat (s : MachineState) (count base : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (target : s.getMem 0x810c8 = BitVec.ofNat 64 base) :
    (GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7 =
      BitVec.ofNat 64 (base + 16 * count) := by
  rw [store_reg,counter,target,KeygenDomain.shift_ofNat]
  simp [BitVec.ofNat_add,BitVec.ofNat_mul,mul_comm] <;> ac_rfl
theorem pair_access (s : MachineState) (count base k : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (source : s.getMem 0x810c0 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000)
    (countBound : count < 512) (offsetBound : k ≤ 24)
    (offsetAlign : k % 8 = 0) :
    accessValid
      ((GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7 +
        BitVec.ofNat 64 k) 8 = true := by
  have ptr := pair_reg_nat s count base counter source
  have baseBound : base + 32 * count + k + 8 < 2 ^ 64 := by
    rcases baseCase with rfl | rfl <;> omega
  have ptrBound : base + 32 * count < 2 ^ 64 := by omega
  have ptrNat :
      ((GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7).toNat =
        base + 32 * count := by
    rw [ptr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ptrBound]
  have addrNat :
      ((GroupedBalancedSignBottomTreePairPtrLoop67.pairState s).getReg .x7 +
        BitVec.ofNat 64 k).toNat = base + 32 * count + k := by
    rw [BitVec.toNat_add,ptrNat,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
    rw [Nat.mod_eq_of_lt (by omega : base + 32 * count + k < 2 ^ 64)]
  simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
  rw [addrNat]
  constructor
  · change base + 32 * count + k + 8 ≤ 16777216
    rcases baseCase with rfl | rfl <;> omega
  · rcases baseCase with rfl | rfl <;> omega
theorem store_access (s : MachineState) (count base k : Nat)
    (counter : s.getMem 0x810d8 = BitVec.ofNat 64 count)
    (target : s.getMem 0x810c8 = BitVec.ofNat 64 base)
    (baseCase : base = 0x83000 ∨ base = 0x88000)
    (countBound : count < 512) (offsetBound : k ≤ 8)
    (offsetAlign : k % 8 = 0) :
    accessValid
      ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7 +
        BitVec.ofNat 64 k) 8 = true := by
  have ptr := store_reg_nat s count base counter target
  have baseBound : base + 16 * count + k + 8 < 2 ^ 64 := by
    rcases baseCase with rfl | rfl <;> omega
  have ptrBound : base + 16 * count < 2 ^ 64 := by omega
  have ptrNat :
      ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7).toNat =
        base + 16 * count := by
    rw [ptr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ptrBound]
  have addrNat :
      ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7 +
        BitVec.ofNat 64 k).toNat = base + 16 * count + k := by
    rw [BitVec.toNat_add,ptrNat,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
    rw [Nat.mod_eq_of_lt (by omega : base + 16 * count + k < 2 ^ 64)]
  simp only [accessValid,rangeValid,Bool.and_eq_true,decide_eq_true_eq]
  rw [addrNat]
  constructor
  · change base + 16 * count + k + 8 ≤ 16777216
    rcases baseCase with rfl | rfl <;> omega
  · rcases baseCase with rfl | rfl <;> omega
#print axioms pair_reg_nat
#print axioms pair_frame
#print axioms store_reg_nat
#print axioms pair_access
#print axioms store_access
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePointerData67
