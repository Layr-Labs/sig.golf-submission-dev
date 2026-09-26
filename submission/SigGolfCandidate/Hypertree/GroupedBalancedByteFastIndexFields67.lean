import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndex67

/-! Memory and side-bit fields after one upper Merkle index shift. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastIndexFields67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeIndex67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem index_side (s : MachineState) :
    (indexState s).getReg .x6 = s.getMem 0x81008 &&& 1 := by
  simp [indexState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem index_low_word (s : MachineState) :
    (indexState s).getMem 0x81008 =
      (s.getMem 0x81008 >>> 1) + (s.getMem 0x81010 <<< 63) := by
  simp [indexState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem index_mid_word (s : MachineState) :
    (indexState s).getMem 0x81010 =
      (s.getMem 0x81010 >>> 1) + (s.getMem 0x81018 <<< 63) := by
  simp [indexState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem index_high_word (s : MachineState) :
    (indexState s).getMem 0x81018 = s.getMem 0x81018 >>> 1 := by
  simp [indexState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem index_side_word (s : MachineState) :
    (indexState s).getMem 0x81020 = s.getMem 0x81008 &&& 1 := by
  simp [indexState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem index_mem (s : MachineState) (a : Word)
    (h08 : a ≠ 0x81008) (h10 : a ≠ 0x81010)
    (h18 : a ≠ 0x81018) (h20 : a ≠ 0x81020) :
    (indexState s).getMem a = s.getMem a := by
  simp [indexState, execInstrBr, signExtend12,
    Expansion.mem_setMem, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  split_ifs with e1 e2 e3 e4
  · exact False.elim (h18 e1)
  · exact False.elim (h10 e2)
  · exact False.elim (h08 e3)
  · exact False.elim (h20 e4)
  · rfl

theorem index_low_frame (s : MachineState) (a : Word)
    (low : a.toNat < 0x80020) :
    (indexState s).getMem a = s.getMem a := by
  have low_ne (n : Nat) (high : 0x80020 ≤ n) (small : n < 2^64) :
      a ≠ BitVec.ofNat 64 n := by
    intro eq
    have h := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at h
    omega
  apply index_mem s a
  · exact low_ne 0x81008 (by decide) (by decide)
  · exact low_ne 0x81010 (by decide) (by decide)
  · exact low_ne 0x81018 (by decide) (by decide)
  · exact low_ne 0x81020 (by decide) (by decide)

#print axioms index_side
#print axioms index_low_word
#print axioms index_mid_word
#print axioms index_high_word
#print axioms index_side_word
#print axioms index_mem
#print axioms index_low_frame

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastIndexFields67
