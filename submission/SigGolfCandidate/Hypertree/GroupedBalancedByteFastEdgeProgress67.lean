import SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdge67

/-! State updates at the end of a Fast2Byte upper Merkle edge. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeProgress67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeUpdate67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem update_pointer (s : MachineState) :
    (updateState s).getMem 0x81048 = s.getMem 0x81048 + 16 := by
  simp [updateState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem update_edge_count (s : MachineState) :
    (updateState s).getMem 0x81000 = s.getMem 0x81000 + 1 := by
  simp [updateState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem update_level_count (s : MachineState) :
    (updateState s).getMem 0x81050 = s.getMem 0x81050 + 1 := by
  simp [updateState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem update_reg_count (s : MachineState) :
    (updateState s).getReg .x6 = s.getMem 0x81050 + 1 := by
  simp [updateState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem update_reg_limit (s : MachineState) :
    (updateState s).getReg .x7 = s.getMem 0x81060 := by
  simp [updateState, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem update_mem (s : MachineState) (a : Word)
    (hptr : a ≠ 0x81048) (hedge : a ≠ 0x81000)
    (hlevel : a ≠ 0x81050) :
    (updateState s).getMem a = s.getMem a := by
  simp [updateState, execInstrBr, signExtend12,
    Expansion.mem_setMem, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]
  split_ifs with e1 e2 e3
  · exact False.elim (hlevel e1)
  · exact False.elim (hedge e2)
  · exact False.elim (hptr e3)
  · rfl

#print axioms update_pointer
#print axioms update_edge_count
#print axioms update_level_count
#print axioms update_reg_count
#print axioms update_reg_limit
#print axioms update_mem

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeProgress67
