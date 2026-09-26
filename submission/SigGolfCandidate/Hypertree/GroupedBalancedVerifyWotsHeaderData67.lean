import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderFields67

/-! The WOTS query header and tree index after the decoder return. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open GroupedBalancedVerifyWotsHeaderBlock67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem header_word (s : MachineState) :
    (headerState s).getMem 0x90000 =
      2#64 + (s.getMem 0x81000 <<< 8) := by
  simp [headerState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem header_index_low (s : MachineState) :
    (headerState s).getMem 0x90008 = s.getMem 0x81008 := by
  simp [headerState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem header_index_mid (s : MachineState) :
    (headerState s).getMem 0x90010 = s.getMem 0x81010 := by
  simp [headerState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem header_index_high (s : MachineState) :
    (headerState s).getMem 0x90018 = s.getMem 0x81018 := by
  simp [headerState,execInstrBr,signExtend12,Expansion.mem_setMem,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms header_word
#print axioms header_index_low
#print axioms header_index_mid
#print axioms header_index_high
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderData67
