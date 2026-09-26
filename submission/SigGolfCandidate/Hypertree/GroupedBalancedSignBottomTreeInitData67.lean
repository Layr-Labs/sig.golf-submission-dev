import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntryData67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInit67

/-! Source and target buffers prepared for the first Merkle parent level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInitData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev init := GroupedBalancedSignBottomTreeInit67.initState

theorem init_source (s : MachineState) :
    (init s).getMem 0x810c0 = 0x83000 := by
  simp [init, GroupedBalancedSignBottomTreeInit67.initState,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem init_target (s : MachineState) :
    (init s).getMem 0x810c8 = 0x88000 := by
  simp [init, GroupedBalancedSignBottomTreeInit67.initState,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem init_count (s : MachineState) :
    (init s).getMem 0x810d0 = s.getMem 0x810d0 >>> 1 := by
  simp [init, GroupedBalancedSignBottomTreeInit67.initState,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem init_frame (s : MachineState) (a : Word)
    (hsource : a ≠ 0x810c0) (htarget : a ≠ 0x810c8)
    (hcount : a ≠ 0x810d0) :
    (init s).getMem a = s.getMem a := by
  change a ≠ (528576#64) at hsource
  change a ≠ (528584#64) at htarget
  change a ≠ (528592#64) at hcount
  simp [init, GroupedBalancedSignBottomTreeInit67.initState,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, hsource, htarget, hcount]

theorem init_stack (s : MachineState) :
    (init s).getReg .x2 = s.getReg .x2 := by
  simp [init, GroupedBalancedSignBottomTreeInit67.initState,
    execInstrBr, MachineState.getReg_setReg_ne]

#print axioms init_source
#print axioms init_target
#print axioms init_count
#print axioms init_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInitData67
