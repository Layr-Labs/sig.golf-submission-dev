import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashStorePtr67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashStoreCopy67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
def storedState (s : MachineState) : MachineState :=
  GroupedBalancedSignBottomTreeHashStoreCopy67.copyState
    (GroupedBalancedSignBottomTreeHashStorePtr67.storeState s)
theorem stored_low (s : MachineState) :
    (storedState s).getMem
      ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7) =
      s.getMem 0x80300 := by
  simp [storedState,GroupedBalancedSignBottomTreeHashStorePtr67.storeState,
    GroupedBalancedSignBottomTreeHashStoreCopy67.copyState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem stored_high (s : MachineState) :
    (storedState s).getMem
      ((GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7 + 8) =
      s.getMem 0x80308 := by
  simp [storedState,GroupedBalancedSignBottomTreeHashStorePtr67.storeState,
    GroupedBalancedSignBottomTreeHashStoreCopy67.copyState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem stored_frame (s : MachineState) (a : Word)
    (h0 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7)
    (h1 : a ≠ (GroupedBalancedSignBottomTreeHashStorePtr67.storeState s).getReg .x7 + 8) :
    (storedState s).getMem a = s.getMem a := by
  simp [GroupedBalancedSignBottomTreeHashStorePtr67.storeState,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne] at h0 h1
  simp [storedState,GroupedBalancedSignBottomTreeHashStorePtr67.storeState,
    GroupedBalancedSignBottomTreeHashStoreCopy67.copyState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1]
#print axioms stored_low
#print axioms stored_high
#print axioms stored_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeStoreData67
