import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntry67

/-! The signer calls its bottom-tree parent builder after the 1,024th leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeCall67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def callState (s : MachineState) : MachineState :=
  execInstrBr s (.JAL .x1 0x8bc)

theorem call_code :
    Keygen.instructionAt image 0x14ec =
      some (.base (.JAL .x1 0x8bc)) := by
  decide

theorem call_step (s : MachineState) (pc : s.pc = 0x14ec) :
    OrdinarySteps image s 1 (callState s) := by
  apply OrdinarySteps.step s (callState s) _
      (.base (.JAL .x1 0x8bc)) 0
  · simpa only [Keygen.fetch_at, pc] using call_code
  · rfl
  exact OrdinarySteps.refl _

theorem call_pc (s : MachineState) (pc : s.pc = 0x14ec) :
    (callState s).pc = 0x1da8 := by
  simp [callState, execInstrBr, pc, signExtend21]

theorem call_link (s : MachineState) (pc : s.pc = 0x14ec) :
    (callState s).getReg .x1 = 0x14f0 := by
  simp [callState, execInstrBr, pc, MachineState.getReg_setReg_eq]

theorem call_stack (s : MachineState) :
    (callState s).getReg .x2 = s.getReg .x2 := by
  simp [callState, execInstrBr, MachineState.getReg_setReg_ne]

theorem call_mem (s : MachineState) (a : Word) :
    (callState s).getMem a = s.getMem a := by
  simp [callState, execInstrBr,
    MachineState.getMem_setReg, MachineState.getMem_setPC]

#print axioms call_step
#print axioms call_pc
#print axioms call_mem
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeCall67
