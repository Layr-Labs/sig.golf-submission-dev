import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairPtr67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairLoad67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def loadState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x7 0)
  let s := execInstrBr s (.LD .x12 .x7 8)
  let s := execInstrBr s (.LD .x13 .x7 16)
  execInstrBr s (.LD .x14 .x7 24)
theorem load_steps (s : MachineState) (pc : s.pc = 0x1f28)
    (valid0 : accessValid (s.getReg .x7 + 0) 8 = true)
    (valid1 : accessValid (s.getReg .x7 + 8) 8 = true)
    (valid2 : accessValid (s.getReg .x7 + 16) 8 = true)
    (valid3 : accessValid (s.getReg .x7 + 24) 8 = true)
    : OrdinarySteps image s 4 (loadState s) := by
  let s1 := execInstrBr s (.LD .x11 .x7 0)
  let s2 := execInstrBr s1 (.LD .x12 .x7 8)
  let s3 := execInstrBr s2 (.LD .x13 .x7 16)
  have c0 : Keygen.instructionAt image 0x1f28 = some (.base (.LD .x11 .x7 0)) := by decide
  have c1 : Keygen.instructionAt image 0x1f2c = some (.base (.LD .x12 .x7 8)) := by decide
  have c2 : Keygen.instructionAt image 0x1f30 = some (.base (.LD .x13 .x7 16)) := by decide
  have c3 : Keygen.instructionAt image 0x1f34 = some (.base (.LD .x14 .x7 24)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x7 0)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · simpa [loadState,s1,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using valid0
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x12 .x7 8)) 2
  · have hp : s1.pc = 0x1f2c := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · simpa [loadState,s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using valid1
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x13 .x7 16)) 1
  · have hp : s2.pc = 0x1f30 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simpa [loadState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using valid2
  apply OrdinarySteps.step s3 (loadState s) _ (.base (.LD .x14 .x7 24)) 0
  · have hp : s3.pc = 0x1f34 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · simpa [loadState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using valid3
  exact OrdinarySteps.refl _
theorem load_pc (s : MachineState) (pc : s.pc = 0x1f28) : (loadState s).pc = 0x1f38 := by
  simp [loadState,execInstrBr,pc,signExtend12]
#print axioms load_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreePairLoad67
