import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderCopy67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeNodeInput67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def inputState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x20)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.SD .x28 .x12 8)
  let s := execInstrBr s (.SD .x28 .x13 16)
  execInstrBr s (.SD .x28 .x14 24)
theorem input_steps (s : MachineState) (pc : s.pc = 0x1f38) :
    OrdinarySteps image s 6 (inputState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x80)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x20)
  let s3 := execInstrBr s2 (.SD .x28 .x11 0)
  let s4 := execInstrBr s3 (.SD .x28 .x12 8)
  let s5 := execInstrBr s4 (.SD .x28 .x13 16)
  have c0 : Keygen.instructionAt image 0x1f38 = some (.base (.LUI .x28 0x80)) := by decide
  have c1 : Keygen.instructionAt image 0x1f3c = some (.base (.ADDI .x28 .x28 0x20)) := by decide
  have c2 : Keygen.instructionAt image 0x1f40 = some (.base (.SD .x28 .x11 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1f44 = some (.base (.SD .x28 .x12 8)) := by decide
  have c4 : Keygen.instructionAt image 0x1f48 = some (.base (.SD .x28 .x13 16)) := by decide
  have c5 : Keygen.instructionAt image 0x1f4c = some (.base (.SD .x28 .x14 24)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x80)) 5
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x20)) 4
  · have hp : s1.pc = 0x1f3c := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x11 0)) 3
  · have hp : s2.pc = 0x1f40 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [inputState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x12 8)) 2
  · have hp : s3.pc = 0x1f44 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [inputState,s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SD .x28 .x13 16)) 1
  · have hp : s4.pc = 0x1f48 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · simp [inputState,s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 (inputState s) _ (.base (.SD .x28 .x14 24)) 0
  · have hp : s5.pc = 0x1f4c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [inputState,s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem input_pc (s : MachineState) (pc : s.pc = 0x1f38) : (inputState s).pc = 0x1f50 := by
  simp [inputState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms input_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeNodeInput67
