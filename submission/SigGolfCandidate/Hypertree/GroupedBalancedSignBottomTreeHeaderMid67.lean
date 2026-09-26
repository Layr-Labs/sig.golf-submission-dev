import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeNodeInput67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTag67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderMid67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTag67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def tagState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 4)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  execInstrBr s (.SD .x28 .x10 0)
theorem tag_steps (s : MachineState) (pc : s.pc = 0x1f50) :
    OrdinarySteps image s 9 (tagState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 4)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 0x80)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0)
  have c0 : Keygen.instructionAt image 0x1f50 = some (.base (.ADDI .x10 .x0 4)) := by decide
  have c1 : Keygen.instructionAt image 0x1f54 = some (.base (.LUI .x28 0x81)) := by decide
  have c2 : Keygen.instructionAt image 0x1f58 = some (.base (.ADDI .x28 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1f5c = some (.base (.LD .x11 .x28 0)) := by decide
  have c4 : Keygen.instructionAt image 0x1f60 = some (.base (.SLLI .x11 .x11 8)) := by decide
  have c5 : Keygen.instructionAt image 0x1f64 = some (.base (.ADD .x10 .x10 .x11)) := by decide
  have c6 : Keygen.instructionAt image 0x1f68 = some (.base (.LUI .x28 0x80)) := by decide
  have c7 : Keygen.instructionAt image 0x1f6c = some (.base (.ADDI .x28 .x28 0)) := by decide
  have c8 : Keygen.instructionAt image 0x1f70 = some (.base (.SD .x28 .x10 0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 4)) 8
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 7
  · have hp : s1.pc = 0x1f54 := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 6
  · have hp : s2.pc = 0x1f58 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 5
  · have hp : s3.pc = 0x1f5c := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [tagState,s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 4
  · have hp : s4.pc = 0x1f60 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 3
  · have hp : s5.pc = 0x1f64 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s6.pc = 0x1f68 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0)) 1
  · have hp : s7.pc = 0x1f6c := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 (tagState s) _ (.base (.SD .x28 .x10 0)) 0
  · have hp : s8.pc = 0x1f70 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [tagState,s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem tag_pc (s : MachineState) (pc : s.pc = 0x1f50) : (tagState s).pc = 0x1f74 := by
  simp [tagState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms tag_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTag67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderMid67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def middleState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x10)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x10)
  execInstrBr s (.SD .x28 .x11 0)
theorem middle_steps (s : MachineState) (pc : s.pc = 0x1f74) :
    OrdinarySteps image s 12 (middleState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x11 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 8)
  let s6 := execInstrBr s5 (.SD .x28 .x11 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0x10)
  let s9 := execInstrBr s8 (.LD .x11 .x28 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x80)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 0x10)
  have c0 : Keygen.instructionAt image 0x1f74 = some (.base (.LUI .x28 0x81)) := by decide
  have c1 : Keygen.instructionAt image 0x1f78 = some (.base (.ADDI .x28 .x28 8)) := by decide
  have c2 : Keygen.instructionAt image 0x1f7c = some (.base (.LD .x11 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1f80 = some (.base (.LUI .x28 0x80)) := by decide
  have c4 : Keygen.instructionAt image 0x1f84 = some (.base (.ADDI .x28 .x28 8)) := by decide
  have c5 : Keygen.instructionAt image 0x1f88 = some (.base (.SD .x28 .x11 0)) := by decide
  have c6 : Keygen.instructionAt image 0x1f8c = some (.base (.LUI .x28 0x81)) := by decide
  have c7 : Keygen.instructionAt image 0x1f90 = some (.base (.ADDI .x28 .x28 0x10)) := by decide
  have c8 : Keygen.instructionAt image 0x1f94 = some (.base (.LD .x11 .x28 0)) := by decide
  have c9 : Keygen.instructionAt image 0x1f98 = some (.base (.LUI .x28 0x80)) := by decide
  have c10 : Keygen.instructionAt image 0x1f9c = some (.base (.ADDI .x28 .x28 0x10)) := by decide
  have c11 : Keygen.instructionAt image 0x1fa0 = some (.base (.SD .x28 .x11 0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 11
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 10
  · have hp : s1.pc = 0x1f78 := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 0)) 9
  · have hp : s2.pc = 0x1f7c := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [middleState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 8
  · have hp : s3.pc = 0x1f80 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 8)) 7
  · have hp : s4.pc = 0x1f84 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x11 0)) 6
  · have hp : s5.pc = 0x1f88 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [middleState,s1,s2,s3,s4,s5,s6,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 5
  · have hp : s6.pc = 0x1f8c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0x10)) 4
  · have hp : s7.pc = 0x1f90 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x11 .x28 0)) 3
  · have hp : s8.pc = 0x1f94 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [middleState,s1,s2,s3,s4,s5,s6,s7,s8,s9,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 2
  · have hp : s9.pc = 0x1f98 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 0x10)) 1
  · have hp : s10.pc = 0x1f9c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 (middleState s) _ (.base (.SD .x28 .x11 0)) 0
  · have hp : s11.pc = 0x1fa0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [middleState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem middle_pc (s : MachineState) (pc : s.pc = 0x1f74) : (middleState s).pc = 0x1fa4 := by
  simp [middleState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms middle_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderMid67
