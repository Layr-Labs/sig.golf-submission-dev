import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInit67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexLoad67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexShift67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexLoad67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def loadState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xa8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xb0)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xb8)
  execInstrBr s (.LD .x10 .x28 0)
theorem load_steps (s : MachineState) (pc : s.pc = 0x1e04) :
    OrdinarySteps image s 9 (loadState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xa8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0xb0)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0xb8)
  have c0 : Keygen.instructionAt image 0x1e04 = some (.base (.LUI .x28 0x81)) := by decide
  have c1 : Keygen.instructionAt image 0x1e08 = some (.base (.ADDI .x28 .x28 0xa8)) := by decide
  have c2 : Keygen.instructionAt image 0x1e0c = some (.base (.LD .x6 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1e10 = some (.base (.LUI .x28 0x81)) := by decide
  have c4 : Keygen.instructionAt image 0x1e14 = some (.base (.ADDI .x28 .x28 0xb0)) := by decide
  have c5 : Keygen.instructionAt image 0x1e18 = some (.base (.LD .x7 .x28 0)) := by decide
  have c6 : Keygen.instructionAt image 0x1e1c = some (.base (.LUI .x28 0x81)) := by decide
  have c7 : Keygen.instructionAt image 0x1e20 = some (.base (.ADDI .x28 .x28 0xb8)) := by decide
  have c8 : Keygen.instructionAt image 0x1e24 = some (.base (.LD .x10 .x28 0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 8
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xa8)) 7
  · have hp : s1.pc = 0x1e08 := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 6
  · have hp : s2.pc = 0x1e0c := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [loadState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 5
  · have hp : s3.pc = 0x1e10 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0xb0)) 4
  · have hp : s4.pc = 0x1e14 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 3
  · have hp : s5.pc = 0x1e18 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [loadState,s1,s2,s3,s4,s5,s6,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s6.pc = 0x1e1c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0xb8)) 1
  · have hp : s7.pc = 0x1e20 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 (loadState s) _ (.base (.LD .x10 .x28 0)) 0
  · have hp : s8.pc = 0x1e24 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [loadState,s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem load_pc (s : MachineState) (pc : s.pc = 0x1e04) : (loadState s).pc = 0x1e28 := by
  simp [loadState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms load_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexLoad67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexShift67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def shiftState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SLLI .x11 .x7 63)
  let s := execInstrBr s (.SRLI .x6 .x6 1)
  let s := execInstrBr s (.ADD .x6 .x6 .x11)
  let s := execInstrBr s (.SLLI .x11 .x10 63)
  let s := execInstrBr s (.SRLI .x7 .x7 1)
  let s := execInstrBr s (.ADD .x7 .x7 .x11)
  let s := execInstrBr s (.SRLI .x10 .x10 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xa8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xb0)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xb8)
  execInstrBr s (.SD .x28 .x10 0)
theorem shift_steps (s : MachineState) (pc : s.pc = 0x1e28) :
    OrdinarySteps image s 16 (shiftState s) := by
  let s1 := execInstrBr s (.SLLI .x11 .x7 63)
  let s2 := execInstrBr s1 (.SRLI .x6 .x6 1)
  let s3 := execInstrBr s2 (.ADD .x6 .x6 .x11)
  let s4 := execInstrBr s3 (.SLLI .x11 .x10 63)
  let s5 := execInstrBr s4 (.SRLI .x7 .x7 1)
  let s6 := execInstrBr s5 (.ADD .x7 .x7 .x11)
  let s7 := execInstrBr s6 (.SRLI .x10 .x10 1)
  let s8 := execInstrBr s7 (.LUI .x28 0x81)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0xa8)
  let s10 := execInstrBr s9 (.SD .x28 .x6 0)
  let s11 := execInstrBr s10 (.LUI .x28 0x81)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0xb0)
  let s13 := execInstrBr s12 (.SD .x28 .x7 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x81)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 0xb8)
  have c0 : Keygen.instructionAt image 0x1e28 = some (.base (.SLLI .x11 .x7 63)) := by decide
  have c1 : Keygen.instructionAt image 0x1e2c = some (.base (.SRLI .x6 .x6 1)) := by decide
  have c2 : Keygen.instructionAt image 0x1e30 = some (.base (.ADD .x6 .x6 .x11)) := by decide
  have c3 : Keygen.instructionAt image 0x1e34 = some (.base (.SLLI .x11 .x10 63)) := by decide
  have c4 : Keygen.instructionAt image 0x1e38 = some (.base (.SRLI .x7 .x7 1)) := by decide
  have c5 : Keygen.instructionAt image 0x1e3c = some (.base (.ADD .x7 .x7 .x11)) := by decide
  have c6 : Keygen.instructionAt image 0x1e40 = some (.base (.SRLI .x10 .x10 1)) := by decide
  have c7 : Keygen.instructionAt image 0x1e44 = some (.base (.LUI .x28 0x81)) := by decide
  have c8 : Keygen.instructionAt image 0x1e48 = some (.base (.ADDI .x28 .x28 0xa8)) := by decide
  have c9 : Keygen.instructionAt image 0x1e4c = some (.base (.SD .x28 .x6 0)) := by decide
  have c10 : Keygen.instructionAt image 0x1e50 = some (.base (.LUI .x28 0x81)) := by decide
  have c11 : Keygen.instructionAt image 0x1e54 = some (.base (.ADDI .x28 .x28 0xb0)) := by decide
  have c12 : Keygen.instructionAt image 0x1e58 = some (.base (.SD .x28 .x7 0)) := by decide
  have c13 : Keygen.instructionAt image 0x1e5c = some (.base (.LUI .x28 0x81)) := by decide
  have c14 : Keygen.instructionAt image 0x1e60 = some (.base (.ADDI .x28 .x28 0xb8)) := by decide
  have c15 : Keygen.instructionAt image 0x1e64 = some (.base (.SD .x28 .x10 0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.SLLI .x11 .x7 63)) 15
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SRLI .x6 .x6 1)) 14
  · have hp : s1.pc = 0x1e2c := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADD .x6 .x6 .x11)) 13
  · have hp : s2.pc = 0x1e30 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x11 .x10 63)) 12
  · have hp : s3.pc = 0x1e34 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SRLI .x7 .x7 1)) 11
  · have hp : s4.pc = 0x1e38 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x7 .x7 .x11)) 10
  · have hp : s5.pc = 0x1e3c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SRLI .x10 .x10 1)) 9
  · have hp : s6.pc = 0x1e40 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x81)) 8
  · have hp : s7.pc = 0x1e44 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0xa8)) 7
  · have hp : s8.pc = 0x1e48 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SD .x28 .x6 0)) 6
  · have hp : s9.pc = 0x1e4c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [shiftState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x81)) 5
  · have hp : s10.pc = 0x1e50 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0xb0)) 4
  · have hp : s11.pc = 0x1e54 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x7 0)) 3
  · have hp : s12.pc = 0x1e58 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [shiftState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s13.pc = 0x1e5c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 0xb8)) 1
  · have hp : s14.pc = 0x1e60 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 (shiftState s) _ (.base (.SD .x28 .x10 0)) 0
  · have hp : s15.pc = 0x1e64 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [shiftState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem shift_pc (s : MachineState) (pc : s.pc = 0x1e28) : (shiftState s).pc = 0x1e68 := by
  simp [shiftState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms shift_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeIndexShift67
