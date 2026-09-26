import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntry67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInit67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def initState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x83)
  let s := execInstrBr s (.ADDI .x6 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x6 0x88)
  let s := execInstrBr s (.ADDI .x6 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SRLI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd0)
  execInstrBr s (.SD .x28 .x6 0)
theorem init_steps (s : MachineState) (pc : s.pc = 0x1dc0) :
    OrdinarySteps image s 17 (initState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x83)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0)
  let s3 := execInstrBr s2 (.LUI .x28 0x81)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 0xc0)
  let s5 := execInstrBr s4 (.SD .x28 .x6 0)
  let s6 := execInstrBr s5 (.LUI .x6 0x88)
  let s7 := execInstrBr s6 (.ADDI .x6 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x81)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0xc8)
  let s10 := execInstrBr s9 (.SD .x28 .x6 0)
  let s11 := execInstrBr s10 (.LUI .x28 0x81)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0xd0)
  let s13 := execInstrBr s12 (.LD .x6 .x28 0)
  let s14 := execInstrBr s13 (.SRLI .x6 .x6 1)
  let s15 := execInstrBr s14 (.LUI .x28 0x81)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 0xd0)
  have c0 : Keygen.instructionAt image 0x1dc0 = some (.base (.LUI .x6 0x83)) := by decide
  have c1 : Keygen.instructionAt image 0x1dc4 = some (.base (.ADDI .x6 .x6 0)) := by decide
  have c2 : Keygen.instructionAt image 0x1dc8 = some (.base (.LUI .x28 0x81)) := by decide
  have c3 : Keygen.instructionAt image 0x1dcc = some (.base (.ADDI .x28 .x28 0xc0)) := by decide
  have c4 : Keygen.instructionAt image 0x1dd0 = some (.base (.SD .x28 .x6 0)) := by decide
  have c5 : Keygen.instructionAt image 0x1dd4 = some (.base (.LUI .x6 0x88)) := by decide
  have c6 : Keygen.instructionAt image 0x1dd8 = some (.base (.ADDI .x6 .x6 0)) := by decide
  have c7 : Keygen.instructionAt image 0x1ddc = some (.base (.LUI .x28 0x81)) := by decide
  have c8 : Keygen.instructionAt image 0x1de0 = some (.base (.ADDI .x28 .x28 0xc8)) := by decide
  have c9 : Keygen.instructionAt image 0x1de4 = some (.base (.SD .x28 .x6 0)) := by decide
  have c10 : Keygen.instructionAt image 0x1de8 = some (.base (.LUI .x28 0x81)) := by decide
  have c11 : Keygen.instructionAt image 0x1dec = some (.base (.ADDI .x28 .x28 0xd0)) := by decide
  have c12 : Keygen.instructionAt image 0x1df0 = some (.base (.LD .x6 .x28 0)) := by decide
  have c13 : Keygen.instructionAt image 0x1df4 = some (.base (.SRLI .x6 .x6 1)) := by decide
  have c14 : Keygen.instructionAt image 0x1df8 = some (.base (.LUI .x28 0x81)) := by decide
  have c15 : Keygen.instructionAt image 0x1dfc = some (.base (.ADDI .x28 .x28 0xd0)) := by decide
  have c16 : Keygen.instructionAt image 0x1e00 = some (.base (.SD .x28 .x6 0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x83)) 16
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0)) 15
  · have hp : s1.pc = 0x1dc4 := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x81)) 14
  · have hp : s2.pc = 0x1dc8 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 0xc0)) 13
  · have hp : s3.pc = 0x1dcc := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SD .x28 .x6 0)) 12
  · have hp : s4.pc = 0x1dd0 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · simp [initState,s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x6 0x88)) 11
  · have hp : s5.pc = 0x1dd4 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x6 .x6 0)) 10
  · have hp : s6.pc = 0x1dd8 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x81)) 9
  · have hp : s7.pc = 0x1ddc := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0xc8)) 8
  · have hp : s8.pc = 0x1de0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.SD .x28 .x6 0)) 7
  · have hp : s9.pc = 0x1de4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [initState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s10.pc = 0x1de8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0xd0)) 5
  · have hp : s11.pc = 0x1dec := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.LD .x6 .x28 0)) 4
  · have hp : s12.pc = 0x1df0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [initState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.SRLI .x6 .x6 1)) 3
  · have hp : s13.pc = 0x1df4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s14.pc = 0x1df8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 0xd0)) 1
  · have hp : s15.pc = 0x1dfc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 (initState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s16.pc = 0x1e00 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [initState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem init_pc (s : MachineState) (pc : s.pc = 0x1dc0) : (initState s).pc = 0x1e04 := by
  simp [initState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms init_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeInit67
