import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHeaderMid67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashReady67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def readyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x18)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x18)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0x200)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  execInstrBr s (.ADDI .x5 .x0 1)
theorem ready_steps (s : MachineState) (pc : s.pc = 0x1fa4) :
    OrdinarySteps image s 12 (readyState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x18)
  let s3 := execInstrBr s2 (.LD .x11 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x80)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x18)
  let s6 := execInstrBr s5 (.SD .x28 .x11 0)
  let s7 := execInstrBr s6 (.LUI .x10 0x80)
  let s8 := execInstrBr s7 (.ADDI .x10 .x10 0)
  let s9 := execInstrBr s8 (.ADDI .x11 .x0 0x200)
  let s10 := execInstrBr s9 (.LUI .x12 0x80)
  let s11 := execInstrBr s10 (.ADDI .x12 .x12 0x300)
  have c0 : Keygen.instructionAt image 0x1fa4 = some (.base (.LUI .x28 0x81)) := by decide
  have c1 : Keygen.instructionAt image 0x1fa8 = some (.base (.ADDI .x28 .x28 0x18)) := by decide
  have c2 : Keygen.instructionAt image 0x1fac = some (.base (.LD .x11 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1fb0 = some (.base (.LUI .x28 0x80)) := by decide
  have c4 : Keygen.instructionAt image 0x1fb4 = some (.base (.ADDI .x28 .x28 0x18)) := by decide
  have c5 : Keygen.instructionAt image 0x1fb8 = some (.base (.SD .x28 .x11 0)) := by decide
  have c6 : Keygen.instructionAt image 0x1fbc = some (.base (.LUI .x10 0x80)) := by decide
  have c7 : Keygen.instructionAt image 0x1fc0 = some (.base (.ADDI .x10 .x10 0)) := by decide
  have c8 : Keygen.instructionAt image 0x1fc4 = some (.base (.ADDI .x11 .x0 0x200)) := by decide
  have c9 : Keygen.instructionAt image 0x1fc8 = some (.base (.LUI .x12 0x80)) := by decide
  have c10 : Keygen.instructionAt image 0x1fcc = some (.base (.ADDI .x12 .x12 0x300)) := by decide
  have c11 : Keygen.instructionAt image 0x1fd0 = some (.base (.ADDI .x5 .x0 1)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 11
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x18)) 10
  · have hp : s1.pc = 0x1fa8 := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x11 .x28 0)) 9
  · have hp : s2.pc = 0x1fac := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [readyState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x80)) 8
  · have hp : s3.pc = 0x1fb0 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x18)) 7
  · have hp : s4.pc = 0x1fb4 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.SD .x28 .x11 0)) 6
  · have hp : s5.pc = 0x1fb8 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [readyState,s1,s2,s3,s4,s5,s6,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s6.pc = 0x1fbc := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s7.pc = 0x1fc0 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x0 0x200)) 3
  · have hp : s8.pc = 0x1fc4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s9.pc = 0x1fc8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s10.pc = 0x1fcc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 (readyState s) _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s11.pc = 0x1fd0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  exact OrdinarySteps.refl _
theorem ready_pc (s : MachineState) (pc : s.pc = 0x1fa4) : (readyState s).pc = 0x1fd4 := by
  simp [readyState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms ready_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashReady67
