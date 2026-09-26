import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeH4Query67
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashStorePtr67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
def storeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc8)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x300)
  let s := execInstrBr s (.LD .x10 .x28 0)
  execInstrBr s (.LD .x11 .x28 8)
theorem store_steps (s : MachineState) (pc : s.pc = 0x1fd8) :
    OrdinarySteps image s 12 (storeState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xd8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0xc8)
  let s7 := execInstrBr s6 (.LD .x10 .x28 0)
  let s8 := execInstrBr s7 (.ADD .x7 .x7 .x10)
  let s9 := execInstrBr s8 (.LUI .x28 0x80)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 0x300)
  let s11 := execInstrBr s10 (.LD .x10 .x28 0)
  have c0 : Keygen.instructionAt image 0x1fd8 = some (.base (.LUI .x28 0x81)) := by decide
  have c1 : Keygen.instructionAt image 0x1fdc = some (.base (.ADDI .x28 .x28 0xd8)) := by decide
  have c2 : Keygen.instructionAt image 0x1fe0 = some (.base (.LD .x6 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1fe4 = some (.base (.SLLI .x7 .x6 4)) := by decide
  have c4 : Keygen.instructionAt image 0x1fe8 = some (.base (.LUI .x28 0x81)) := by decide
  have c5 : Keygen.instructionAt image 0x1fec = some (.base (.ADDI .x28 .x28 0xc8)) := by decide
  have c6 : Keygen.instructionAt image 0x1ff0 = some (.base (.LD .x10 .x28 0)) := by decide
  have c7 : Keygen.instructionAt image 0x1ff4 = some (.base (.ADD .x7 .x7 .x10)) := by decide
  have c8 : Keygen.instructionAt image 0x1ff8 = some (.base (.LUI .x28 0x80)) := by decide
  have c9 : Keygen.instructionAt image 0x1ffc = some (.base (.ADDI .x28 .x28 0x300)) := by decide
  have c10 : Keygen.instructionAt image 0x2000 = some (.base (.LD .x10 .x28 0)) := by decide
  have c11 : Keygen.instructionAt image 0x2004 = some (.base (.LD .x11 .x28 8)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 11
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xd8)) 10
  · have hp : s1.pc = 0x1fdc := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 9
  · have hp : s2.pc = 0x1fe0 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [storeState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x7 .x6 4)) 8
  · have hp : s3.pc = 0x1fe4 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 7
  · have hp : s4.pc = 0x1fe8 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0xc8)) 6
  · have hp : s5.pc = 0x1fec := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LD .x10 .x28 0)) 5
  · have hp : s6.pc = 0x1ff0 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [storeState,s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.ADD .x7 .x7 .x10)) 4
  · have hp : s7.pc = 0x1ff4 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x80)) 3
  · have hp : s8.pc = 0x1ff8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 0x300)) 2
  · have hp : s9.pc = 0x1ffc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x10 .x28 0)) 1
  · have hp : s10.pc = 0x2000 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [storeState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s11 (storeState s) _ (.base (.LD .x11 .x28 8)) 0
  · have hp : s11.pc = 0x2004 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [storeState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem store_pc (s : MachineState) (pc : s.pc = 0x1fd8) : (storeState s).pc = 0x2008 := by
  simp [storeState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms store_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashStorePtr67
