import SigGolfCandidate.Hypertree.GroupedBalancedVerifyEntry67

/-! Verifier setup from the initial control writes to the first copy loop. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifySetup67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x6 0x2c)
  let s := execInstrBr s (.ADDI .x6 .x6 0x720)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x20)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x28)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x30)
  execInstrBr s (.ADDI .x10 .x0 4)

private theorem setup_code :
    Keygen.instructionAt image 0x1030 = some (.base (.LUI .x6 0x2c)) ∧
    Keygen.instructionAt image 0x1034 = some (.base (.ADDI .x6 .x6 0x720)) ∧
    Keygen.instructionAt image 0x1038 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x103c = some (.base (.ADDI .x28 .x28 0x48)) ∧
    Keygen.instructionAt image 0x1040 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1044 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1048 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x104c = some (.base (.ADDI .x28 .x28 0x20)) ∧
    Keygen.instructionAt image 0x1050 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1054 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1058 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x105c = some (.base (.ADDI .x28 .x28 0x28)) ∧
    Keygen.instructionAt image 0x1060 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1064 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1068 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x106c = some (.base (.ADDI .x7 .x7 0x30)) ∧
    Keygen.instructionAt image 0x1070 = some (.base (.ADDI .x10 .x0 4))
    := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x1030) :
    OrdinarySteps image s 17 (setupState s) := by
  let s1 := execInstrBr s (.LUI .x6 0x2c)
  let s2 := execInstrBr s1 (.ADDI .x6 .x6 0x720)
  let s3 := execInstrBr s2 (.LUI .x28 0x81)
  let s4 := execInstrBr s3 (.ADDI .x28 .x28 0x48)
  let s5 := execInstrBr s4 (.SD .x28 .x6 0)
  let s6 := execInstrBr s5 (.ADDI .x6 .x0 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x80)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0x20)
  let s9 := execInstrBr s8 (.SD .x28 .x6 0)
  let s10 := execInstrBr s9 (.ADDI .x6 .x0 0)
  let s11 := execInstrBr s10 (.LUI .x28 0x80)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0x28)
  let s13 := execInstrBr s12 (.SD .x28 .x6 0)
  let s14 := execInstrBr s13 (.ADDI .x6 .x0 0)
  let s15 := execInstrBr s14 (.LUI .x7 0x80)
  let s16 := execInstrBr s15 (.ADDI .x7 .x7 0x30)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x6 0x2c)) 16
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x6 .x6 0x720)) 15
  · have hp : s1.pc = 0x1034 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LUI .x28 0x81)) 14
  · have hp : s2.pc = 0x1038 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x28 .x28 0x48)) 13
  · have hp : s3.pc = 0x103c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.SD .x28 .x6 0)) 12
  · have hp : s4.pc = 0x1040 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · simp [s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x6 .x0 0)) 11
  · have hp : s5.pc = 0x1044 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 10
  · have hp : s6.pc = 0x1048 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0x20)) 9
  · have hp : s7.pc = 0x104c := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x6 0)) 8
  · have hp : s8.pc = 0x1050 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x6 .x0 0)) 7
  · have hp : s9.pc = 0x1054 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x80)) 6
  · have hp : s10.pc = 0x1058 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0x28)) 5
  · have hp : s11.pc = 0x105c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s12.pc = 0x1060 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s13.pc = 0x1064 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x7 0x80)) 2
  · have hp : s14.pc = 0x1068 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x7 .x7 0x30)) 1
  · have hp : s15.pc = 0x106c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 (setupState s) _ (.base (.ADDI .x10 .x0 4)) 0
  · have hp : s16.pc = 0x1070 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) (pc : s.pc = 0x1030) :
    (setupState s).pc = 0x1074 := by
  simp [setupState,execInstrBr,pc]

theorem setup_regs (s : MachineState) :
    (setupState s).getReg .x6 = 0 ∧
    (setupState s).getReg .x7 = 0x80030 ∧
    (setupState s).getReg .x10 = 4 := by
  simp [setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_pointer (s : MachineState) :
    (setupState s).getMem 0x81048 = 0x2c720 := by
  simp [setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

#print axioms setup_steps
end SigGolfCandidate.Hypertree.GroupedBalancedVerifySetup67
