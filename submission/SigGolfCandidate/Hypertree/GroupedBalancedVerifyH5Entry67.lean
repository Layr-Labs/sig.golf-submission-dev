import SigGolfCandidate.Hypertree.GroupedBalancedVerifySecondCopy67

/-! The first verifier H5 query is reached by exact bytecode execution. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Entry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def setupState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 5)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.ADDI .x11 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 896)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  execInstrBr s (.ADDI .x5 .x0 1)

private theorem setup_code :
    Keygen.instructionAt image 0x10b8 = some (.base (.ADDI .x10 .x0 5)) ∧
    Keygen.instructionAt image 0x10bc = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x10c0 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x10c4 = some (.base (.SD .x28 .x10 0)) ∧
    Keygen.instructionAt image 0x10c8 = some (.base (.ADDI .x11 .x0 0)) ∧
    Keygen.instructionAt image 0x10cc = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x10d0 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x10d4 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x10d8 = some (.base (.ADDI .x11 .x0 0)) ∧
    Keygen.instructionAt image 0x10dc = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x10e0 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x10e4 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x10e8 = some (.base (.ADDI .x11 .x0 0)) ∧
    Keygen.instructionAt image 0x10ec = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x10f0 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x10f4 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x10f8 = some (.base (.LUI .x10 0x80)) ∧
    Keygen.instructionAt image 0x10fc = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x1100 = some (.base (.ADDI .x11 .x0 896)) ∧
    Keygen.instructionAt image 0x1104 = some (.base (.LUI .x12 0x80)) ∧
    Keygen.instructionAt image 0x1108 = some (.base (.ADDI .x12 .x12 0x300)) ∧
    Keygen.instructionAt image 0x110c = some (.base (.ADDI .x5 .x0 1))
    := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem setup_steps (s : MachineState) (pc : s.pc = 0x10b8) :
    OrdinarySteps image s 22 (setupState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 5)
  let s2 := execInstrBr s1 (.LUI .x28 0x80)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.SD .x28 .x10 0)
  let s5 := execInstrBr s4 (.ADDI .x11 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x80)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 8)
  let s8 := execInstrBr s7 (.SD .x28 .x11 0)
  let s9 := execInstrBr s8 (.ADDI .x11 .x0 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x80)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 16)
  let s12 := execInstrBr s11 (.SD .x28 .x11 0)
  let s13 := execInstrBr s12 (.ADDI .x11 .x0 0)
  let s14 := execInstrBr s13 (.LUI .x28 0x80)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 24)
  let s16 := execInstrBr s15 (.SD .x28 .x11 0)
  let s17 := execInstrBr s16 (.LUI .x10 0x80)
  let s18 := execInstrBr s17 (.ADDI .x10 .x10 0)
  let s19 := execInstrBr s18 (.ADDI .x11 .x0 896)
  let s20 := execInstrBr s19 (.LUI .x12 0x80)
  let s21 := execInstrBr s20 (.ADDI .x12 .x12 0x300)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21⟩ := setup_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 5)) 21
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x80)) 20
  · have hp : s1.pc = 0x10bc := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 19
  · have hp : s2.pc = 0x10c0 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x10 0)) 18
  · have hp : s3.pc = 0x10c4 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x11 .x0 0)) 17
  · have hp : s4.pc = 0x10c8 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x80)) 16
  · have hp : s5.pc = 0x10cc := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 8)) 15
  · have hp : s6.pc = 0x10d0 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x11 0)) 14
  · have hp : s7.pc = 0x10d4 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x11 .x0 0)) 13
  · have hp : s8.pc = 0x10d8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 12
  · have hp : s9.pc = 0x10dc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 16)) 11
  · have hp : s10.pc = 0x10e0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x11 0)) 10
  · have hp : s11.pc = 0x10e4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x11 .x0 0)) 9
  · have hp : s12.pc = 0x10e8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x80)) 8
  · have hp : s13.pc = 0x10ec := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 24)) 7
  · have hp : s14.pc = 0x10f0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.SD .x28 .x11 0)) 6
  · have hp : s15.pc = 0x10f4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s16.pc = 0x10f8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s17.pc = 0x10fc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x11 .x0 896)) 3
  · have hp : s18.pc = 0x1100 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s19.pc = 0x1104 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s20.pc = 0x1108 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 (setupState s) _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s21.pc = 0x110c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  exact OrdinarySteps.refl _

theorem setup_pc (s : MachineState) (pc : s.pc = 0x10b8) :
    (setupState s).pc = 0x1110 := by
  simp [setupState,execInstrBr,pc]

theorem setup_regs (s : MachineState) :
    (setupState s).getReg .x5 = 1 ∧
    (setupState s).getReg .x10 = 0x80000 ∧
    (setupState s).getReg .x11 = 896 ∧
    (setupState s).getReg .x12 = 0x80300 := by
  simp [setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem setup_pointer (s : MachineState) :
    (setupState s).getMem 0x81048 = s.getMem 0x81048 := by
  simp [setupState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

#print axioms setup_steps
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyH5Entry67
