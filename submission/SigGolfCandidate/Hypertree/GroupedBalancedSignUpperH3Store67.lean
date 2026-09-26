import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Hash67

/-! Store one upper WOTS leaf value and advance the leaf/address counters. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Store67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67Byte.image

def advanceState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x6 4)
  let s := execInstrBr s (.LUI .x10 0x83)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADD .x7 .x7 .x10)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0x300)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 8)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd0)
  let s := execInstrBr s (.LD .x7 .x28 0)
  execInstrBr s (.BNE .x6 .x7 (-1244))

private theorem advance_code :
    Keygen.instructionAt image 0x1bb4 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1bb8 = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x1bbc = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1bc0 = some (.base (.SLLI .x7 .x6 4)) ∧
    Keygen.instructionAt image 0x1bc4 = some (.base (.LUI .x10 0x83)) ∧
    Keygen.instructionAt image 0x1bc8 = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x1bcc = some (.base (.ADD .x7 .x7 .x10)) ∧
    Keygen.instructionAt image 0x1bd0 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1bd4 = some (.base (.ADDI .x28 .x28 0x300)) ∧
    Keygen.instructionAt image 0x1bd8 = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x1bdc = some (.base (.LD .x11 .x28 8)) ∧
    Keygen.instructionAt image 0x1be0 = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1be4 = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x1be8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1bec = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1bf0 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1bf4 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1bf8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1bfc = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1c00 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1c04 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1c08 = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x1c0c = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1c10 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1c14 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1c18 = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x1c1c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1c20 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1c24 = some (.base (.ADDI .x28 .x28 0xd0)) ∧
    Keygen.instructionAt image 0x1c28 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x1c2c = some (.base (.BNE .x6 .x7 (-1244))) := by
  decide

theorem advance_steps (s : MachineState) (pc : s.pc = 0x1bb4)
    (valid : accessValid ((s.getMem 0x810e0 <<< 4) + 0x83000) 8 = true)
    (valid8 : accessValid ((s.getMem 0x810e0 <<< 4) + 0x83000 + 8) 8 = true) :
    OrdinarySteps image s 31 (advanceState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xe0)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.SLLI .x7 .x6 4)
  let s5 := execInstrBr s4 (.LUI .x10 0x83)
  let s6 := execInstrBr s5 (.ADDI .x10 .x10 0)
  let s7 := execInstrBr s6 (.ADD .x7 .x7 .x10)
  let s8 := execInstrBr s7 (.LUI .x28 0x80)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0x300)
  let s10 := execInstrBr s9 (.LD .x10 .x28 0)
  let s11 := execInstrBr s10 (.LD .x11 .x28 8)
  let s12 := execInstrBr s11 (.SD .x7 .x10 0)
  let s13 := execInstrBr s12 (.SD .x7 .x11 8)
  let s14 := execInstrBr s13 (.LUI .x28 0x81)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 8)
  let s16 := execInstrBr s15 (.LD .x6 .x28 0)
  let s17 := execInstrBr s16 (.ADDI .x6 .x6 1)
  let s18 := execInstrBr s17 (.LUI .x28 0x81)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 8)
  let s20 := execInstrBr s19 (.SD .x28 .x6 0)
  let s21 := execInstrBr s20 (.LUI .x28 0x81)
  let s22 := execInstrBr s21 (.ADDI .x28 .x28 0xe0)
  let s23 := execInstrBr s22 (.LD .x6 .x28 0)
  let s24 := execInstrBr s23 (.ADDI .x6 .x6 1)
  let s25 := execInstrBr s24 (.LUI .x28 0x81)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 0xe0)
  let s27 := execInstrBr s26 (.SD .x28 .x6 0)
  let s28 := execInstrBr s27 (.LUI .x28 0x81)
  let s29 := execInstrBr s28 (.ADDI .x28 .x28 0xd0)
  let s30 := execInstrBr s29 (.LD .x7 .x28 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30⟩ := advance_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 30
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xe0)) 29
  · have hp : s1.pc = 0x1bb8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 28
  · have hp : s2.pc = 0x1bbc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s3 s4 _ (.base (.SLLI .x7 .x6 4)) 27
  · have hp : s3.pc = 0x1bc0 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x10 0x83)) 26
  · have hp : s4.pc = 0x1bc4 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x10 .x10 0)) 25
  · have hp : s5.pc = 0x1bc8 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADD .x7 .x7 .x10)) 24
  · have hp : s6.pc = 0x1bcc := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x80)) 23
  · have hp : s7.pc = 0x1bd0 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0x300)) 22
  · have hp : s8.pc = 0x1bd4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x10 .x28 0)) 21
  · have hp : s9.pc = 0x1bd8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x11 .x28 8)) 20
  · have hp : s10.pc = 0x1bdc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  have stackReg : s11.getReg .x7 =
      (s.getMem 0x810e0 <<< 4) + 0x83000 := by
    simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,
      signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,BitVec.add_comm]
  have validS11 : accessValid (s11.getReg .x7) 8 = true := by
    rw [stackReg]
    exact valid
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x7 .x10 0)) 19
  · have hp : s11.pc = 0x1be0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s12,ordinaryStep,memoryArgumentsValid,signExtend12,validS11]
  have validS12 : accessValid (s12.getReg .x7 + 8) 8 = true := by
    simpa [s12,execInstrBr,stackReg] using valid8
  have validS12' : accessValid (s12.getReg .x7 + signExtend12 (8 : BitVec 12)) 8 = true := by
    simpa [signExtend12] using validS12
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x7 .x11 8)) 18
  · have hp : s12.pc = 0x1be4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp only [ordinaryStep,memoryArgumentsValid]
    exact if_pos validS12'
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x81)) 17
  · have hp : s13.pc = 0x1be8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 8)) 16
  · have hp : s14.pc = 0x1bec := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.LD .x6 .x28 0)) 15
  · have hp : s15.pc = 0x1bf0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x6 .x6 1)) 14
  · have hp : s16.pc = 0x1bf4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 0x81)) 13
  · have hp : s17.pc = 0x1bf8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 8)) 12
  · have hp : s18.pc = 0x1bfc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.SD .x28 .x6 0)) 11
  · have hp : s19.pc = 0x1c00 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s20 s21 _ (.base (.LUI .x28 0x81)) 10
  · have hp : s20.pc = 0x1c04 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.ADDI .x28 .x28 0xe0)) 9
  · have hp : s21.pc = 0x1c08 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.LD .x6 .x28 0)) 8
  · have hp : s22.pc = 0x1c0c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s23 s24 _ (.base (.ADDI .x6 .x6 1)) 7
  · have hp : s23.pc = 0x1c10 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s24.pc = 0x1c14 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 0xe0)) 5
  · have hp : s25.pc = 0x1c18 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s26.pc = 0x1c1c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s27 s28 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s27.pc = 0x1c20 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x28 .x28 0xd0)) 2
  · have hp : s28.pc = 0x1c24 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.LD .x7 .x28 0)) 1
  · have hp : s29.pc = 0x1c28 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,advanceState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,valid,valid8,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,BitVec.add_comm]
  apply OrdinarySteps.step s30 (advanceState s) _ (.base (.BNE .x6 .x7 (-1244))) 0
  · have hp : s30.pc = 0x1c2c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  exact OrdinarySteps.refl _

#print axioms advance_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Store67
