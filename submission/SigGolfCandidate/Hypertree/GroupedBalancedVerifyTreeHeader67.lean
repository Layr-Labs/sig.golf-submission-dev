import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeStart67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHighFrame67

/-! One verifier tree round shifts the 192-bit path index and selects its branch. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHeader67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.LD .x10 .x28 0)
  let s := execInstrBr s (.ANDI .x11 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 32)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.SRLI .x6 .x6 1)
  let s := execInstrBr s (.SLLI .x11 .x7 63)
  let s := execInstrBr s (.ADD .x6 .x6 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.SRLI .x7 .x7 1)
  let s := execInstrBr s (.SLLI .x11 .x10 63)
  let s := execInstrBr s (.ADD .x7 .x7 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.SRLI .x10 .x10 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 32)
  execInstrBr s (.LD .x6 .x28 0)

private theorem header_code :
    Keygen.instructionAt image 0x1290 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1294 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1298 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x129c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12a0 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x12a4 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x12a8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12ac = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x12b0 = some (.base (.LD .x10 .x28 0)) ∧
    Keygen.instructionAt image 0x12b4 = some (.base (.ANDI .x11 .x6 1)) ∧
    Keygen.instructionAt image 0x12b8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12bc = some (.base (.ADDI .x28 .x28 32)) ∧
    Keygen.instructionAt image 0x12c0 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x12c4 = some (.base (.SRLI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x12c8 = some (.base (.SLLI .x11 .x7 63)) ∧
    Keygen.instructionAt image 0x12cc = some (.base (.ADD .x6 .x6 .x11)) ∧
    Keygen.instructionAt image 0x12d0 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12d4 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x12d8 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x12dc = some (.base (.SRLI .x7 .x7 1)) ∧
    Keygen.instructionAt image 0x12e0 = some (.base (.SLLI .x11 .x10 63)) ∧
    Keygen.instructionAt image 0x12e4 = some (.base (.ADD .x7 .x7 .x11)) ∧
    Keygen.instructionAt image 0x12e8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12ec = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x12f0 = some (.base (.SD .x28 .x7 0)) ∧
    Keygen.instructionAt image 0x12f4 = some (.base (.SRLI .x10 .x10 1)) ∧
    Keygen.instructionAt image 0x12f8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12fc = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x1300 = some (.base (.SD .x28 .x10 0)) ∧
    Keygen.instructionAt image 0x1304 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1308 = some (.base (.ADDI .x28 .x28 32)) ∧
    Keygen.instructionAt image 0x130c = some (.base (.LD .x6 .x28 0))
    := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem header_steps (s : MachineState) (pc : s.pc = 0x1290) :
    OrdinarySteps image s 32 (headerState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 16)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 24)
  let s9 := execInstrBr s8 (.LD .x10 .x28 0)
  let s10 := execInstrBr s9 (.ANDI .x11 .x6 1)
  let s11 := execInstrBr s10 (.LUI .x28 0x81)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 32)
  let s13 := execInstrBr s12 (.SD .x28 .x11 0)
  let s14 := execInstrBr s13 (.SRLI .x6 .x6 1)
  let s15 := execInstrBr s14 (.SLLI .x11 .x7 63)
  let s16 := execInstrBr s15 (.ADD .x6 .x6 .x11)
  let s17 := execInstrBr s16 (.LUI .x28 0x81)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 8)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.SRLI .x7 .x7 1)
  let s21 := execInstrBr s20 (.SLLI .x11 .x10 63)
  let s22 := execInstrBr s21 (.ADD .x7 .x7 .x11)
  let s23 := execInstrBr s22 (.LUI .x28 0x81)
  let s24 := execInstrBr s23 (.ADDI .x28 .x28 16)
  let s25 := execInstrBr s24 (.SD .x28 .x7 0)
  let s26 := execInstrBr s25 (.SRLI .x10 .x10 1)
  let s27 := execInstrBr s26 (.LUI .x28 0x81)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 24)
  let s29 := execInstrBr s28 (.SD .x28 .x10 0)
  let s30 := execInstrBr s29 (.LUI .x28 0x81)
  let s31 := execInstrBr s30 (.ADDI .x28 .x28 32)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31⟩ := header_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 31
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 30
  · have hp : s1.pc = 0x1294 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 29
  · have hp : s2.pc = 0x1298 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 28
  · have hp : s3.pc = 0x129c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 16)) 27
  · have hp : s4.pc = 0x12a0 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 26
  · have hp : s5.pc = 0x12a4 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 25
  · have hp : s6.pc = 0x12a8 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 24)) 24
  · have hp : s7.pc = 0x12ac := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.LD .x10 .x28 0)) 23
  · have hp : s8.pc = 0x12b0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.ANDI .x11 .x6 1)) 22
  · have hp : s9.pc = 0x12b4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x81)) 21
  · have hp : s10.pc = 0x12b8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 32)) 20
  · have hp : s11.pc = 0x12bc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.SD .x28 .x11 0)) 19
  · have hp : s12.pc = 0x12c0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s13 s14 _ (.base (.SRLI .x6 .x6 1)) 18
  · have hp : s13.pc = 0x12c4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SLLI .x11 .x7 63)) 17
  · have hp : s14.pc = 0x12c8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADD .x6 .x6 .x11)) 16
  · have hp : s15.pc = 0x12cc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 0x81)) 15
  · have hp : s16.pc = 0x12d0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 8)) 14
  · have hp : s17.pc = 0x12d4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x6 0)) 13
  · have hp : s18.pc = 0x12d8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.SRLI .x7 .x7 1)) 12
  · have hp : s19.pc = 0x12dc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SLLI .x11 .x10 63)) 11
  · have hp : s20.pc = 0x12e0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.ADD .x7 .x7 .x11)) 10
  · have hp : s21.pc = 0x12e4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.LUI .x28 0x81)) 9
  · have hp : s22.pc = 0x12e8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.ADDI .x28 .x28 16)) 8
  · have hp : s23.pc = 0x12ec := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.SD .x28 .x7 0)) 7
  · have hp : s24.pc = 0x12f0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s25 s26 _ (.base (.SRLI .x10 .x10 1)) 6
  · have hp : s25.pc = 0x12f4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.LUI .x28 0x81)) 5
  · have hp : s26.pc = 0x12f8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x28 .x28 24)) 4
  · have hp : s27.pc = 0x12fc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.SD .x28 .x10 0)) 3
  · have hp : s28.pc = 0x1300 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  apply OrdinarySteps.step s29 s30 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s29.pc = 0x1304 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.ADDI .x28 .x28 32)) 1
  · have hp : s30.pc = 0x1308 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 (headerState s) _ (.base (.LD .x6 .x28 0)) 0
  · have hp : s31.pc = 0x130c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · simp [headerState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
  exact OrdinarySteps.refl _

theorem header_pc (s : MachineState) (pc : s.pc = 0x1290) :
    (headerState s).pc = 0x1310 := by
  simp [headerState,execInstrBr,pc]

theorem header_pointer (s : MachineState) :
    (headerState s).getMem 0x81048 = s.getMem 0x81048 := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem header_count (s : MachineState) :
    (headerState s).getMem 0x81050 = s.getMem 0x81050 := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem header_safe (s : MachineState) :
    GroupedBalancedVerifyTreeHighFrame67.SafeFrame s (headerState s) := by
  constructor
  · intro a ha
    simp [headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]
    split_ifs with e1 e2 e3 e4
    all_goals
      try { have hn := congrArg BitVec.toNat e1; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e2; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e3; simp at hn; omega }
      try { have hn := congrArg BitVec.toNat e4; simp at hn; omega }
      try rfl
  · simp [headerState,execInstrBr,MachineState.getReg_setReg_ne]

theorem branch_count (s : MachineState) :
    (execInstrBr s (.BEQ .x6 .x0 88)).getMem 0x81050 = s.getMem 0x81050 := by
  simp [execInstrBr]

theorem branch_safe (s : MachineState) :
    GroupedBalancedVerifyTreeHighFrame67.SafeFrame s
      (execInstrBr s (.BEQ .x6 .x0 88)) := by
  constructor
  · intro a _
    simp [execInstrBr]
  · simp [execInstrBr,MachineState.getReg_setReg_ne]

theorem header_selector (s : MachineState) :
    (headerState s).getReg .x6 = s.getMem 0x81008#64 &&& 1#64 ∧
    (headerState s).getMem 0x81020#64 = s.getMem 0x81008#64 &&& 1#64 := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem header_bit (s : MachineState) :
    (headerState s).getReg .x6 = 0 ∨
    (headerState s).getReg .x6 = 1 := by
  rw [(header_selector s).1]
  have bound : (s.getMem 0x81008#64 &&& 1#64).toNat ≤ 1 := by
    rw [BitVec.toNat_and]
    have h : (s.getMem 0x81008#64).toNat &&& 1 ≤ 1 := Nat.and_le_right
    simpa using h
  have cases : (s.getMem 0x81008#64 &&& 1#64).toNat = 0 ∨
      (s.getMem 0x81008#64 &&& 1#64).toNat = 1 := by omega
  rcases cases with h | h
  · left
    apply BitVec.eq_of_toNat_eq
    simpa using h
  · right
    apply BitVec.eq_of_toNat_eq
    simpa using h

private theorem branch_code :
    Keygen.instructionAt image 0x1310 = some (.base (.BEQ .x6 .x0 88)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem branch_step (s : MachineState) (pc : s.pc = 0x1310) :
    OrdinarySteps image s 1 (execInstrBr s (.BEQ .x6 .x0 88)) := by
  apply OrdinarySteps.step s (execInstrBr s (.BEQ .x6 .x0 88)) _
    (.base (.BEQ .x6 .x0 88)) 0
  · simpa only [Keygen.fetch_at,pc] using branch_code
  · rfl
  exact OrdinarySteps.refl _

theorem branch_pc (s : MachineState) (pc : s.pc = 0x1310)
    (bit : s.getReg .x6 = 0 ∨ s.getReg .x6 = 1) :
    (execInstrBr s (.BEQ .x6 .x0 88)).pc =
      (if s.getReg .x6 = 0 then 0x1368 else 0x1314) := by
  rcases bit with h | h
  · simp [execInstrBr,pc,h,signExtend13]
  · simp [execInstrBr,pc,h,signExtend13]

#print axioms header_steps
#print axioms header_bit
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeHeader67
