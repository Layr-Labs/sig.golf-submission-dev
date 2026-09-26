import SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopies67

/-! Exact 33-instruction Merkle-node query header for Fast2Byte. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeHeader67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def HeaderCode (image : Image) : Prop :=
  Keygen.instructionAt image 0x18ac = some (.base (.ADDI .x10 .x0 4)) ∧
  Keygen.instructionAt image 0x18b0 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x18b4 = some (.base (.ADDI .x28 .x28 0)) ∧
  Keygen.instructionAt image 0x18b8 = some (.base (.LD .x11 .x28 0)) ∧
  Keygen.instructionAt image 0x18bc = some (.base (.SLLI .x11 .x11 8)) ∧
  Keygen.instructionAt image 0x18c0 = some (.base (.ADD .x10 .x10 .x11)) ∧
  Keygen.instructionAt image 0x18c4 = some (.base (.LUI .x28 0x80)) ∧
  Keygen.instructionAt image 0x18c8 = some (.base (.ADDI .x28 .x28 0)) ∧
  Keygen.instructionAt image 0x18cc = some (.base (.SD .x28 .x10 0)) ∧
  Keygen.instructionAt image 0x18d0 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x18d4 = some (.base (.ADDI .x28 .x28 8)) ∧
  Keygen.instructionAt image 0x18d8 = some (.base (.LD .x11 .x28 0)) ∧
  Keygen.instructionAt image 0x18dc = some (.base (.LUI .x28 0x80)) ∧
  Keygen.instructionAt image 0x18e0 = some (.base (.ADDI .x28 .x28 8)) ∧
  Keygen.instructionAt image 0x18e4 = some (.base (.SD .x28 .x11 0)) ∧
  Keygen.instructionAt image 0x18e8 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x18ec = some (.base (.ADDI .x28 .x28 16)) ∧
  Keygen.instructionAt image 0x18f0 = some (.base (.LD .x11 .x28 0)) ∧
  Keygen.instructionAt image 0x18f4 = some (.base (.LUI .x28 0x80)) ∧
  Keygen.instructionAt image 0x18f8 = some (.base (.ADDI .x28 .x28 16)) ∧
  Keygen.instructionAt image 0x18fc = some (.base (.SD .x28 .x11 0)) ∧
  Keygen.instructionAt image 0x1900 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1904 = some (.base (.ADDI .x28 .x28 24)) ∧
  Keygen.instructionAt image 0x1908 = some (.base (.LD .x11 .x28 0)) ∧
  Keygen.instructionAt image 0x190c = some (.base (.LUI .x28 0x80)) ∧
  Keygen.instructionAt image 0x1910 = some (.base (.ADDI .x28 .x28 24)) ∧
  Keygen.instructionAt image 0x1914 = some (.base (.SD .x28 .x11 0)) ∧
  Keygen.instructionAt image 0x1918 = some (.base (.LUI .x10 0x80)) ∧
  Keygen.instructionAt image 0x191c = some (.base (.ADDI .x10 .x10 0)) ∧
  Keygen.instructionAt image 0x1920 = some (.base (.ADDI .x11 .x0 512)) ∧
  Keygen.instructionAt image 0x1924 = some (.base (.LUI .x12 0x80)) ∧
  Keygen.instructionAt image 0x1928 = some (.base (.ADDI .x12 .x12 0x300)) ∧
  Keygen.instructionAt image 0x192c = some (.base (.ADDI .x5 .x0 1))

theorem concrete_code : HeaderCode image := by
  unfold HeaderCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 4)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x80)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 512)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  execInstrBr s (.ADDI .x5 .x0 1)

theorem header_block (s : MachineState) (pc : s.pc = 0x18ac) :
    OrdinarySteps image s 33 (headerState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 4)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 0x80)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0)
  let s9 := execInstrBr s8 (.SD .x28 .x10 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x81)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 8)
  let s12 := execInstrBr s11 (.LD .x11 .x28 0)
  let s13 := execInstrBr s12 (.LUI .x28 0x80)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 8)
  let s15 := execInstrBr s14 (.SD .x28 .x11 0)
  let s16 := execInstrBr s15 (.LUI .x28 0x81)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 16)
  let s18 := execInstrBr s17 (.LD .x11 .x28 0)
  let s19 := execInstrBr s18 (.LUI .x28 0x80)
  let s20 := execInstrBr s19 (.ADDI .x28 .x28 16)
  let s21 := execInstrBr s20 (.SD .x28 .x11 0)
  let s22 := execInstrBr s21 (.LUI .x28 0x81)
  let s23 := execInstrBr s22 (.ADDI .x28 .x28 24)
  let s24 := execInstrBr s23 (.LD .x11 .x28 0)
  let s25 := execInstrBr s24 (.LUI .x28 0x80)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 24)
  let s27 := execInstrBr s26 (.SD .x28 .x11 0)
  let s28 := execInstrBr s27 (.LUI .x10 0x80)
  let s29 := execInstrBr s28 (.ADDI .x10 .x10 0)
  let s30 := execInstrBr s29 (.ADDI .x11 .x0 512)
  let s31 := execInstrBr s30 (.LUI .x12 0x80)
  let s32 := execInstrBr s31 (.ADDI .x12 .x12 0x300)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32⟩ := concrete_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 4)) 32
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 31
  · have hp : s1.pc = 0x18b0 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 30
  · have hp : s2.pc = 0x18b4 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 29
  · have hp : s3.pc = 0x18b8 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 28
  · have hp : s4.pc = 0x18bc := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 27
  · have hp : s5.pc = 0x18c0 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 26
  · have hp : s6.pc = 0x18c4 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0)) 25
  · have hp : s7.pc = 0x18c8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x10 0)) 24
  · have hp : s8.pc = 0x18cc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 23
  · have hp : s9.pc = 0x18d0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 8)) 22
  · have hp : s10.pc = 0x18d4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x11 .x28 0)) 21
  · have hp : s11.pc = 0x18d8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 0x80)) 20
  · have hp : s12.pc = 0x18dc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 8)) 19
  · have hp : s13.pc = 0x18e0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x28 .x11 0)) 18
  · have hp : s14.pc = 0x18e4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 0x81)) 17
  · have hp : s15.pc = 0x18e8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 16)) 16
  · have hp : s16.pc = 0x18ec := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LD .x11 .x28 0)) 15
  · have hp : s17.pc = 0x18f0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 0x80)) 14
  · have hp : s18.pc = 0x18f4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 16)) 13
  · have hp : s19.pc = 0x18f8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SD .x28 .x11 0)) 12
  · have hp : s20.pc = 0x18fc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s21.pc = 0x1900 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 24)) 10
  · have hp : s22.pc = 0x1904 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.LD .x11 .x28 0)) 9
  · have hp : s23.pc = 0x1908 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 0x80)) 8
  · have hp : s24.pc = 0x190c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 24)) 7
  · have hp : s25.pc = 0x1910 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.SD .x28 .x11 0)) 6
  · have hp : s26.pc = 0x1914 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s27 s28 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s27.pc = 0x1918 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s28.pc = 0x191c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.ADDI .x11 .x0 512)) 3
  · have hp : s29.pc = 0x1920 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s30.pc = 0x1924 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s31.pc = 0x1928 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · rfl
  apply OrdinarySteps.step s32 _ _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s32.pc = 0x192c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · rfl
  exact OrdinarySteps.refl _

theorem header_pc (s : MachineState) (pc : s.pc = 0x18ac) :
    (headerState s).pc = 0x1930 := by
  simp [headerState,execInstrBr,pc]

theorem header_fields (s : MachineState) (pc : s.pc = 0x18ac) :
    GroupedBalancedByteFastNodeQuery67.Fields (headerState s) := by
  constructor
  · exact header_pc s pc
  · simp [headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [headerState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastNodeHeader67
