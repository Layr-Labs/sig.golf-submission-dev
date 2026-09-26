import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafCopy67

/-! Exact 37-instruction upper-leaf query prelude for Fast2Byte. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPrelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def PreludeCode (image : Image) : Prop :=
  Keygen.instructionAt image 0x1684 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1688 = some (.base (.ADDI .x28 .x28 0x48)) ∧
  Keygen.instructionAt image 0x168c = some (.base (.SD .x28 .x22 0)) ∧
  Keygen.instructionAt image 0x1690 = some (.base (.ADDI .x10 .x0 3)) ∧
  Keygen.instructionAt image 0x1694 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x1698 = some (.base (.ADDI .x28 .x28 0)) ∧
  Keygen.instructionAt image 0x169c = some (.base (.LD .x11 .x28 0)) ∧
  Keygen.instructionAt image 0x16a0 = some (.base (.SLLI .x11 .x11 8)) ∧
  Keygen.instructionAt image 0x16a4 = some (.base (.ADD .x10 .x10 .x11)) ∧
  Keygen.instructionAt image 0x16a8 = some (.base (.LUI .x28 0x80)) ∧
  Keygen.instructionAt image 0x16ac = some (.base (.ADDI .x28 .x28 0)) ∧
  Keygen.instructionAt image 0x16b0 = some (.base (.SD .x28 .x10 0)) ∧
  Keygen.instructionAt image 0x16b4 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x16b8 = some (.base (.ADDI .x28 .x28 8)) ∧
  Keygen.instructionAt image 0x16bc = some (.base (.LD .x11 .x28 0)) ∧
  Keygen.instructionAt image 0x16c0 = some (.base (.LUI .x28 0x80)) ∧
  Keygen.instructionAt image 0x16c4 = some (.base (.ADDI .x28 .x28 8)) ∧
  Keygen.instructionAt image 0x16c8 = some (.base (.SD .x28 .x11 0)) ∧
  Keygen.instructionAt image 0x16cc = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x16d0 = some (.base (.ADDI .x28 .x28 16)) ∧
  Keygen.instructionAt image 0x16d4 = some (.base (.LD .x11 .x28 0)) ∧
  Keygen.instructionAt image 0x16d8 = some (.base (.LUI .x28 0x80)) ∧
  Keygen.instructionAt image 0x16dc = some (.base (.ADDI .x28 .x28 16)) ∧
  Keygen.instructionAt image 0x16e0 = some (.base (.SD .x28 .x11 0)) ∧
  Keygen.instructionAt image 0x16e4 = some (.base (.LUI .x28 0x81)) ∧
  Keygen.instructionAt image 0x16e8 = some (.base (.ADDI .x28 .x28 24)) ∧
  Keygen.instructionAt image 0x16ec = some (.base (.LD .x11 .x28 0)) ∧
  Keygen.instructionAt image 0x16f0 = some (.base (.LUI .x28 0x80)) ∧
  Keygen.instructionAt image 0x16f4 = some (.base (.ADDI .x28 .x28 24)) ∧
  Keygen.instructionAt image 0x16f8 = some (.base (.SD .x28 .x11 0)) ∧
  Keygen.instructionAt image 0x16fc = some (.base (.LUI .x10 0x80)) ∧
  Keygen.instructionAt image 0x1700 = some (.base (.ADDI .x10 .x10 0)) ∧
  Keygen.instructionAt image 0x1704 = some (.base (.LUI .x11 2)) ∧
  Keygen.instructionAt image 0x1708 = some (.base (.ADDI .x11 .x11 0x280)) ∧
  Keygen.instructionAt image 0x170c = some (.base (.LUI .x12 0x80)) ∧
  Keygen.instructionAt image 0x1710 = some (.base (.ADDI .x12 .x12 0x300)) ∧
  Keygen.instructionAt image 0x1714 = some (.base (.ADDI .x5 .x0 1))

theorem concrete_code : PreludeCode image := by
  unfold PreludeCode image GroupedBalancedVerifyImage67Fast2Byte.image
  decide

def preludeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x48)
  let s := execInstrBr s (.SD .x28 .x22 0)
  let s := execInstrBr s (.ADDI .x10 .x0 3)
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
  let s := execInstrBr s (.LUI .x11 2)
  let s := execInstrBr s (.ADDI .x11 .x11 0x280)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x300)
  execInstrBr s (.ADDI .x5 .x0 1)

theorem prelude_block (s : MachineState) (pc : s.pc = 0x1684) :
    OrdinarySteps image s 37 (preludeState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x48)
  let s3 := execInstrBr s2 (.SD .x28 .x22 0)
  let s4 := execInstrBr s3 (.ADDI .x10 .x0 3)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0)
  let s7 := execInstrBr s6 (.LD .x11 .x28 0)
  let s8 := execInstrBr s7 (.SLLI .x11 .x11 8)
  let s9 := execInstrBr s8 (.ADD .x10 .x10 .x11)
  let s10 := execInstrBr s9 (.LUI .x28 0x80)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 0)
  let s12 := execInstrBr s11 (.SD .x28 .x10 0)
  let s13 := execInstrBr s12 (.LUI .x28 0x81)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 8)
  let s15 := execInstrBr s14 (.LD .x11 .x28 0)
  let s16 := execInstrBr s15 (.LUI .x28 0x80)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 8)
  let s18 := execInstrBr s17 (.SD .x28 .x11 0)
  let s19 := execInstrBr s18 (.LUI .x28 0x81)
  let s20 := execInstrBr s19 (.ADDI .x28 .x28 16)
  let s21 := execInstrBr s20 (.LD .x11 .x28 0)
  let s22 := execInstrBr s21 (.LUI .x28 0x80)
  let s23 := execInstrBr s22 (.ADDI .x28 .x28 16)
  let s24 := execInstrBr s23 (.SD .x28 .x11 0)
  let s25 := execInstrBr s24 (.LUI .x28 0x81)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 24)
  let s27 := execInstrBr s26 (.LD .x11 .x28 0)
  let s28 := execInstrBr s27 (.LUI .x28 0x80)
  let s29 := execInstrBr s28 (.ADDI .x28 .x28 24)
  let s30 := execInstrBr s29 (.SD .x28 .x11 0)
  let s31 := execInstrBr s30 (.LUI .x10 0x80)
  let s32 := execInstrBr s31 (.ADDI .x10 .x10 0)
  let s33 := execInstrBr s32 (.LUI .x11 2)
  let s34 := execInstrBr s33 (.ADDI .x11 .x11 0x280)
  let s35 := execInstrBr s34 (.LUI .x12 0x80)
  let s36 := execInstrBr s35 (.ADDI .x12 .x12 0x300)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36⟩ := concrete_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 36
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x48)) 35
  · have hp : s1.pc = 0x1688 := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x28 .x22 0)) 34
  · have hp : s2.pc = 0x168c := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x10 .x0 3)) 33
  · have hp : s3.pc = 0x1690 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 32
  · have hp : s4.pc = 0x1694 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0)) 31
  · have hp : s5.pc = 0x1698 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LD .x11 .x28 0)) 30
  · have hp : s6.pc = 0x169c := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.SLLI .x11 .x11 8)) 29
  · have hp : s7.pc = 0x16a0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADD .x10 .x10 .x11)) 28
  · have hp : s8.pc = 0x16a4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x80)) 27
  · have hp : s9.pc = 0x16a8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 0)) 26
  · have hp : s10.pc = 0x16ac := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x10 0)) 25
  · have hp : s11.pc = 0x16b0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 0x81)) 24
  · have hp : s12.pc = 0x16b4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 8)) 23
  · have hp : s13.pc = 0x16b8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LD .x11 .x28 0)) 22
  · have hp : s14.pc = 0x16bc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 0x80)) 21
  · have hp : s15.pc = 0x16c0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 8)) 20
  · have hp : s16.pc = 0x16c4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.SD .x28 .x11 0)) 19
  · have hp : s17.pc = 0x16c8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 0x81)) 18
  · have hp : s18.pc = 0x16cc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 16)) 17
  · have hp : s19.pc = 0x16d0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.LD .x11 .x28 0)) 16
  · have hp : s20.pc = 0x16d4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 0x80)) 15
  · have hp : s21.pc = 0x16d8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 16)) 14
  · have hp : s22.pc = 0x16dc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.SD .x28 .x11 0)) 13
  · have hp : s23.pc = 0x16e0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 0x81)) 12
  · have hp : s24.pc = 0x16e4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 24)) 11
  · have hp : s25.pc = 0x16e8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.LD .x11 .x28 0)) 10
  · have hp : s26.pc = 0x16ec := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s27 s28 _ (.base (.LUI .x28 0x80)) 9
  · have hp : s27.pc = 0x16f0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x28 .x28 24)) 8
  · have hp : s28.pc = 0x16f4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.SD .x28 .x11 0)) 7
  · have hp : s29.pc = 0x16f8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s30 s31 _ (.base (.LUI .x10 0x80)) 6
  · have hp : s30.pc = 0x16fc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.ADDI .x10 .x10 0)) 5
  · have hp : s31.pc = 0x1700 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · rfl
  apply OrdinarySteps.step s32 s33 _ (.base (.LUI .x11 2)) 4
  · have hp : s32.pc = 0x1704 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · rfl
  apply OrdinarySteps.step s33 s34 _ (.base (.ADDI .x11 .x11 0x280)) 3
  · have hp : s33.pc = 0x1708 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c33
  · rfl
  apply OrdinarySteps.step s34 s35 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s34.pc = 0x170c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c34
  · rfl
  apply OrdinarySteps.step s35 s36 _ (.base (.ADDI .x12 .x12 0x300)) 1
  · have hp : s35.pc = 0x1710 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c35
  · rfl
  apply OrdinarySteps.step s36 _ _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s36.pc = 0x1714 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c36
  · rfl
  exact OrdinarySteps.refl _

theorem prelude_pc (s : MachineState) (pc : s.pc = 0x1684) :
    (preludeState s).pc = 0x1718 := by
  simp [preludeState,execInstrBr,pc]

theorem prelude_fields (s : MachineState) (pc : s.pc = 0x1684) :
    GroupedBalancedByteFastLeafQuery67.Fields (preludeState s) := by
  constructor
  · exact prelude_pc s pc
  · simp [preludeState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [preludeState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [preludeState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  · simp [preludeState,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPrelude67
