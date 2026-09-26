import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeCall67
import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67Byte
import SigGolfCandidate.Hypertree.KeygenTrace
import SigGolfCandidate.Hypertree.SignRandomizer

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Header67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Hash67. -/
section
/-! The direct67 H3 leaf header, through its oracle call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Header67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedSignImage67Byte.image
def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 3)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 128)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x10 128)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.LUI .x11 2)
  let s := execInstrBr s (.ADDI .x11 .x11 640)
  let s := execInstrBr s (.LUI .x12 128)
  let s := execInstrBr s (.ADDI .x12 .x12 768)
  execInstrBr s (.ADDI .x5 .x0 1)
private theorem header_code :
    Keygen.instructionAt image 0x1b28 = some (.base (.ADDI .x10 .x0 3)) ∧
    Keygen.instructionAt image 0x1b2c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1b30 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1b34 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1b38 = some (.base (.SLLI .x11 .x11 8)) ∧
    Keygen.instructionAt image 0x1b3c = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 0x1b40 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x1b44 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1b48 = some (.base (.SD .x28 .x10 0)) ∧
    Keygen.instructionAt image 0x1b4c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1b50 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1b54 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1b58 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x1b5c = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1b60 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1b64 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1b68 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x1b6c = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1b70 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x1b74 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x1b78 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1b7c = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1b80 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x1b84 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1b88 = some (.base (.LUI .x28 128)) ∧
    Keygen.instructionAt image 0x1b8c = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x1b90 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1b94 = some (.base (.LUI .x10 128)) ∧
    Keygen.instructionAt image 0x1b98 = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x1b9c = some (.base (.LUI .x11 2)) ∧
    Keygen.instructionAt image 0x1ba0 = some (.base (.ADDI .x11 .x11 640)) ∧
    Keygen.instructionAt image 0x1ba4 = some (.base (.LUI .x12 128)) ∧
    Keygen.instructionAt image 0x1ba8 = some (.base (.ADDI .x12 .x12 768)) ∧
    Keygen.instructionAt image 0x1bac = some (.base (.ADDI .x5 .x0 1))
    := by
  unfold image GroupedBalancedSignImage67Byte.image
  decide
theorem header_steps (s : MachineState) (pc : s.pc = 0x1b28) :
    OrdinarySteps image s 34 (headerState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 3)
  let s2 := execInstrBr s1 (.LUI .x28 129)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x11 .x28 0)
  let s5 := execInstrBr s4 (.SLLI .x11 .x11 8)
  let s6 := execInstrBr s5 (.ADD .x10 .x10 .x11)
  let s7 := execInstrBr s6 (.LUI .x28 128)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0)
  let s9 := execInstrBr s8 (.SD .x28 .x10 0)
  let s10 := execInstrBr s9 (.LUI .x28 129)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 8)
  let s12 := execInstrBr s11 (.LD .x11 .x28 0)
  let s13 := execInstrBr s12 (.LUI .x28 128)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 8)
  let s15 := execInstrBr s14 (.SD .x28 .x11 0)
  let s16 := execInstrBr s15 (.LUI .x28 129)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 16)
  let s18 := execInstrBr s17 (.LD .x11 .x28 0)
  let s19 := execInstrBr s18 (.LUI .x28 128)
  let s20 := execInstrBr s19 (.ADDI .x28 .x28 16)
  let s21 := execInstrBr s20 (.SD .x28 .x11 0)
  let s22 := execInstrBr s21 (.LUI .x28 129)
  let s23 := execInstrBr s22 (.ADDI .x28 .x28 24)
  let s24 := execInstrBr s23 (.LD .x11 .x28 0)
  let s25 := execInstrBr s24 (.LUI .x28 128)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 24)
  let s27 := execInstrBr s26 (.SD .x28 .x11 0)
  let s28 := execInstrBr s27 (.LUI .x10 128)
  let s29 := execInstrBr s28 (.ADDI .x10 .x10 0)
  let s30 := execInstrBr s29 (.LUI .x11 2)
  let s31 := execInstrBr s30 (.ADDI .x11 .x11 640)
  let s32 := execInstrBr s31 (.LUI .x12 128)
  let s33 := execInstrBr s32 (.ADDI .x12 .x12 768)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33⟩ := header_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 3)) 33
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 129)) 32
  · have hp : s1.pc = 0x1b2c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 31
  · have hp : s2.pc = 0x1b30 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 30
  · have hp : s3.pc = 0x1b34 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 29
  · have hp : s4.pc = 0x1b38 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 28
  · have hp : s5.pc = 0x1b3c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 128)) 27
  · have hp : s6.pc = 0x1b40 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0)) 26
  · have hp : s7.pc = 0x1b44 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x10 0)) 25
  · have hp : s8.pc = 0x1b48 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 129)) 24
  · have hp : s9.pc = 0x1b4c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 8)) 23
  · have hp : s10.pc = 0x1b50 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x11 .x28 0)) 22
  · have hp : s11.pc = 0x1b54 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 128)) 21
  · have hp : s12.pc = 0x1b58 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 8)) 20
  · have hp : s13.pc = 0x1b5c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x28 .x11 0)) 19
  · have hp : s14.pc = 0x1b60 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 129)) 18
  · have hp : s15.pc = 0x1b64 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 16)) 17
  · have hp : s16.pc = 0x1b68 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LD .x11 .x28 0)) 16
  · have hp : s17.pc = 0x1b6c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 128)) 15
  · have hp : s18.pc = 0x1b70 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 16)) 14
  · have hp : s19.pc = 0x1b74 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SD .x28 .x11 0)) 13
  · have hp : s20.pc = 0x1b78 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 129)) 12
  · have hp : s21.pc = 0x1b7c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 24)) 11
  · have hp : s22.pc = 0x1b80 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.LD .x11 .x28 0)) 10
  · have hp : s23.pc = 0x1b84 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 128)) 9
  · have hp : s24.pc = 0x1b88 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 24)) 8
  · have hp : s25.pc = 0x1b8c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.SD .x28 .x11 0)) 7
  · have hp : s26.pc = 0x1b90 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,headerState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s27 s28 _ (.base (.LUI .x10 128)) 6
  · have hp : s27.pc = 0x1b94 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x10 .x10 0)) 5
  · have hp : s28.pc = 0x1b98 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.LUI .x11 2)) 4
  · have hp : s29.pc = 0x1b9c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.ADDI .x11 .x11 640)) 3
  · have hp : s30.pc = 0x1ba0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.LUI .x12 128)) 2
  · have hp : s31.pc = 0x1ba4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · rfl
  apply OrdinarySteps.step s32 s33 _ (.base (.ADDI .x12 .x12 768)) 1
  · have hp : s32.pc = 0x1ba8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · rfl
  apply OrdinarySteps.step s33 (headerState s) _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s33.pc = 0x1bac := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c33
  · rfl
  exact OrdinarySteps.refl _
theorem header_pc (s : MachineState) (pc : s.pc = 0x1b28) :
    (headerState s).pc = 0x1bb0 := by
  simp [headerState,execInstrBr,pc]

theorem header_regs (s : MachineState) :
    (headerState s).getReg .x5 = 1 ∧
    (headerState s).getReg .x10 = 0x80000 ∧
    (headerState s).getReg .x11 = 8832 ∧
    (headerState s).getReg .x12 = 0x80300 := by
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem header_high_frame (s : MachineState) (a : Word)
    (high : 0x81000 ≤ a.toNat) :
    (headerState s).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80000#64 := by
    intro eq
    rw [eq] at high
    norm_num at high
  have h8 : a ≠ 0x80008#64 := by
    intro eq
    rw [eq] at high
    norm_num at high
  have h10 : a ≠ 0x80010#64 := by
    intro eq
    rw [eq] at high
    norm_num at high
  have h18 : a ≠ 0x80018#64 := by
    intro eq
    rw [eq] at high
    norm_num at high
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    h0,h8,h10,h18]

theorem header_low_frame (s : MachineState) (a : Word)
    (low : a.toNat < 0x80000) :
    (headerState s).getMem a = s.getMem a := by
  have h0 : a ≠ 0x80000#64 := by
    intro eq
    rw [eq] at low
    norm_num at low
  have h8 : a ≠ 0x80008#64 := by
    intro eq
    rw [eq] at low
    norm_num at low
  have h10 : a ≠ 0x80010#64 := by
    intro eq
    rw [eq] at low
    norm_num at low
  have h18 : a ≠ 0x80018#64 := by
    intro eq
    rw [eq] at low
    norm_num at low
  simp [headerState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    h0,h8,h10,h18]

#print axioms header_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Header67

end

/-! The upper WOTS endpoint table enters its H3 leaf compression call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Hash67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev prepared := GroupedBalancedSignUpperH3Header67.headerState

theorem hash_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1bb0)
    (fields : s.getReg .x5 = 1 ∧ s.getReg .x10 = 0x80000 ∧
      s.getReg .x11 = 8832 ∧ s.getReg .x12 = 0x80300) :
    Trace hash image s 1 144 1 18
      (writeHash s (hash (hashInput s))) := by
  have code : fetch image s = some (.base .ECALL) := by
    have hc : Keygen.instructionAt image 0x1bb0 = some (.base .ECALL) := by
      decide
    change Keygen.instructionAt image s.pc = some (.base .ECALL)
    rw [pc]
    exact hc
  obtain ⟨service,source,bits,destination⟩ := fields
  have valid : hashArgumentsValid s = true := by
    simp [hashArgumentsValid,source,bits,destination,
      accessValid,rangeValid,MEMORY_BYTES]
  have len : (hashInput s).1 = 8832 := by simp [hashInput,bits]
  simpa [len,compressions] using
    Trace.hash s _ 0 0 0 0 code service valid (Trace.refl _)

theorem header_hash (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1b28) :
    ∃ final,
      Trace hash image s 35 178 1 18 final ∧
      final.pc = 0x1bb4 ∧
      (∀ a : Word, 0x81000 ≤ a.toNat → final.getMem a = s.getMem a) := by
  let ready := prepared s
  have first : Trace hash image s 34 34 0 0 ready :=
    (GroupedBalancedSignUpperH3Header67.header_steps s pc).trace
  have readyPc := GroupedBalancedSignUpperH3Header67.header_pc s pc
  have readyRegs := GroupedBalancedSignUpperH3Header67.header_regs s
  let final := writeHash ready (hash (hashInput ready))
  have second : Trace hash image ready 1 144 1 18 final :=
    hash_trace hash ready readyPc readyRegs
  refine ⟨final,by simpa only [Nat.reduceAdd] using first.trans second,?_,?_⟩
  · change ready.pc + 4 = 0x1bb4
    rw [readyPc]
    decide
  · intro a high
    have readyHigh : ready.getMem a = s.getMem a :=
      GroupedBalancedSignUpperH3Header67.header_high_frame s a high
    have finalHigh : final.getMem a = ready.getMem a := by
      apply Signing.hash_answer_frame ready (hash (hashInput ready))
        readyRegs.2.2.2 a
      intro i same
      have hn := congrArg BitVec.toNat same
      simp only [Signing.wordAddress,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 0x80300+8*i.val < 2^64)] at hn
      omega
    exact finalHigh.trans readyHigh

#print axioms hash_trace
#print axioms header_hash
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH3Hash67
