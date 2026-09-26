import SigGolfCandidate.Hypertree.GroupedBalancedSignIndexPrefix67
import SigGolfCandidate.Hypertree.KeygenDomain
import SigGolfCandidate.Hypertree.GroupedBottomTree

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Prelude67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Query67. -/
section
/-! Exact fixed 33-instruction signer H1 bottom-secret query prelude. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Prelude67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def image : Image := GroupedBalancedSignImage67.image

def preludeState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x10 .x0 1)
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
  let s := execInstrBr s (.ADDI .x12 .x12 768)
  execInstrBr s (.ADDI .x5 .x0 1)

private theorem prelude_code :
    Keygen.instructionAt image 0x12f4 = some (.base (.ADDI .x10 .x0 1)) ∧
    Keygen.instructionAt image 0x12f8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x12fc = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1300 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1304 = some (.base (.SLLI .x11 .x11 8)) ∧
    Keygen.instructionAt image 0x1308 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 0x130c = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1310 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1314 = some (.base (.SD .x28 .x10 0)) ∧
    Keygen.instructionAt image 0x1318 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x131c = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1320 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1324 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1328 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x132c = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1330 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1334 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x1338 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x133c = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1340 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x1344 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1348 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x134c = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x1350 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1354 = some (.base (.LUI .x28 0x80)) ∧
    Keygen.instructionAt image 0x1358 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x135c = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x1360 = some (.base (.LUI .x10 0x80)) ∧
    Keygen.instructionAt image 0x1364 = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x1368 = some (.base (.ADDI .x11 .x0 512)) ∧
    Keygen.instructionAt image 0x136c = some (.base (.LUI .x12 0x80)) ∧
    Keygen.instructionAt image 0x1370 = some (.base (.ADDI .x12 .x12 768)) ∧
    Keygen.instructionAt image 0x1374 = some (.base (.ADDI .x5 .x0 1)) := by
  unfold image GroupedBalancedSignImage67.image
  decide

theorem prelude_steps (s : MachineState) (pc : s.pc = 0x12f4) :
    OrdinarySteps image s 33 (preludeState s) := by
  let s1 := execInstrBr s (.ADDI .x10 .x0 1)
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
  let s32 := execInstrBr s31 (.ADDI .x12 .x12 768)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32⟩ := prelude_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x10 .x0 1)) 32
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 31
  · have hp : s1.pc = 0x12f8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 30
  · have hp : s2.pc = 0x12fc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x11 .x28 0)) 29
  · have hp : s3.pc = 0x1300 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.SLLI .x11 .x11 8)) 28
  · have hp : s4.pc = 0x1304 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x10 .x10 .x11)) 27
  · have hp : s5.pc = 0x1308 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x80)) 26
  · have hp : s6.pc = 0x130c := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0)) 25
  · have hp : s7.pc = 0x1310 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x10 0)) 24
  · have hp : s8.pc = 0x1314 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 23
  · have hp : s9.pc = 0x1318 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 8)) 22
  · have hp : s10.pc = 0x131c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x11 .x28 0)) 21
  · have hp : s11.pc = 0x1320 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 0x80)) 20
  · have hp : s12.pc = 0x1324 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 8)) 19
  · have hp : s13.pc = 0x1328 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x28 .x11 0)) 18
  · have hp : s14.pc = 0x132c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 0x81)) 17
  · have hp : s15.pc = 0x1330 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 16)) 16
  · have hp : s16.pc = 0x1334 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LD .x11 .x28 0)) 15
  · have hp : s17.pc = 0x1338 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s18 s19 _ (.base (.LUI .x28 0x80)) 14
  · have hp : s18.pc = 0x133c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.ADDI .x28 .x28 16)) 13
  · have hp : s19.pc = 0x1340 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.SD .x28 .x11 0)) 12
  · have hp : s20.pc = 0x1344 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s21 s22 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s21.pc = 0x1348 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · rfl
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x28 .x28 24)) 10
  · have hp : s22.pc = 0x134c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.LD .x11 .x28 0)) 9
  · have hp : s23.pc = 0x1350 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 0x80)) 8
  · have hp : s24.pc = 0x1354 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 24)) 7
  · have hp : s25.pc = 0x1358 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.SD .x28 .x11 0)) 6
  · have hp : s26.pc = 0x135c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s27 s28 _ (.base (.LUI .x10 0x80)) 5
  · have hp : s27.pc = 0x1360 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x10 .x10 0)) 4
  · have hp : s28.pc = 0x1364 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.ADDI .x11 .x0 512)) 3
  · have hp : s29.pc = 0x1368 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.LUI .x12 0x80)) 2
  · have hp : s30.pc = 0x136c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.ADDI .x12 .x12 768)) 1
  · have hp : s31.pc = 0x1370 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · rfl
  apply OrdinarySteps.step s32 (preludeState s) _ (.base (.ADDI .x5 .x0 1)) 0
  · have hp : s32.pc = 0x1374 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · rfl
  exact OrdinarySteps.refl _

theorem prelude_pc (s : MachineState) (pc : s.pc = 0x12f4) :
    (preludeState s).pc = 0x1378 := by
  simp [preludeState,execInstrBr,pc]

theorem prelude_header (s : MachineState) (i : Fin 4) :
    (preludeState s).getMem (Signing.wordAddress 0x80000 i.val) =
      if i.val = 0 then 1 + (s.getMem 0x81000 <<< 8)
      else s.getMem (Signing.wordAddress 0x81000 i.val) := by
  fin_cases i <;>
    simp [preludeState,Signing.wordAddress,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem prelude_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80000) (h1 : a ≠ 0x80008)
    (h2 : a ≠ 0x80010) (h3 : a ≠ 0x80018) :
    (preludeState s).getMem a = s.getMem a := by
  change a ≠ 524288#64 at h0
  change a ≠ 524296#64 at h1
  change a ≠ 524304#64 at h2
  change a ≠ 524312#64 at h3
  simp [preludeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3]

theorem prelude_hash_args (s : MachineState) :
    (preludeState s).getReg .x10 = 0x80000 ∧
    (preludeState s).getReg .x11 = 512 ∧
    (preludeState s).getReg .x12 = 0x80300 ∧
    (preludeState s).getReg .x5 = 1 := by
  simp [preludeState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms prelude_steps
#print axioms prelude_header
#print axioms prelude_frame
#print axioms prelude_hash_args

end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Prelude67

end

/-! The signer's first bottom hash derives a leaf-specific private seed. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Query67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image
private abbrev prelude := GroupedBalancedSignBottomH1Prelude67.preludeState

theorem secret_query (staged : MachineState) (leaf : Nat)
    (secretKey : SecretKey)
    (level : staged.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (keyWords : ∀ i : Fin 4,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    hashInput (prelude staged) =
      Reference.packed (KeygenDomain.secretPayload
        (KeygenDomain.header 1 0 0 0 0) leaf secretKey) := by
  let ready := prelude staged
  have head : ready.getMem 0x80000 =
      KeygenDomain.header 1 0 0 0 0 := by
    have h := GroupedBalancedSignBottomH1Prelude67.prelude_header staged (0 : Fin 4)
    rw [level] at h
    simpa [ready,Signing.wordAddress,KeygenDomain.header] using h
  have treeWords : ∀ i : Fin 3,
      ready.getMem (Signing.wordAddress 0x80008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64 := by
    intro i
    fin_cases i
    · simpa [ready,Signing.wordAddress] using
        (GroupedBalancedSignBottomH1Prelude67.prelude_header staged (1 : Fin 4)).trans (address 0)
    · simpa [ready,Signing.wordAddress] using
        (GroupedBalancedSignBottomH1Prelude67.prelude_header staged (2 : Fin 4)).trans (address 1)
    · simpa [ready,Signing.wordAddress] using
        (GroupedBalancedSignBottomH1Prelude67.prelude_header staged (3 : Fin 4)).trans (address 2)
  have valueWords : ∀ i : Fin 4,
      ready.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64 := by
    intro i
    rw [GroupedBalancedSignBottomH1Prelude67.prelude_frame staged _
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact keyWords i
  have words := KeygenDomain.secret_words_of_layout ready
    (KeygenDomain.header 1 0 0 0 0) leaf secretKey
    head treeWords valueWords
  have args := GroupedBalancedSignBottomH1Prelude67.prelude_hash_args staged
  exact KeygenDomain.secret_query_eq ready _ leaf secretKey args.1 args.2.1 words

theorem secret_answer (hash : Hash) (staged : MachineState)
    (leaf : Nat) (secretKey : SecretKey)
    (level : staged.getMem 0x81000 = 0)
    (address : ∀ i : Fin 3,
      staged.getMem (Signing.wordAddress 0x81008 i.val) =
        (BitVec.ofNat 192 leaf).extractLsb' (64*i.val) 64)
    (keyWords : ∀ i : Fin 4,
      staged.getMem (Signing.wordAddress 0x80020 i.val) =
        secretKey.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 2,
      (writeHash (prelude staged) (hash (hashInput (prelude staged)))).getMem
          (Signing.wordAddress 0x80300 i.val) =
        (GroupedBottomTree.secret hash secretKey leaf).extractLsb'
          (64*i.val) 64 := by
  intro i
  have ready := GroupedBalancedSignBottomH1Prelude67.prelude_hash_args staged
  have query := secret_query staged leaf secretKey level address keyWords
  rw [Signing.hash_answer_word (prelude staged)
    (hash (hashInput (prelude staged))) ready.2.2.1
      ⟨i.val,by have := i.isLt; omega⟩]
  rw [query]
  change (hash (Reference.packed (KeygenDomain.secretPayload
      (KeygenDomain.header 1 0 0 0 0) leaf secretKey))).extractLsb'
        (64*i.val) 64 = _
  simp only [GroupedBottomTree.secret,Reference.query,
    KeygenDomain.secretPayload,KeygenDomain.header]
  let result := hash (Reference.packed
    (bytes (n := 8) (BitVec.ofNat 64
      (1 + 0 * 2 ^ 8 + 0 * 2 ^ 16 + 0 * 2 ^ 24 + 0 * 2 ^ 32)) ++
      bytes (n := 24) (BitVec.ofNat 192 leaf) ++ bytes secretKey))
  change result.extractLsb' (64*i.val) 64 =
    (result.extractLsb' 0 128).extractLsb' (64*i.val) 64
  fin_cases i <;> ext j hj <;> simp (disch := omega)

theorem secret_call (hash : Hash) (staged : MachineState)
    (pc : staged.pc = 0x12f4) :
    Trace hash image staged 34 41 1 1
      (writeHash (prelude staged) (hash (hashInput (prelude staged)))) := by
  have steps := GroupedBalancedSignBottomH1Prelude67.prelude_steps staged pc
  have readyPc := GroupedBalancedSignBottomH1Prelude67.prelude_pc staged pc
  have code : fetch image (prelude staged) = some (.base .ECALL) := by
    have raw : Keygen.instructionAt image 0x1378 = some (.base .ECALL) := by decide
    simpa only [Keygen.fetch_at,readyPc] using raw
  obtain ⟨source,bits,destination,service⟩ :=
    GroupedBalancedSignBottomH1Prelude67.prelude_hash_args staged
  have call := KeygenDomain.secret_hash_trace image hash (prelude staged)
    code service source bits destination
  simpa only [Nat.reduceAdd, image,
    GroupedBalancedSignBottomH1Prelude67.image] using
    (OrdinarySteps.trace (hash := hash) steps).trans call

#print axioms secret_query
#print axioms secret_answer
#print axioms secret_call
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomH1Query67
