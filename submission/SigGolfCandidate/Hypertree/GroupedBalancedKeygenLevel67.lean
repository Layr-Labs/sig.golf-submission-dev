import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneNode67
/-! Swap tree buffers and halve the parent count after one keygen H4 level. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLevel67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
private abbrev image := GroupedBalancedKeygenImage67.image
def levelState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 120)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 128)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 120)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 128)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 112)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SRLI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 112)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 80)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 80)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 4)
  execInstrBr s (.BNE .x6 .x7 7724)
private theorem level_code :
    Keygen.instructionAt image 0x15bc = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x15c0 = some (.base (.ADDI .x28 .x28 120)) ∧
    Keygen.instructionAt image 0x15c4 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x15c8 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x15cc = some (.base (.ADDI .x28 .x28 128)) ∧
    Keygen.instructionAt image 0x15d0 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x15d4 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x15d8 = some (.base (.ADDI .x28 .x28 120)) ∧
    Keygen.instructionAt image 0x15dc = some (.base (.SD .x28 .x7 0)) ∧
    Keygen.instructionAt image 0x15e0 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x15e4 = some (.base (.ADDI .x28 .x28 128)) ∧
    Keygen.instructionAt image 0x15e8 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x15ec = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x15f0 = some (.base (.ADDI .x28 .x28 112)) ∧
    Keygen.instructionAt image 0x15f4 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x15f8 = some (.base (.SRLI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x15fc = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1600 = some (.base (.ADDI .x28 .x28 112)) ∧
    Keygen.instructionAt image 0x1604 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1608 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x160c = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1610 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1614 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1618 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x161c = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1620 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1624 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1628 = some (.base (.ADDI .x28 .x28 80)) ∧
    Keygen.instructionAt image 0x162c = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1630 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1634 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x1638 = some (.base (.ADDI .x28 .x28 80)) ∧
    Keygen.instructionAt image 0x163c = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1640 = some (.base (.ADDI .x7 .x0 4)) ∧
    Keygen.instructionAt image 0x1644 = some (.base (.BNE .x6 .x7 7724)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide
theorem level_steps (s : MachineState) (pc : s.pc = 0x15bc) :
    OrdinarySteps image s 35 (levelState s) := by
  let s1 := execInstrBr s (.LUI .x28 129)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 120)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 129)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 128)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.LUI .x28 129)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 120)
  let s9 := execInstrBr s8 (.SD .x28 .x7 0)
  let s10 := execInstrBr s9 (.LUI .x28 129)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 128)
  let s12 := execInstrBr s11 (.SD .x28 .x6 0)
  let s13 := execInstrBr s12 (.LUI .x28 129)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 112)
  let s15 := execInstrBr s14 (.LD .x6 .x28 0)
  let s16 := execInstrBr s15 (.SRLI .x6 .x6 1)
  let s17 := execInstrBr s16 (.LUI .x28 129)
  let s18 := execInstrBr s17 (.ADDI .x28 .x28 112)
  let s19 := execInstrBr s18 (.SD .x28 .x6 0)
  let s20 := execInstrBr s19 (.LUI .x28 129)
  let s21 := execInstrBr s20 (.ADDI .x28 .x28 0)
  let s22 := execInstrBr s21 (.LD .x6 .x28 0)
  let s23 := execInstrBr s22 (.ADDI .x6 .x6 1)
  let s24 := execInstrBr s23 (.LUI .x28 129)
  let s25 := execInstrBr s24 (.ADDI .x28 .x28 0)
  let s26 := execInstrBr s25 (.SD .x28 .x6 0)
  let s27 := execInstrBr s26 (.LUI .x28 129)
  let s28 := execInstrBr s27 (.ADDI .x28 .x28 80)
  let s29 := execInstrBr s28 (.LD .x6 .x28 0)
  let s30 := execInstrBr s29 (.ADDI .x6 .x6 1)
  let s31 := execInstrBr s30 (.LUI .x28 129)
  let s32 := execInstrBr s31 (.ADDI .x28 .x28 80)
  let s33 := execInstrBr s32 (.SD .x28 .x6 0)
  let s34 := execInstrBr s33 (.ADDI .x7 .x0 4)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34⟩ := level_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 129)) 34
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 120)) 33
  · have hp : s1.pc = 0x15c0 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 32
  · have hp : s2.pc = 0x15c4 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 129)) 31
  · have hp : s3.pc = 0x15c8 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 128)) 30
  · have hp : s4.pc = 0x15cc := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 29
  · have hp : s5.pc = 0x15d0 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 129)) 28
  · have hp : s6.pc = 0x15d4 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 120)) 27
  · have hp : s7.pc = 0x15d8 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x7 0)) 26
  · have hp : s8.pc = 0x15dc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 129)) 25
  · have hp : s9.pc = 0x15e0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 128)) 24
  · have hp : s10.pc = 0x15e4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x6 0)) 23
  · have hp : s11.pc = 0x15e8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 129)) 22
  · have hp : s12.pc = 0x15ec := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 112)) 21
  · have hp : s13.pc = 0x15f0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LD .x6 .x28 0)) 20
  · have hp : s14.pc = 0x15f4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.SRLI .x6 .x6 1)) 19
  · have hp : s15.pc = 0x15f8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 129)) 18
  · have hp : s16.pc = 0x15fc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.ADDI .x28 .x28 112)) 17
  · have hp : s17.pc = 0x1600 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.SD .x28 .x6 0)) 16
  · have hp : s18.pc = 0x1604 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s19 s20 _ (.base (.LUI .x28 129)) 15
  · have hp : s19.pc = 0x1608 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.ADDI .x28 .x28 0)) 14
  · have hp : s20.pc = 0x160c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.LD .x6 .x28 0)) 13
  · have hp : s21.pc = 0x1610 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s22 s23 _ (.base (.ADDI .x6 .x6 1)) 12
  · have hp : s22.pc = 0x1614 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.LUI .x28 129)) 11
  · have hp : s23.pc = 0x1618 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.ADDI .x28 .x28 0)) 10
  · have hp : s24.pc = 0x161c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.SD .x28 .x6 0)) 9
  · have hp : s25.pc = 0x1620 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s26 s27 _ (.base (.LUI .x28 129)) 8
  · have hp : s26.pc = 0x1624 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · rfl
  apply OrdinarySteps.step s27 s28 _ (.base (.ADDI .x28 .x28 80)) 7
  · have hp : s27.pc = 0x1628 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.LD .x6 .x28 0)) 6
  · have hp : s28.pc = 0x162c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s29 s30 _ (.base (.ADDI .x6 .x6 1)) 5
  · have hp : s29.pc = 0x1630 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · rfl
  apply OrdinarySteps.step s30 s31 _ (.base (.LUI .x28 129)) 4
  · have hp : s30.pc = 0x1634 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.ADDI .x28 .x28 80)) 3
  · have hp : s31.pc = 0x1638 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · rfl
  apply OrdinarySteps.step s32 s33 _ (.base (.SD .x28 .x6 0)) 2
  · have hp : s32.pc = 0x163c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,levelState,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s33 s34 _ (.base (.ADDI .x7 .x0 4)) 1
  · have hp : s33.pc = 0x1640 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c33
  · rfl
  apply OrdinarySteps.step s34 (levelState s) _ (.base (.BNE .x6 .x7 7724)) 0
  · have hp : s34.pc = 0x1644 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c34
  · rfl
  exact OrdinarySteps.refl _

theorem level_pc (s : MachineState) (pc : s.pc = 0x15bc) :
    (levelState s).pc =
      if s.getMem 0x81050#64 + 1 = 4 then 0x1648 else 0x1470 := by
  simp [levelState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]

theorem level_controls (s : MachineState) :
    (levelState s).getMem 0x81078#64 = s.getMem 0x81080#64 ∧
    (levelState s).getMem 0x81080#64 = s.getMem 0x81078#64 ∧
    (levelState s).getMem 0x81070#64 = s.getMem 0x81070#64 >>> 1 ∧
    (levelState s).getMem 0x81000#64 = s.getMem 0x81000#64 + 1 ∧
    (levelState s).getMem 0x81050#64 = s.getMem 0x81050#64 + 1 ∧
    (levelState s).getMem 0x81040#64 = s.getMem 0x81040#64 := by
  simp [levelState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms level_steps
#print axioms level_controls
end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLevel67
