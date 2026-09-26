import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLimit67

/-! The fixed verifier header block after the byte-table decoder returns. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderBlock67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def headerState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 56)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x10 .x0 2)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 8)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 24)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 56)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.SLLI .x11 .x11 32)
  let s := execInstrBr s (.ADD .x10 .x10 .x11)
  let s := execInstrBr s (.LUI .x28 0x90)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x10 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x90)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x90)
  let s := execInstrBr s (.ADDI .x28 .x28 16)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.LD .x11 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x90)
  let s := execInstrBr s (.ADDI .x28 .x28 24)
  let s := execInstrBr s (.SD .x28 .x11 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 72)
  execInstrBr s (.LD .x22 .x28 0)

private theorem code :
    Keygen.instructionAt image 0x1518 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x151c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1520 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x1524 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1528 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x152c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1530 = some (.base (.ADDI .x28 .x28 56)) ∧
    Keygen.instructionAt image 0x1534 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1538 = some (.base (.ADDI .x10 .x0 2)) ∧
    Keygen.instructionAt image 0x153c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1540 = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1544 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1548 = some (.base (.SLLI .x11 .x11 8)) ∧
    Keygen.instructionAt image 0x154c = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 0x1550 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1554 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x1558 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x155c = some (.base (.SLLI .x11 .x11 24)) ∧
    Keygen.instructionAt image 0x1560 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 0x1564 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1568 = some (.base (.ADDI .x28 .x28 56)) ∧
    Keygen.instructionAt image 0x156c = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1570 = some (.base (.SLLI .x11 .x11 32)) ∧
    Keygen.instructionAt image 0x1574 = some (.base (.ADD .x10 .x10 .x11)) ∧
    Keygen.instructionAt image 0x1578 = some (.base (.LUI .x28 0x90)) ∧
    Keygen.instructionAt image 0x157c = some (.base (.ADDI .x28 .x28 0)) ∧
    Keygen.instructionAt image 0x1580 = some (.base (.SD .x28 .x10 0)) ∧
    Keygen.instructionAt image 0x1584 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1588 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x158c = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x1590 = some (.base (.LUI .x28 0x90)) ∧
    Keygen.instructionAt image 0x1594 = some (.base (.ADDI .x28 .x28 8)) ∧
    Keygen.instructionAt image 0x1598 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x159c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x15a0 = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x15a4 = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x15a8 = some (.base (.LUI .x28 0x90)) ∧
    Keygen.instructionAt image 0x15ac = some (.base (.ADDI .x28 .x28 16)) ∧
    Keygen.instructionAt image 0x15b0 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x15b4 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x15b8 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x15bc = some (.base (.LD .x11 .x28 0)) ∧
    Keygen.instructionAt image 0x15c0 = some (.base (.LUI .x28 0x90)) ∧
    Keygen.instructionAt image 0x15c4 = some (.base (.ADDI .x28 .x28 24)) ∧
    Keygen.instructionAt image 0x15c8 = some (.base (.SD .x28 .x11 0)) ∧
    Keygen.instructionAt image 0x15cc = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x15d0 = some (.base (.ADDI .x28 .x28 72)) ∧
    Keygen.instructionAt image 0x15d4 = some (.base (.LD .x22 .x28 0)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  apply And.intro
  · decide
  decide

theorem header_steps (s : MachineState) (pc : s.pc = 0x1518) :
    OrdinarySteps image s 48 (headerState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 48)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x0 0)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 56)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.ADDI .x10 .x0 2)
  let s10 := execInstrBr s9 (.LUI .x28 0x81)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 0)
  let s12 := execInstrBr s11 (.LD .x11 .x28 0)
  let s13 := execInstrBr s12 (.SLLI .x11 .x11 8)
  let s14 := execInstrBr s13 (.ADD .x10 .x10 .x11)
  let s15 := execInstrBr s14 (.LUI .x28 0x81)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 48)
  let s17 := execInstrBr s16 (.LD .x11 .x28 0)
  let s18 := execInstrBr s17 (.SLLI .x11 .x11 24)
  let s19 := execInstrBr s18 (.ADD .x10 .x10 .x11)
  let s20 := execInstrBr s19 (.LUI .x28 0x81)
  let s21 := execInstrBr s20 (.ADDI .x28 .x28 56)
  let s22 := execInstrBr s21 (.LD .x11 .x28 0)
  let s23 := execInstrBr s22 (.SLLI .x11 .x11 32)
  let s24 := execInstrBr s23 (.ADD .x10 .x10 .x11)
  let s25 := execInstrBr s24 (.LUI .x28 0x90)
  let s26 := execInstrBr s25 (.ADDI .x28 .x28 0)
  let s27 := execInstrBr s26 (.SD .x28 .x10 0)
  let s28 := execInstrBr s27 (.LUI .x28 0x81)
  let s29 := execInstrBr s28 (.ADDI .x28 .x28 8)
  let s30 := execInstrBr s29 (.LD .x11 .x28 0)
  let s31 := execInstrBr s30 (.LUI .x28 0x90)
  let s32 := execInstrBr s31 (.ADDI .x28 .x28 8)
  let s33 := execInstrBr s32 (.SD .x28 .x11 0)
  let s34 := execInstrBr s33 (.LUI .x28 0x81)
  let s35 := execInstrBr s34 (.ADDI .x28 .x28 16)
  let s36 := execInstrBr s35 (.LD .x11 .x28 0)
  let s37 := execInstrBr s36 (.LUI .x28 0x90)
  let s38 := execInstrBr s37 (.ADDI .x28 .x28 16)
  let s39 := execInstrBr s38 (.SD .x28 .x11 0)
  let s40 := execInstrBr s39 (.LUI .x28 0x81)
  let s41 := execInstrBr s40 (.ADDI .x28 .x28 24)
  let s42 := execInstrBr s41 (.LD .x11 .x28 0)
  let s43 := execInstrBr s42 (.LUI .x28 0x90)
  let s44 := execInstrBr s43 (.ADDI .x28 .x28 24)
  let s45 := execInstrBr s44 (.SD .x28 .x11 0)
  let s46 := execInstrBr s45 (.LUI .x28 0x81)
  let s47 := execInstrBr s46 (.ADDI .x28 .x28 72)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47⟩ := code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 47
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 46
  · have hp : s1.pc = 0x151c := by
      simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 48)) 45
  · have hp : s2.pc = 0x1520 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 44
  · have hp : s3.pc = 0x1524 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s4,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x0 0)) 43
  · have hp : s4.pc = 0x1528 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 42
  · have hp : s5.pc = 0x152c := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 56)) 41
  · have hp : s6.pc = 0x1530 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 40
  · have hp : s7.pc = 0x1534 := by
      simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s8,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x10 .x0 2)) 39
  · have hp : s8.pc = 0x1538 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 38
  · have hp : s9.pc = 0x153c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 0)) 37
  · have hp : s10.pc = 0x1540 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x11 .x28 0)) 36
  · have hp : s11.pc = 0x1544 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [s12,s9,s10,s11,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.SLLI .x11 .x11 8)) 35
  · have hp : s12.pc = 0x1548 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADD .x10 .x10 .x11)) 34
  · have hp : s13.pc = 0x154c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 0x81)) 33
  · have hp : s14.pc = 0x1550 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 48)) 32
  · have hp : s15.pc = 0x1554 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LD .x11 .x28 0)) 31
  · have hp : s16.pc = 0x1558 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [s17,s14,s15,s16,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s17 s18 _ (.base (.SLLI .x11 .x11 24)) 30
  · have hp : s17.pc = 0x155c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADD .x10 .x10 .x11)) 29
  · have hp : s18.pc = 0x1560 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.LUI .x28 0x81)) 28
  · have hp : s19.pc = 0x1564 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c19
  · rfl
  apply OrdinarySteps.step s20 s21 _ (.base (.ADDI .x28 .x28 56)) 27
  · have hp : s20.pc = 0x1568 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  apply OrdinarySteps.step s21 s22 _ (.base (.LD .x11 .x28 0)) 26
  · have hp : s21.pc = 0x156c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c21
  · simp [s22,s19,s20,s21,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s22 s23 _ (.base (.SLLI .x11 .x11 32)) 25
  · have hp : s22.pc = 0x1570 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c22
  · rfl
  apply OrdinarySteps.step s23 s24 _ (.base (.ADD .x10 .x10 .x11)) 24
  · have hp : s23.pc = 0x1574 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c23
  · rfl
  apply OrdinarySteps.step s24 s25 _ (.base (.LUI .x28 0x90)) 23
  · have hp : s24.pc = 0x1578 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c24
  · rfl
  apply OrdinarySteps.step s25 s26 _ (.base (.ADDI .x28 .x28 0)) 22
  · have hp : s25.pc = 0x157c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c25
  · rfl
  apply OrdinarySteps.step s26 s27 _ (.base (.SD .x28 .x10 0)) 21
  · have hp : s26.pc = 0x1580 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c26
  · simp [s27,s24,s25,s26,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s27 s28 _ (.base (.LUI .x28 0x81)) 20
  · have hp : s27.pc = 0x1584 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c27
  · rfl
  apply OrdinarySteps.step s28 s29 _ (.base (.ADDI .x28 .x28 8)) 19
  · have hp : s28.pc = 0x1588 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c28
  · rfl
  apply OrdinarySteps.step s29 s30 _ (.base (.LD .x11 .x28 0)) 18
  · have hp : s29.pc = 0x158c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c29
  · simp [s30,s27,s28,s29,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s30 s31 _ (.base (.LUI .x28 0x90)) 17
  · have hp : s30.pc = 0x1590 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c30
  · rfl
  apply OrdinarySteps.step s31 s32 _ (.base (.ADDI .x28 .x28 8)) 16
  · have hp : s31.pc = 0x1594 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c31
  · rfl
  apply OrdinarySteps.step s32 s33 _ (.base (.SD .x28 .x11 0)) 15
  · have hp : s32.pc = 0x1598 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c32
  · simp [s33,s30,s31,s32,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s33 s34 _ (.base (.LUI .x28 0x81)) 14
  · have hp : s33.pc = 0x159c := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c33
  · rfl
  apply OrdinarySteps.step s34 s35 _ (.base (.ADDI .x28 .x28 16)) 13
  · have hp : s34.pc = 0x15a0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c34
  · rfl
  apply OrdinarySteps.step s35 s36 _ (.base (.LD .x11 .x28 0)) 12
  · have hp : s35.pc = 0x15a4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c35
  · simp [s36,s33,s34,s35,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s36 s37 _ (.base (.LUI .x28 0x90)) 11
  · have hp : s36.pc = 0x15a8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c36
  · rfl
  apply OrdinarySteps.step s37 s38 _ (.base (.ADDI .x28 .x28 16)) 10
  · have hp : s37.pc = 0x15ac := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c37
  · rfl
  apply OrdinarySteps.step s38 s39 _ (.base (.SD .x28 .x11 0)) 9
  · have hp : s38.pc = 0x15b0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c38
  · simp [s39,s36,s37,s38,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s39 s40 _ (.base (.LUI .x28 0x81)) 8
  · have hp : s39.pc = 0x15b4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c39
  · rfl
  apply OrdinarySteps.step s40 s41 _ (.base (.ADDI .x28 .x28 24)) 7
  · have hp : s40.pc = 0x15b8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c40
  · rfl
  apply OrdinarySteps.step s41 s42 _ (.base (.LD .x11 .x28 0)) 6
  · have hp : s41.pc = 0x15bc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c41
  · simp [s42,s39,s40,s41,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s42 s43 _ (.base (.LUI .x28 0x90)) 5
  · have hp : s42.pc = 0x15c0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c42
  · rfl
  apply OrdinarySteps.step s43 s44 _ (.base (.ADDI .x28 .x28 24)) 4
  · have hp : s43.pc = 0x15c4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c43
  · rfl
  apply OrdinarySteps.step s44 s45 _ (.base (.SD .x28 .x11 0)) 3
  · have hp : s44.pc = 0x15c8 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c44
  · simp [s45,s42,s43,s44,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s45 s46 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s45.pc = 0x15cc := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c45
  · rfl
  apply OrdinarySteps.step s46 s47 _ (.base (.ADDI .x28 .x28 72)) 1
  · have hp : s46.pc = 0x15d0 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c46
  · rfl
  apply OrdinarySteps.step s47 (headerState s) _ (.base (.LD .x22 .x28 0)) 0
  · have hp : s47.pc = 0x15d4 := by
      simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46,s47,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c47
  · change ordinaryStep s47 (.base (.LD .x22 .x28 0)) =
        some (execInstrBr s47 (.LD .x22 .x28 0))
    simp [s45,s46,s47,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

#print axioms header_steps
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderBlock67
