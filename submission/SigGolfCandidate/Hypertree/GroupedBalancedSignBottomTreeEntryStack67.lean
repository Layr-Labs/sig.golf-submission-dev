import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntry67

/-! The bottom parent subroutine accepts either embedded-data stack base. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntryStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image

theorem entry_steps_stack (s : MachineState)
    (pc : s.pc = 0x1da8)
    (sp : s.getReg .x2 = 0xfff7e0 ∨ s.getReg .x2 = 0xfff700) :
    OrdinarySteps image s 6
      (GroupedBalancedSignBottomTreeEntry67.entryState s) := by
  let s1 := execInstrBr s (.ADDI .x2 .x2 0xff0)
  let s2 := execInstrBr s1 (.SD .x2 .x1 0)
  let s3 := execInstrBr s2 (.ADDI .x6 .x0 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x50)
  have c0 : Keygen.instructionAt image 0x1da8 =
      some (.base (.ADDI .x2 .x2 0xff0)) := by decide
  have c1 : Keygen.instructionAt image 0x1dac =
      some (.base (.SD .x2 .x1 0)) := by decide
  have c2 : Keygen.instructionAt image 0x1db0 =
      some (.base (.ADDI .x6 .x0 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1db4 =
      some (.base (.LUI .x28 0x81)) := by decide
  have c4 : Keygen.instructionAt image 0x1db8 =
      some (.base (.ADDI .x28 .x28 0x50)) := by decide
  have c5 : Keygen.instructionAt image 0x1dbc =
      some (.base (.SD .x28 .x6 0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x2 .x2 0xff0)) 5
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x2 .x1 0)) 4
  · have hp : s1.pc = 0x1dac := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rcases sp with h|h
    · simp [s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,
        h,signExtend12,accessValid,rangeValid,MEMORY_BYTES,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    · simp [s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,
        h,signExtend12,accessValid,rangeValid,MEMORY_BYTES,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s2.pc = 0x1db0 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s3.pc = 0x1db4 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x50)) 1
  · have hp : s4.pc = 0x1db8 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 (GroupedBalancedSignBottomTreeEntry67.entryState s) _
    (.base (.SD .x28 .x6 0)) 0
  · have hp : s5.pc = 0x1dbc := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [GroupedBalancedSignBottomTreeEntry67.entryState,s1,s2,s3,s4,s5,
      ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem entry_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeEntry67.entryState s).getReg .x2 =
      s.getReg .x2 + 18446744073709551600#64 := by
  simp [GroupedBalancedSignBottomTreeEntry67.entryState,execInstrBr,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

#print axioms entry_steps_stack
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntryStack67
