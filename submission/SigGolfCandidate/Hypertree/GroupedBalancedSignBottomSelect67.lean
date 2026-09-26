import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSeedCopies67

/-! Route the first H1 seed to the witness iff its leaf is selected. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelect67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def selectState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe8)
  let s := execInstrBr s (.LD .x7 .x28 0)
  execInstrBr s (.BNE .x6 .x7 0x30)

private theorem select_code :
    Keygen.instructionAt image 0x137c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1380 = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x1384 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1388 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x138c = some (.base (.ADDI .x28 .x28 0xe8)) ∧
    Keygen.instructionAt image 0x1390 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x1394 = some (.base (.BNE .x6 .x7 0x30)) := by
  decide

theorem select_steps (s : MachineState) (pc : s.pc = 0x137c) :
    OrdinarySteps image s 7 (selectState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xe0)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0xe8)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6⟩ := select_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 6
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xe0)) 5
  · have hp : s1.pc = 0x1380 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
  · have hp : s2.pc = 0x1384 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,selectState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s3.pc = 0x1388 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0xe8)) 2
  · have hp : s4.pc = 0x138c := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 1
  · have hp : s5.pc = 0x1390 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [s1,s2,s3,s4,s5,s6,selectState,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 (selectState s) _ (.base (.BNE .x6 .x7 0x30)) 0
  · have hp : s6.pc = 0x1394 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  exact OrdinarySteps.refl _

theorem select_pc (s : MachineState) (pc : s.pc = 0x137c) :
    (selectState s).pc =
      if s.getMem 0x810e0 = s.getMem 0x810e8 then 0x1398 else 0x13c4 := by
  simp [selectState,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem select_frame (s : MachineState) (a : Word) :
    (selectState s).getMem a = s.getMem a := by
  simp [selectState,execInstrBr]

#print axioms select_steps
#print axioms select_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelect67
