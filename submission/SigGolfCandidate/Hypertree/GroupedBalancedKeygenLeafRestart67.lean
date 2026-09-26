import SigGolfCandidate.Hypertree.GroupedBalancedKeygenOneLeaf67

/-! Reset the WOTS counter before the next direct67 keygen leaf. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafRestart67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192

private abbrev image := GroupedBalancedKeygenImage67.image

def restartState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  execInstrBr s (.SD .x28 .x6 0)

private theorem restart_code :
    Keygen.instructionAt image 0x1040 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1044 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1048 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x104c = some (.base (.SD .x28 .x6 0)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem restart_steps (s : MachineState) (pc : s.pc = 0x1040) :
    OrdinarySteps image s 4 (restartState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 48)
  obtain ⟨c0,c1,c2,c3⟩ := restart_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 0)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s1.pc = 0x1044 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 48)) 1
  · have hp : s2.pc = 0x1048 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 (restartState s) _ (.base (.SD .x28 .x6 0)) 0
  · have hp : s3.pc = 0x104c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,restartState,ordinaryStep,memoryArgumentsValid,
      execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem restart_pc (s : MachineState) (pc : s.pc = 0x1040) :
    (restartState s).pc = 0x1050 := by
  simp [restartState,execInstrBr,pc]

theorem restart_counter (s : MachineState) :
    (restartState s).getMem 0x81030 = 0 := by
  simp [restartState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem restart_other (s : MachineState) (a : Word) (different : a ≠ 0x81030) :
    (restartState s).getMem a = s.getMem a := by
  simp [restartState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  intro same
  exact False.elim (different same)

#print axioms restart_steps
#print axioms restart_counter

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafRestart67
