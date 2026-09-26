import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67
import SigGolfCandidate.Hypertree.KeygenBlocks

/-! The signer's bottom-tree parent builder enters with a saved return
address and resets its level counter. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntry67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev image := GroupedBalancedSignImage67.image

def entryState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x2 .x2 0xff0)
  let s := execInstrBr s (.SD .x2 .x1 0)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x50)
  execInstrBr s (.SD .x28 .x6 0)

private theorem entry_code :
    Keygen.instructionAt image 0x1da8 =
      some (.base (.ADDI .x2 .x2 0xff0)) ∧
    Keygen.instructionAt image 0x1dac =
      some (.base (.SD .x2 .x1 0)) ∧
    Keygen.instructionAt image 0x1db0 =
      some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1db4 =
      some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1db8 =
      some (.base (.ADDI .x28 .x28 0x50)) ∧
    Keygen.instructionAt image 0x1dbc =
      some (.base (.SD .x28 .x6 0)) := by
  decide

theorem entry_steps (s : MachineState)
    (pc : s.pc = 0x1da8) (sp : s.getReg .x2 = 0x1000000) :
    OrdinarySteps image s 6 (entryState s) := by
  let s1 := execInstrBr s (.ADDI .x2 .x2 0xff0)
  let s2 := execInstrBr s1 (.SD .x2 .x1 0)
  let s3 := execInstrBr s2 (.ADDI .x6 .x0 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x50)
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := entry_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x2 .x2 0xff0)) 5
  · simpa only [Keygen.fetch_at, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x2 .x1 0)) 4
  · have hp : s1.pc = 0x1dac := by
      simp [s1, execInstrBr, pc]
    simpa only [Keygen.fetch_at, hp] using c1
  · simp [s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,
      sp,signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x6 .x0 0)) 3
  · have hp : s2.pc = 0x1db0 := by
      simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s3.pc = 0x1db4 := by
      simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x50)) 1
  · have hp : s4.pc = 0x1db8 := by
      simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 (entryState s) _
    (.base (.SD .x28 .x6 0)) 0
  · have hp : s5.pc = 0x1dbc := by
      simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [entryState,s1,s2,s3,s4,s5,ordinaryStep,
      memoryArgumentsValid,execInstrBr,signExtend12,
      accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _

theorem entry_pc (s : MachineState) (pc : s.pc = 0x1da8) :
    (entryState s).pc = 0x1dc0 := by
  simp [entryState,execInstrBr,pc]

theorem entry_level (s : MachineState) :
    (entryState s).getMem 0x81050 = 0 := by
  simp [entryState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms entry_steps
#print axioms entry_level

end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntry67
