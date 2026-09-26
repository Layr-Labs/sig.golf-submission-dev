import SigGolfCandidate.Hypertree.GroupedBalancedVerifyWotsHeaderBlock67

/-! End-of-group counter update before the verifier decides whether to continue. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroup67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def countState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x58)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x58)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 30)
  s

private theorem count_code :
    Keygen.instructionAt image 0x19c4 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x19c8 = some (.base (.ADDI .x28 .x28 0x58)) ∧
    Keygen.instructionAt image 0x19cc = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x19d0 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x19d4 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x19d8 = some (.base (.ADDI .x28 .x28 0x58)) ∧
    Keygen.instructionAt image 0x19dc = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x19e0 = some (.base (.ADDI .x7 .x0 30)) := by
  unfold image GroupedBalancedVerifyImage67Fast2Byte.image
    GroupedBalancedVerifyImage67Fast2Byte.code
  decide

theorem count_steps (s : MachineState) (pc : s.pc = 0x19c4) :
    OrdinarySteps image s 8 (countState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x58)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x58)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩ := count_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x58)) 6
  · have hp : s1.pc = 0x19c8 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 5
  · have hp : s2.pc = 0x19cc := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 4
  · have hp : s3.pc = 0x19d0 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s4.pc = 0x19d4 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x58)) 2
  · have hp : s5.pc = 0x19d8 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 1
  · have hp : s6.pc = 0x19dc := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 (countState s) _ (.base (.ADDI .x7 .x0 30)) 0
  · have hp : s7.pc = 0x19e0 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem count_pc (s : MachineState) (pc : s.pc = 0x19c4) :
    (countState s).pc = 0x19e4 := by
  simp [countState,execInstrBr,pc]

theorem count_x6 (s : MachineState) :
    (countState s).getReg .x6 = s.getMem 0x81058 + 1 := by
  simp [countState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq,MachineState.getMem_setMem_ne]

theorem count_x7 (s : MachineState) :
    (countState s).getReg .x7 = 30 := by
  simp [countState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem count_mem (s : MachineState) (a : Word)
    (ne : a ≠ 0x81058) :
    (countState s).getMem a = s.getMem a := by
  simp [countState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_ne]
  intro eq
  exact (ne eq).elim

theorem count_group (s : MachineState) :
    (countState s).getMem 0x81058 = s.getMem 0x81058 + 1 := by
  simp [countState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    MachineState.getMem_setMem_eq]

#print axioms count_steps
#print axioms count_pc
#print axioms count_x6
#print axioms count_mem
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyEndGroup67
