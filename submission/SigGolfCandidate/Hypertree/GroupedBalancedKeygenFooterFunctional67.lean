import SigGolfCandidate.Hypertree.GroupedBalancedKeygenLeafFunctionalSafety67
import SigGolfCandidate.Hypertree.KeygenTrace

/-! The direct67 keygen footer copies the top root to the public output buffer. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenFooterFunctional67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev image := GroupedBalancedKeygenImage67.image

def outputState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 129)
  let s := execInstrBr s (.ADDI .x28 .x28 120)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.ADDI .x7 .x0 64)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.ADDI .x5 .x0 0)
  execInstrBr s (.ADDI .x10 .x0 1)

private theorem output_code :
    Keygen.instructionAt image 0x1648 = some (.base (.LUI .x28 129)) ∧
    Keygen.instructionAt image 0x164c = some (.base (.ADDI .x28 .x28 120)) ∧
    Keygen.instructionAt image 0x1650 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x1654 = some (.base (.LD .x10 .x7 0)) ∧
    Keygen.instructionAt image 0x1658 = some (.base (.LD .x11 .x7 8)) ∧
    Keygen.instructionAt image 0x165c = some (.base (.ADDI .x7 .x0 64)) ∧
    Keygen.instructionAt image 0x1660 = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1664 = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x1668 = some (.base (.ADDI .x5 .x0 0)) ∧
    Keygen.instructionAt image 0x166c = some (.base (.ADDI .x10 .x0 1)) ∧
    Keygen.instructionAt image 0x1670 = some (.base .ECALL) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem output_steps (s : MachineState) (pc : s.pc = 0x1648)
    (pointer : s.getMem 0x81078#64 = 0x82000#64) :
    OrdinarySteps image s 10 (outputState s) := by
  let s1 := execInstrBr s (.LUI .x28 129)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 120)
  let s3 := execInstrBr s2 (.LD .x7 .x28 0)
  let s4 := execInstrBr s3 (.LD .x10 .x7 0)
  let s5 := execInstrBr s4 (.LD .x11 .x7 8)
  let s6 := execInstrBr s5 (.ADDI .x7 .x0 64)
  let s7 := execInstrBr s6 (.SD .x7 .x10 0)
  let s8 := execInstrBr s7 (.SD .x7 .x11 8)
  let s9 := execInstrBr s8 (.ADDI .x5 .x0 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,_⟩ := output_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 129)) 9
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 120)) 8
  · have hp : s1.pc = 0x164c := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x7 .x28 0)) 7
  · have hp : s2.pc = 0x1650 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x10 .x7 0)) 6
  · have hp : s3.pc = 0x1654 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,pointer,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x11 .x7 8)) 5
  · have hp : s4.pc = 0x1658 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · simp [s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,pointer,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x7 .x0 64)) 4
  · have hp : s5.pc = 0x165c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x7 .x10 0)) 3
  · have hp : s6.pc = 0x1660 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x7 .x11 8)) 2
  · have hp : s7.pc = 0x1664 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,
      execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x5 .x0 0)) 1
  · have hp : s8.pc = 0x1668 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 (outputState s) _ (.base (.ADDI .x10 .x0 1)) 0
  · have hp : s9.pc = 0x166c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  exact OrdinarySteps.refl _

theorem output_pc (s : MachineState) (pc : s.pc = 0x1648) :
    (outputState s).pc = 0x1670 := by
  simp [outputState,execInstrBr,pc]

theorem output_regs (s : MachineState) :
    (outputState s).getReg .x5 = 0 ∧
    (outputState s).getReg .x10 = 1 := by
  simp [outputState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem output_mem (s : MachineState)
    (pointer : s.getMem 0x81078#64 = 0x82000#64) (a : Word) :
    (outputState s).getMem a =
      if a = 0x48 then s.getMem 0x82008 else
      if a = 0x40 then s.getMem 0x82000 else s.getMem a := by
  simp [outputState,execInstrBr,signExtend12,pointer,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem footer (hash : Hash) (s : MachineState) (pc : s.pc = 0x1648)
    (pointer : s.getMem 0x81078#64 = 0x82000#64) :
    Executes hash image s 11 ⟨.success,outputState s,11,0,0⟩ := by
  have block := output_steps s pc pointer
  have haltFetch : fetch image (outputState s) = some (.base .ECALL) := by
    have code := output_code.2.2.2.2.2.2.2.2.2.2
    simpa only [Keygen.fetch_at,output_pc s pc] using code
  have regs := output_regs s
  simpa [regs.2,Execution.charge] using
    block.then_executes (Executes.halt (hash := hash) _ haltFetch regs.1)

#print axioms output_steps
#print axioms output_mem
#print axioms footer

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenFooterFunctional67
