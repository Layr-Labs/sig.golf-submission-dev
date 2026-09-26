import SigGolfCandidate.Hypertree.GroupedBalancedKeygenPrefix67

/-! The initialized top-tree counter selects the left first leaf. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedKeygenBranch67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedKeygenImage67.image

def branchState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 48)
  let s := execInstrBr s (.LD .x19 .x28 0)
  let s := execInstrBr s (.ANDI .x6 .x19 1)
  execInstrBr s (.BEQ .x6 .x0 8)

private theorem branch_code :
    Keygen.instructionAt image 0x1050 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1054 = some (.base (.ADDI .x28 .x28 48)) ∧
    Keygen.instructionAt image 0x1058 = some (.base (.LD .x19 .x28 0)) ∧
    Keygen.instructionAt image 0x105c = some (.base (.ANDI .x6 .x19 1)) ∧
    Keygen.instructionAt image 0x1060 = some (.base (.BEQ .x6 .x0 8)) := by
  unfold image GroupedBalancedKeygenImage67.image
  decide

theorem branch_steps (s : MachineState) (pc : s.pc = 0x1050) :
    OrdinarySteps image s 5 (branchState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 48)
  let s3 := execInstrBr s2 (.LD .x19 .x28 0)
  let s4 := execInstrBr s3 (.ANDI .x6 .x19 1)
  obtain ⟨c0,c1,c2,c3,c4⟩ := branch_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 48)) 3
  · have hp : s1.pc = 0x1054 := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x19 .x28 0)) 2
  · have hp : s2.pc = 0x1058 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ANDI .x6 .x19 1)) 1
  · have hp : s3.pc = 0x105c := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 (branchState s) _ (.base (.BEQ .x6 .x0 8)) 0
  · have hp : s4.pc = 0x1060 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem branch_pc (s : MachineState) (pc : s.pc = 0x1050)
    (zero : s.getMem 0x81030 = 0) :
    (branchState s).pc = 0x1068 := by
  simp [branchState,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  have hzero : s.getMem (528432#64) = 0#64 := zero
  rw [hzero]
  decide

theorem branch_mem (s : MachineState) (a : Word) :
    (branchState s).getMem a = s.getMem a := by
  simp [branchState,execInstrBr]

theorem initial_branch_trace (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1000) :
    Trace hash image s 25 25 0 0
      (branchState (GroupedBalancedKeygenPrefix67.entryState s)) ∧
    (branchState (GroupedBalancedKeygenPrefix67.entryState s)).pc = 0x1068 := by
  have first := GroupedBalancedKeygenPrefix67.entry_trace hash s pc
  have second := (branch_steps (GroupedBalancedKeygenPrefix67.entryState s)
    (GroupedBalancedKeygenPrefix67.entry_pc s pc)).trace (hash := hash)
  constructor
  · simpa only [image,GroupedBalancedKeygenPrefix67.image,
      Nat.reduceAdd] using first.trans second
  · exact branch_pc _ (GroupedBalancedKeygenPrefix67.entry_pc s pc)
      (GroupedBalancedKeygenPrefix67.entry_words s).2.2.2.2

#print axioms initial_branch_trace

end SigGolfCandidate.Hypertree.GroupedBalancedKeygenBranch67
