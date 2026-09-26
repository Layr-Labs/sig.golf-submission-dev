import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMaxCommon67

/-! Configure the paired H1 query's source, bit count, output, and service. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Ready67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def readyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x10 0x80)
  let s := execInstrBr s (.ADDI .x10 .x10 0)
  let s := execInstrBr s (.ADDI .x11 .x0 384)
  let s := execInstrBr s (.LUI .x12 0x80)
  let s := execInstrBr s (.ADDI .x12 .x12 0x20)
  execInstrBr s (.ADDI .x5 .x0 1)

private theorem ready_code :
    Keygen.instructionAt image 0x19b8 = some (.base (.LUI .x10 0x80)) ∧
    Keygen.instructionAt image 0x19bc = some (.base (.ADDI .x10 .x10 0)) ∧
    Keygen.instructionAt image 0x19c0 = some (.base (.ADDI .x11 .x0 384)) ∧
    Keygen.instructionAt image 0x19c4 = some (.base (.LUI .x12 0x80)) ∧
    Keygen.instructionAt image 0x19c8 = some (.base (.ADDI .x12 .x12 0x20)) ∧
    Keygen.instructionAt image 0x19cc = some (.base (.ADDI .x5 .x0 1)) := by decide

theorem ready_steps (s : MachineState) (pc : s.pc = 0x19b8) :
    OrdinarySteps image s 6 (readyState s) := by
  let s1 := execInstrBr s (.LUI .x10 0x80)
  let s2 := execInstrBr s1 (.ADDI .x10 .x10 0)
  let s3 := execInstrBr s2 (.ADDI .x11 .x0 384)
  let s4 := execInstrBr s3 (.LUI .x12 0x80)
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 0x20)
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := ready_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x10 0x80)) 5
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x10 0)) 4
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x11 .x0 384)) 3
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x12 0x80)) 2
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x12 .x12 0x20)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  apply OrdinarySteps.step s5 (readyState s) _ (.base (.ADDI .x5 .x0 1)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,execInstrBr,pc] using c5
  · rfl
  exact OrdinarySteps.refl _

theorem ready_pc (s : MachineState) (pc : s.pc = 0x19b8) :
    (readyState s).pc = 0x19d0 := by
  simp [readyState,execInstrBr,pc]

theorem ready_regs (s : MachineState) :
    (readyState s).getReg .x10 = 0x80000 ∧
    (readyState s).getReg .x11 = 384 ∧
    (readyState s).getReg .x12 = 0x80020 ∧
    (readyState s).getReg .x5 = 1 := by
  simp [readyState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem ready_frame (s : MachineState) (a : Word) :
    (readyState s).getMem a = s.getMem a := by
  simp [readyState,execInstrBr]

#print axioms ready_steps
#print axioms ready_pc
#print axioms ready_regs
#print axioms ready_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Ready67
