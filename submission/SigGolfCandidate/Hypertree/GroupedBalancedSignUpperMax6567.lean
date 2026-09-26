import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Layout67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMax6567
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def maxState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x7 .x0 3)
  let s := execInstrBr s (.ADDI .x10 .x0 65)
  let s := execInstrBr s (.BEQ .x19 .x10 0x10)
  let s := execInstrBr s (.ADDI .x7 .x0 8)
  let s := execInstrBr s (.JAL .x0 0x8)
  let s := execInstrBr s (.ADD .x20 .x7 .x0)
  execInstrBr s (.ADDI .x21 .x0 0)

private theorem max_code :
    Keygen.instructionAt image 0x198c = some (.base (.ADDI .x7 .x0 3)) ∧
    Keygen.instructionAt image 0x1990 = some (.base (.ADDI .x10 .x0 65)) ∧
    Keygen.instructionAt image 0x1994 = some (.base (.BEQ .x19 .x10 0x10)) ∧
    Keygen.instructionAt image 0x19a4 = some (.base (.ADDI .x7 .x0 8)) ∧
    Keygen.instructionAt image 0x19a8 = some (.base (.JAL .x0 0x8)) ∧
    Keygen.instructionAt image 0x19b0 = some (.base (.ADD .x20 .x7 .x0)) ∧
    Keygen.instructionAt image 0x19b4 = some (.base (.ADDI .x21 .x0 0)) := by decide

theorem max_steps (s : MachineState) (pc : s.pc = 0x198c) (eq65 : s.getReg .x19 = 65) :
    OrdinarySteps image s 7 (maxState s) := by
  let s1 := execInstrBr s (.ADDI .x7 .x0 3)
  let s2 := execInstrBr s1 (.ADDI .x10 .x0 65)
  let s3 := execInstrBr s2 (.BEQ .x19 .x10 0x10)
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 8)
  let s5 := execInstrBr s4 (.JAL .x0 0x8)
  let s6 := execInstrBr s5 (.ADD .x20 .x7 .x0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6⟩ := max_code
  have eq65bv : s.getReg .x19 = (65#64) := by simpa only [show (65 : Word) = (65#64) by decide] using eq65
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x7 .x0 3)) 6
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x10 .x0 65)) 5
  · simpa [Keygen.fetch_at,s1,execInstrBr,signExtend12,signExtend13,signExtend21,pc,eq65bv,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.BEQ .x19 .x10 0x10)) 4
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,signExtend12,signExtend13,signExtend21,pc,eq65bv,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x0 8)) 3
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,signExtend12,signExtend13,signExtend21,pc,eq65bv,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.JAL .x0 0x8)) 2
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,signExtend12,signExtend13,signExtend21,pc,eq65bv,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x20 .x7 .x0)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,execInstrBr,signExtend12,signExtend13,signExtend21,pc,eq65bv,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using c5
  · rfl
  apply OrdinarySteps.step s6 (maxState s) _ (.base (.ADDI .x21 .x0 0)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,execInstrBr,signExtend12,signExtend13,signExtend21,pc,eq65bv,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using c6
  · rfl
  exact OrdinarySteps.refl _

theorem max_pc (s : MachineState) (pc : s.pc = 0x198c) (eq65 : s.getReg .x19 = 65) :
    (maxState s).pc = 0x19b8 := by
  have eq65bv : s.getReg .x19 = (65#64) := by simpa only [show (65 : Word) = (65#64) by decide] using eq65
  simp [maxState,execInstrBr,signExtend12,signExtend13,signExtend21,pc,eq65bv,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem max_data (s : MachineState) :
    (maxState s).getReg .x20 = 8 ∧
    (maxState s).getReg .x21 = 0 ∧
    (maxState s).getReg .x19 = s.getReg .x19 := by
  simp [maxState,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem max_frame (s : MachineState) (a : Word) :
    (maxState s).getMem a = s.getMem a := by
  simp [maxState,execInstrBr]

#print axioms max_steps
#print axioms max_data
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperMax6567
