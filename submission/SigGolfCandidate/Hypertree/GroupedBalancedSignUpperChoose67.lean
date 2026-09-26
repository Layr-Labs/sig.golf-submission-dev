import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopiesH367
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCopiesH467

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTailH367
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def tailState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 8)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  execInstrBr s (.JAL .x0 0x98)

private theorem tail_code :
    Keygen.instructionAt image 0x1678 = some (.base (.ADDI .x6 .x0 8)) ∧
    Keygen.instructionAt image 0x167c = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1680 = some (.base (.ADDI .x28 .x28 0xd0)) ∧
    Keygen.instructionAt image 0x1684 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1688 = some (.base (.JAL .x0 0x98)) := by decide

theorem tail_steps (s : MachineState) (pc : s.pc = 0x1678) :
    OrdinarySteps image s 5 (tailState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 8)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0xd0)
  let s4 := execInstrBr s3 (.SD .x28 .x6 0)
  obtain ⟨c0,c1,c2,c3,c4⟩ := tail_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 8)) 4
  · simpa [Keygen.fetch_at, execInstrBr, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 3
  · simpa [Keygen.fetch_at, s1, execInstrBr, pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0xd0)) 2
  · simpa [Keygen.fetch_at, s1, s2, execInstrBr, pc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.SD .x28 .x6 0)) 1
  · simpa [Keygen.fetch_at, s1, s2, s3, execInstrBr, pc] using c3
  · simp [tailState, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, s1, s2, s3, s4]
  apply OrdinarySteps.step s4 (tailState s) _ (.base (.JAL .x0 0x98)) 0
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, execInstrBr, pc] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem tail_pc (s : MachineState) (pc : s.pc = 0x1678) :
    (tailState s).pc = 0x1720 := by
  simp [tailState,execInstrBr,pc,signExtend21]

theorem tail_count (s : MachineState) :
    (tailState s).getMem 0x810d0 = 8 := by
  simp [tailState,execInstrBr,signExtend12,signExtend21,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem tail_frame (s : MachineState) (a : Word) (ha : a ≠ 0x810d0) :
    (tailState s).getMem a = s.getMem a := by
  change a ≠ 528592#64 at ha
  simp [tailState,execInstrBr,signExtend12,signExtend21,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

#print axioms tail_steps
#print axioms tail_count
#print axioms tail_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTailH367


namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTailH467
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def tailState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.ADDI .x6 .x0 16)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd0)
  execInstrBr s (.SD .x28 .x6 0)

private theorem tail_code :
    Keygen.instructionAt image 0x1710 = some (.base (.ADDI .x6 .x0 16)) ∧
    Keygen.instructionAt image 0x1714 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1718 = some (.base (.ADDI .x28 .x28 0xd0)) ∧
    Keygen.instructionAt image 0x171c = some (.base (.SD .x28 .x6 0)) := by decide

theorem tail_steps (s : MachineState) (pc : s.pc = 0x1710) :
    OrdinarySteps image s 4 (tailState s) := by
  let s1 := execInstrBr s (.ADDI .x6 .x0 16)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0xd0)
  obtain ⟨c0,c1,c2,c3⟩ := tail_code
  apply OrdinarySteps.step s s1 _ (.base (.ADDI .x6 .x0 16)) 3
  · simpa [Keygen.fetch_at, execInstrBr, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 2
  · simpa [Keygen.fetch_at, s1, execInstrBr, pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0xd0)) 1
  · simpa [Keygen.fetch_at, s1, s2, execInstrBr, pc] using c2
  · rfl
  apply OrdinarySteps.step s3 (tailState s) _ (.base (.SD .x28 .x6 0)) 0
  · simpa [Keygen.fetch_at, s1, s2, s3, execInstrBr, pc] using c3
  · simp [tailState, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, s1, s2, s3]
  exact OrdinarySteps.refl _

theorem tail_pc (s : MachineState) (pc : s.pc = 0x1710) :
    (tailState s).pc = 0x1720 := by
  simp [tailState,execInstrBr,pc,signExtend21]

theorem tail_count (s : MachineState) :
    (tailState s).getMem 0x810d0 = 16 := by
  simp [tailState,execInstrBr,signExtend12,signExtend21,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem tail_frame (s : MachineState) (a : Word) (ha : a ≠ 0x810d0) :
    (tailState s).getMem a = s.getMem a := by
  change a ≠ 528592#64 at ha
  simp [tailState,execInstrBr,signExtend12,signExtend21,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

#print axioms tail_steps
#print axioms tail_count
#print axioms tail_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperTailH467


namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChoose67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def chooseState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x7 .x0 4)
  execInstrBr s (.BEQ .x6 .x7 0x9c)

private theorem choose_code :
    Keygen.instructionAt image 0x15e0 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x15e4 = some (.base (.ADDI .x28 .x28 0x60)) ∧
    Keygen.instructionAt image 0x15e8 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x15ec = some (.base (.ADDI .x7 .x0 4)) ∧
    Keygen.instructionAt image 0x15f0 = some (.base (.BEQ .x6 .x7 0x9c)) := by
  decide

theorem choose_steps (s : MachineState) (pc : s.pc = 0x15e0) :
    OrdinarySteps image s 5 (chooseState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x60)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x7 .x0 4)
  obtain ⟨c0,c1,c2,c3,c4⟩ := choose_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 4
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x60)) 3
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 2
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      accessValid,rangeValid,MEMORY_BYTES,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x0 4)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 (chooseState s) _ (.base (.BEQ .x6 .x7 0x9c)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  exact OrdinarySteps.refl _

theorem choose_pc (s : MachineState) (pc : s.pc = 0x15e0) :
    (chooseState s).pc =
      if s.getMem 0x81060 = (4 : Word) then 0x168c else 0x15f4 := by
  simp [chooseState,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem choose_frame (s : MachineState) (a : Word) :
    (chooseState s).getMem a = s.getMem a := by
  simp [chooseState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

#print axioms choose_steps
#print axioms choose_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperChoose67
