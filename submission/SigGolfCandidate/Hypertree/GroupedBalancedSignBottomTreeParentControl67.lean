import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeHashStoreCopy67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAdvance67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentControl67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
def advanceState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd0)
  execInstrBr s (.LD .x7 .x28 0)
theorem advance_steps (s : MachineState) (pc : s.pc = 0x2010) :
    OrdinarySteps image s 17 (advanceState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 8)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x81)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0xd8)
  let s10 := execInstrBr s9 (.LD .x6 .x28 0)
  let s11 := execInstrBr s10 (.ADDI .x6 .x6 1)
  let s12 := execInstrBr s11 (.LUI .x28 0x81)
  let s13 := execInstrBr s12 (.ADDI .x28 .x28 0xd8)
  let s14 := execInstrBr s13 (.SD .x28 .x6 0)
  let s15 := execInstrBr s14 (.LUI .x28 0x81)
  let s16 := execInstrBr s15 (.ADDI .x28 .x28 0xd0)
  have c0 : Keygen.instructionAt image 0x2010 = some (.base (.LUI .x28 0x81)) := by decide
  have c1 : Keygen.instructionAt image 0x2014 = some (.base (.ADDI .x28 .x28 8)) := by decide
  have c2 : Keygen.instructionAt image 0x2018 = some (.base (.LD .x6 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x201c = some (.base (.ADDI .x6 .x6 1)) := by decide
  have c4 : Keygen.instructionAt image 0x2020 = some (.base (.LUI .x28 0x81)) := by decide
  have c5 : Keygen.instructionAt image 0x2024 = some (.base (.ADDI .x28 .x28 8)) := by decide
  have c6 : Keygen.instructionAt image 0x2028 = some (.base (.SD .x28 .x6 0)) := by decide
  have c7 : Keygen.instructionAt image 0x202c = some (.base (.LUI .x28 0x81)) := by decide
  have c8 : Keygen.instructionAt image 0x2030 = some (.base (.ADDI .x28 .x28 0xd8)) := by decide
  have c9 : Keygen.instructionAt image 0x2034 = some (.base (.LD .x6 .x28 0)) := by decide
  have c10 : Keygen.instructionAt image 0x2038 = some (.base (.ADDI .x6 .x6 1)) := by decide
  have c11 : Keygen.instructionAt image 0x203c = some (.base (.LUI .x28 0x81)) := by decide
  have c12 : Keygen.instructionAt image 0x2040 = some (.base (.ADDI .x28 .x28 0xd8)) := by decide
  have c13 : Keygen.instructionAt image 0x2044 = some (.base (.SD .x28 .x6 0)) := by decide
  have c14 : Keygen.instructionAt image 0x2048 = some (.base (.LUI .x28 0x81)) := by decide
  have c15 : Keygen.instructionAt image 0x204c = some (.base (.ADDI .x28 .x28 0xd0)) := by decide
  have c16 : Keygen.instructionAt image 0x2050 = some (.base (.LD .x7 .x28 0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 16
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 8)) 15
  · have hp : s1.pc = 0x2014 := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 14
  · have hp : s2.pc = 0x2018 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [advanceState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 13
  · have hp : s3.pc = 0x201c := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 12
  · have hp : s4.pc = 0x2020 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 8)) 11
  · have hp : s5.pc = 0x2024 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 10
  · have hp : s6.pc = 0x2028 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · simp [advanceState,s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x81)) 9
  · have hp : s7.pc = 0x202c := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0xd8)) 8
  · have hp : s8.pc = 0x2030 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x6 .x28 0)) 7
  · have hp : s9.pc = 0x2034 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · simp [advanceState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x6 .x6 1)) 6
  · have hp : s10.pc = 0x2038 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LUI .x28 0x81)) 5
  · have hp : s11.pc = 0x203c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.ADDI .x28 .x28 0xd8)) 4
  · have hp : s12.pc = 0x2040 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.SD .x28 .x6 0)) 3
  · have hp : s13.pc = 0x2044 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c13
  · simp [advanceState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s14 s15 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s14.pc = 0x2048 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.ADDI .x28 .x28 0xd0)) 1
  · have hp : s15.pc = 0x204c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 (advanceState s) _ (.base (.LD .x7 .x28 0)) 0
  · have hp : s16.pc = 0x2050 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c16
  · simp [advanceState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem advance_pc (s : MachineState) (pc : s.pc = 0x2010) : (advanceState s).pc = 0x2054 := by
  simp [advanceState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms advance_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentAdvance67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentControl67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
def branchState (s : MachineState) : MachineState :=
  execInstrBr s (.BNE .x6 .x7 (-332))
theorem branch_steps (s : MachineState) (pc : s.pc = 0x2054) :
    OrdinarySteps image s 1 (branchState s) := by
  have code : Keygen.instructionAt image 0x2054 =
    some (.base (.BNE .x6 .x7 (-332))) := by decide
  apply OrdinarySteps.step s (branchState s) _
    (.base (.BNE .x6 .x7 (-332))) 0
  · simpa only [Keygen.fetch_at,pc] using code
  · rfl
  exact OrdinarySteps.refl _
theorem branch_pc (s : MachineState) (pc : s.pc = 0x2054) :
    (branchState s).pc =
      if s.getReg .x6 ≠ s.getReg .x7 then 0x1f08 else 0x2058 := by
  simp [branchState,execInstrBr,pc,signExtend13]
theorem advance_count (s : MachineState) :
    (GroupedBalancedSignBottomTreeParentAdvance67.advanceState s).getMem 0x810d8 =
      s.getMem 0x810d8 + 1 := by
  simp [GroupedBalancedSignBottomTreeParentAdvance67.advanceState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem advance_address (s : MachineState) :
    (GroupedBalancedSignBottomTreeParentAdvance67.advanceState s).getMem 0x81008 =
      s.getMem 0x81008 + 1 := by
  simp [GroupedBalancedSignBottomTreeParentAdvance67.advanceState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem advance_regs (s : MachineState) :
    (GroupedBalancedSignBottomTreeParentAdvance67.advanceState s).getReg .x6 =
      s.getMem 0x810d8 + 1 ∧
    (GroupedBalancedSignBottomTreeParentAdvance67.advanceState s).getReg .x7 =
      s.getMem 0x810d0 := by
  simp [GroupedBalancedSignBottomTreeParentAdvance67.advanceState,
    execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem advance_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81008) (h1 : a ≠ 0x810d8) :
    (GroupedBalancedSignBottomTreeParentAdvance67.advanceState s).getMem a =
      s.getMem a := by
  change a ≠ 528392#64 at h0
  change a ≠ 528600#64 at h1
  simp [GroupedBalancedSignBottomTreeParentAdvance67.advanceState,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,h0,h1]
theorem branch_frame (s : MachineState) (a : Word) :
    (branchState s).getMem a = s.getMem a := by
  simp [branchState,execInstrBr]
#print axioms branch_steps
#print axioms advance_count
#print axioms advance_address
#print axioms advance_regs
#print axioms advance_frame
#print axioms branch_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentControl67
