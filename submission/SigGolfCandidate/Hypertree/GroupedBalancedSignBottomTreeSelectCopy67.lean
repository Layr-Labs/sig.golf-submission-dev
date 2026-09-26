import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeH4Query67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectPtr67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectCopy67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectPtr67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
private abbrev image := GroupedBalancedSignImage67.image
def selectState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe8)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x50)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.SRL .x6 .x6 .x7)
  let s := execInstrBr s (.XORI .x6 .x6 1)
  let s := execInstrBr s (.SLLI .x6 .x6 4)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc0)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.ADD .x6 .x6 .x7)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x50)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.SLLI .x7 .x7 4)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xf8)
  let s := execInstrBr s (.LD .x10 .x28 0)
  execInstrBr s (.ADD .x7 .x7 .x10)
theorem select_steps (s : MachineState) (pc : s.pc = 0x1e94) :
    OrdinarySteps image s 21 (selectState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xe8)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0x50)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.SRL .x6 .x6 .x7)
  let s8 := execInstrBr s7 (.XORI .x6 .x6 1)
  let s9 := execInstrBr s8 (.SLLI .x6 .x6 4)
  let s10 := execInstrBr s9 (.LUI .x28 0x81)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 0xc0)
  let s12 := execInstrBr s11 (.LD .x7 .x28 0)
  let s13 := execInstrBr s12 (.ADD .x6 .x6 .x7)
  let s14 := execInstrBr s13 (.LUI .x28 0x81)
  let s15 := execInstrBr s14 (.ADDI .x28 .x28 0x50)
  let s16 := execInstrBr s15 (.LD .x7 .x28 0)
  let s17 := execInstrBr s16 (.SLLI .x7 .x7 4)
  let s18 := execInstrBr s17 (.LUI .x28 0x81)
  let s19 := execInstrBr s18 (.ADDI .x28 .x28 0xf8)
  let s20 := execInstrBr s19 (.LD .x10 .x28 0)
  have c0 : Keygen.instructionAt image 0x1e94 = some (.base (.LUI .x28 0x81)) := by decide
  have c1 : Keygen.instructionAt image 0x1e98 = some (.base (.ADDI .x28 .x28 0xe8)) := by decide
  have c2 : Keygen.instructionAt image 0x1e9c = some (.base (.LD .x6 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1ea0 = some (.base (.LUI .x28 0x81)) := by decide
  have c4 : Keygen.instructionAt image 0x1ea4 = some (.base (.ADDI .x28 .x28 0x50)) := by decide
  have c5 : Keygen.instructionAt image 0x1ea8 = some (.base (.LD .x7 .x28 0)) := by decide
  have c6 : Keygen.instructionAt image 0x1eac = some (.base (.SRL .x6 .x6 .x7)) := by decide
  have c7 : Keygen.instructionAt image 0x1eb0 = some (.base (.XORI .x6 .x6 1)) := by decide
  have c8 : Keygen.instructionAt image 0x1eb4 = some (.base (.SLLI .x6 .x6 4)) := by decide
  have c9 : Keygen.instructionAt image 0x1eb8 = some (.base (.LUI .x28 0x81)) := by decide
  have c10 : Keygen.instructionAt image 0x1ebc = some (.base (.ADDI .x28 .x28 0xc0)) := by decide
  have c11 : Keygen.instructionAt image 0x1ec0 = some (.base (.LD .x7 .x28 0)) := by decide
  have c12 : Keygen.instructionAt image 0x1ec4 = some (.base (.ADD .x6 .x6 .x7)) := by decide
  have c13 : Keygen.instructionAt image 0x1ec8 = some (.base (.LUI .x28 0x81)) := by decide
  have c14 : Keygen.instructionAt image 0x1ecc = some (.base (.ADDI .x28 .x28 0x50)) := by decide
  have c15 : Keygen.instructionAt image 0x1ed0 = some (.base (.LD .x7 .x28 0)) := by decide
  have c16 : Keygen.instructionAt image 0x1ed4 = some (.base (.SLLI .x7 .x7 4)) := by decide
  have c17 : Keygen.instructionAt image 0x1ed8 = some (.base (.LUI .x28 0x81)) := by decide
  have c18 : Keygen.instructionAt image 0x1edc = some (.base (.ADDI .x28 .x28 0xf8)) := by decide
  have c19 : Keygen.instructionAt image 0x1ee0 = some (.base (.LD .x10 .x28 0)) := by decide
  have c20 : Keygen.instructionAt image 0x1ee4 = some (.base (.ADD .x7 .x7 .x10)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 20
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xe8)) 19
  · have hp : s1.pc = 0x1e98 := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 18
  · have hp : s2.pc = 0x1e9c := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [selectState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 17
  · have hp : s3.pc = 0x1ea0 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0x50)) 16
  · have hp : s4.pc = 0x1ea4 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 15
  · have hp : s5.pc = 0x1ea8 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [selectState,s1,s2,s3,s4,s5,s6,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.SRL .x6 .x6 .x7)) 14
  · have hp : s6.pc = 0x1eac := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.XORI .x6 .x6 1)) 13
  · have hp : s7.pc = 0x1eb0 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SLLI .x6 .x6 4)) 12
  · have hp : s8.pc = 0x1eb4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s9.pc = 0x1eb8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 0xc0)) 10
  · have hp : s10.pc = 0x1ebc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.LD .x7 .x28 0)) 9
  · have hp : s11.pc = 0x1ec0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [selectState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.ADD .x6 .x6 .x7)) 8
  · have hp : s12.pc = 0x1ec4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.LUI .x28 0x81)) 7
  · have hp : s13.pc = 0x1ec8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.ADDI .x28 .x28 0x50)) 6
  · have hp : s14.pc = 0x1ecc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c14
  · rfl
  apply OrdinarySteps.step s15 s16 _ (.base (.LD .x7 .x28 0)) 5
  · have hp : s15.pc = 0x1ed0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c15
  · simp [selectState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s16 s17 _ (.base (.SLLI .x7 .x7 4)) 4
  · have hp : s16.pc = 0x1ed4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 s18 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s17.pc = 0x1ed8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  apply OrdinarySteps.step s18 s19 _ (.base (.ADDI .x28 .x28 0xf8)) 2
  · have hp : s18.pc = 0x1edc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c18
  · rfl
  apply OrdinarySteps.step s19 s20 _ (.base (.LD .x10 .x28 0)) 1
  · have hp : s19.pc = 0x1ee0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c19
  · simp [selectState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s20 (selectState s) _ (.base (.ADD .x7 .x7 .x10)) 0
  · have hp : s20.pc = 0x1ee4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c20
  · rfl
  exact OrdinarySteps.refl _
theorem select_pc (s : MachineState) (pc : s.pc = 0x1e94) : (selectState s).pc = 0x1ee8 := by
  simp [selectState,execInstrBr,pc,signExtend12,signExtend13]
#print axioms select_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectPtr67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
def copyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x10 .x6 0)
  let s := execInstrBr s (.LD .x11 .x6 8)
  let s := execInstrBr s (.SD .x7 .x10 0)
  execInstrBr s (.SD .x7 .x11 8)
theorem copy_steps (s : MachineState) (pc : s.pc = 0x1ee8)
    (src0 : accessValid (s.getReg .x6) 8 = true)
    (src1 : accessValid (s.getReg .x6 + 8) 8 = true)
    (dst0 : accessValid (s.getReg .x7) 8 = true)
    (dst1 : accessValid (s.getReg .x7 + 8) 8 = true) :
    OrdinarySteps image s 4 (copyState s) := by
  let s1 := execInstrBr s (.LD .x10 .x6 0)
  let s2 := execInstrBr s1 (.LD .x11 .x6 8)
  let s3 := execInstrBr s2 (.SD .x7 .x10 0)
  have c0 : Keygen.instructionAt image 0x1ee8 = some (.base (.LD .x10 .x6 0)) := by decide
  have c1 : Keygen.instructionAt image 0x1eec = some (.base (.LD .x11 .x6 8)) := by decide
  have c2 : Keygen.instructionAt image 0x1ef0 = some (.base (.SD .x7 .x10 0)) := by decide
  have c3 : Keygen.instructionAt image 0x1ef4 = some (.base (.SD .x7 .x11 8)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LD .x10 .x6 0)) 3
  · simpa only [Keygen.fetch_at,pc] using c0
  · simp [s1,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,src0]
  apply OrdinarySteps.step s1 s2 _ (.base (.LD .x11 .x6 8)) 2
  · have hp : s1.pc = 0x1eec := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · simpa [s1,s2,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using src1
  apply OrdinarySteps.step s2 s3 _ (.base (.SD .x7 .x10 0)) 1
  · have hp : s2.pc = 0x1ef0 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      dst0,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 (copyState s) _ (.base (.SD .x7 .x11 8)) 0
  · have hp : s3.pc = 0x1ef4 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · simpa [copyState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,
      signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using dst1
  exact OrdinarySteps.refl _
theorem copy_pc (s : MachineState) (pc : s.pc = 0x1ee8) :
    (copyState s).pc = 0x1ef8 := by
  simp [copyState,execInstrBr,pc,signExtend12]
#print axioms copy_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeSelectCopy67
