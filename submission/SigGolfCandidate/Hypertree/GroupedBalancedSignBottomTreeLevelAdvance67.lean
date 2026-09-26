import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeModel67
import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeParentControl67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelSwap67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelAdvance67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelSwap67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
def swapState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc8)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc0)
  let s := execInstrBr s (.SD .x28 .x7 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc8)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xd0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.SRLI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  execInstrBr s (.ADDI .x28 .x28 0xd0)
theorem swap_steps (s : MachineState) (pc : s.pc = 0x2058) :
    OrdinarySteps image s 18 (swapState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xc0)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0xc8)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  let s7 := execInstrBr s6 (.LUI .x28 0x81)
  let s8 := execInstrBr s7 (.ADDI .x28 .x28 0xc0)
  let s9 := execInstrBr s8 (.SD .x28 .x7 0)
  let s10 := execInstrBr s9 (.LUI .x28 0x81)
  let s11 := execInstrBr s10 (.ADDI .x28 .x28 0xc8)
  let s12 := execInstrBr s11 (.SD .x28 .x6 0)
  let s13 := execInstrBr s12 (.LUI .x28 0x81)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 0xd0)
  let s15 := execInstrBr s14 (.LD .x6 .x28 0)
  let s16 := execInstrBr s15 (.SRLI .x6 .x6 1)
  let s17 := execInstrBr s16 (.LUI .x28 0x81)
  have c0 : Keygen.instructionAt image 0x2058 = some (.base (.LUI .x28 0x81)) := by decide
  have c1 : Keygen.instructionAt image 0x205c = some (.base (.ADDI .x28 .x28 0xc0)) := by decide
  have c2 : Keygen.instructionAt image 0x2060 = some (.base (.LD .x6 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x2064 = some (.base (.LUI .x28 0x81)) := by decide
  have c4 : Keygen.instructionAt image 0x2068 = some (.base (.ADDI .x28 .x28 0xc8)) := by decide
  have c5 : Keygen.instructionAt image 0x206c = some (.base (.LD .x7 .x28 0)) := by decide
  have c6 : Keygen.instructionAt image 0x2070 = some (.base (.LUI .x28 0x81)) := by decide
  have c7 : Keygen.instructionAt image 0x2074 = some (.base (.ADDI .x28 .x28 0xc0)) := by decide
  have c8 : Keygen.instructionAt image 0x2078 = some (.base (.SD .x28 .x7 0)) := by decide
  have c9 : Keygen.instructionAt image 0x207c = some (.base (.LUI .x28 0x81)) := by decide
  have c10 : Keygen.instructionAt image 0x2080 = some (.base (.ADDI .x28 .x28 0xc8)) := by decide
  have c11 : Keygen.instructionAt image 0x2084 = some (.base (.SD .x28 .x6 0)) := by decide
  have c12 : Keygen.instructionAt image 0x2088 = some (.base (.LUI .x28 0x81)) := by decide
  have c13 : Keygen.instructionAt image 0x208c = some (.base (.ADDI .x28 .x28 0xd0)) := by decide
  have c14 : Keygen.instructionAt image 0x2090 = some (.base (.LD .x6 .x28 0)) := by decide
  have c15 : Keygen.instructionAt image 0x2094 = some (.base (.SRLI .x6 .x6 1)) := by decide
  have c16 : Keygen.instructionAt image 0x2098 = some (.base (.LUI .x28 0x81)) := by decide
  have c17 : Keygen.instructionAt image 0x209c = some (.base (.ADDI .x28 .x28 0xd0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 17
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xc0)) 16
  · have hp : s1.pc = 0x205c := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 15
  · have hp : s2.pc = 0x2060 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · simp [swapState,s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 14
  · have hp : s3.pc = 0x2064 := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0xc8)) 13
  · have hp : s4.pc = 0x2068 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 12
  · have hp : s5.pc = 0x206c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · simp [swapState,s1,s2,s3,s4,s5,s6,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s6 s7 _ (.base (.LUI .x28 0x81)) 11
  · have hp : s6.pc = 0x2070 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x28 .x28 0xc0)) 10
  · have hp : s7.pc = 0x2074 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x28 .x7 0)) 9
  · have hp : s8.pc = 0x2078 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · simp [swapState,s1,s2,s3,s4,s5,s6,s7,s8,s9,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s9 s10 _ (.base (.LUI .x28 0x81)) 8
  · have hp : s9.pc = 0x207c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.ADDI .x28 .x28 0xc8)) 7
  · have hp : s10.pc = 0x2080 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.SD .x28 .x6 0)) 6
  · have hp : s11.pc = 0x2084 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · simp [swapState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 0x81)) 5
  · have hp : s12.pc = 0x2088 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 0xd0)) 4
  · have hp : s13.pc = 0x208c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.LD .x6 .x28 0)) 3
  · have hp : s14.pc = 0x2090 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [swapState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.SRLI .x6 .x6 1)) 2
  · have hp : s15.pc = 0x2094 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.LUI .x28 0x81)) 1
  · have hp : s16.pc = 0x2098 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 (swapState s) _ (.base (.ADDI .x28 .x28 0xd0)) 0
  · have hp : s17.pc = 0x209c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c17
  · rfl
  exact OrdinarySteps.refl _
theorem swap_pc (s : MachineState) (pc : s.pc = 0x2058) : (swapState s).pc = 0x20a0 := by
  simp [swapState,execInstrBr,pc,signExtend12,signExtend13]
theorem swap_ptr (s : MachineState) :
    (swapState s).getReg .x28 = 0x810d0 := by
  simp [swapState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem swap_source (s : MachineState) :
    (swapState s).getMem 0x810c0 = s.getMem 0x810c8 := by
  simp [swapState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem swap_target (s : MachineState) :
    (swapState s).getMem 0x810c8 = s.getMem 0x810c0 := by
  simp [swapState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem swap_half_count (s : MachineState) :
    (swapState s).getReg .x6 = s.getMem 0x810d0 >>> 1 := by
  simp [swapState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem swap_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x810c0) (h1 : a ≠ 0x810c8) :
    (swapState s).getMem a = s.getMem a := by
  change a ≠ 528576#64 at h0
  change a ≠ 528584#64 at h1
  simp [swapState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1]
#print axioms swap_steps
#print axioms swap_ptr
#print axioms swap_source
#print axioms swap_target
#print axioms swap_half_count
#print axioms swap_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelSwap67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
def advanceState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x50)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x50)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  execInstrBr s (.LD .x7 .x28 0)
theorem advance_steps (s : MachineState) (pc : s.pc = 0x20a0)
    (ptr : s.getReg .x28 = 0x810d0) :
    OrdinarySteps image s 18 (advanceState s) := by
  let s1 := execInstrBr s (.SD .x28 .x6 0)
  let s2 := execInstrBr s1 (.LUI .x28 0x81)
  let s3 := execInstrBr s2 (.ADDI .x28 .x28 0)
  let s4 := execInstrBr s3 (.LD .x6 .x28 0)
  let s5 := execInstrBr s4 (.ADDI .x6 .x6 1)
  let s6 := execInstrBr s5 (.LUI .x28 0x81)
  let s7 := execInstrBr s6 (.ADDI .x28 .x28 0)
  let s8 := execInstrBr s7 (.SD .x28 .x6 0)
  let s9 := execInstrBr s8 (.LUI .x28 0x81)
  let s10 := execInstrBr s9 (.ADDI .x28 .x28 0x50)
  let s11 := execInstrBr s10 (.LD .x6 .x28 0)
  let s12 := execInstrBr s11 (.ADDI .x6 .x6 1)
  let s13 := execInstrBr s12 (.LUI .x28 0x81)
  let s14 := execInstrBr s13 (.ADDI .x28 .x28 0x50)
  let s15 := execInstrBr s14 (.SD .x28 .x6 0)
  let s16 := execInstrBr s15 (.LUI .x28 0x81)
  let s17 := execInstrBr s16 (.ADDI .x28 .x28 0x60)
  have c0 : Keygen.instructionAt image 0x20a0 = some (.base (.SD .x28 .x6 0)) := by decide
  have c1 : Keygen.instructionAt image 0x20a4 = some (.base (.LUI .x28 0x81)) := by decide
  have c2 : Keygen.instructionAt image 0x20a8 = some (.base (.ADDI .x28 .x28 0)) := by decide
  have c3 : Keygen.instructionAt image 0x20ac = some (.base (.LD .x6 .x28 0)) := by decide
  have c4 : Keygen.instructionAt image 0x20b0 = some (.base (.ADDI .x6 .x6 1)) := by decide
  have c5 : Keygen.instructionAt image 0x20b4 = some (.base (.LUI .x28 0x81)) := by decide
  have c6 : Keygen.instructionAt image 0x20b8 = some (.base (.ADDI .x28 .x28 0)) := by decide
  have c7 : Keygen.instructionAt image 0x20bc = some (.base (.SD .x28 .x6 0)) := by decide
  have c8 : Keygen.instructionAt image 0x20c0 = some (.base (.LUI .x28 0x81)) := by decide
  have c9 : Keygen.instructionAt image 0x20c4 = some (.base (.ADDI .x28 .x28 0x50)) := by decide
  have c10 : Keygen.instructionAt image 0x20c8 = some (.base (.LD .x6 .x28 0)) := by decide
  have c11 : Keygen.instructionAt image 0x20cc = some (.base (.ADDI .x6 .x6 1)) := by decide
  have c12 : Keygen.instructionAt image 0x20d0 = some (.base (.LUI .x28 0x81)) := by decide
  have c13 : Keygen.instructionAt image 0x20d4 = some (.base (.ADDI .x28 .x28 0x50)) := by decide
  have c14 : Keygen.instructionAt image 0x20d8 = some (.base (.SD .x28 .x6 0)) := by decide
  have c15 : Keygen.instructionAt image 0x20dc = some (.base (.LUI .x28 0x81)) := by decide
  have c16 : Keygen.instructionAt image 0x20e0 = some (.base (.ADDI .x28 .x28 0x60)) := by decide
  have c17 : Keygen.instructionAt image 0x20e4 = some (.base (.LD .x7 .x28 0)) := by decide
  apply OrdinarySteps.step s s1 _ (.base (.SD .x28 .x6 0)) 17
  · simpa only [Keygen.fetch_at,pc] using c0
  · simp [advanceState,s1,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ptr]
  apply OrdinarySteps.step s1 s2 _ (.base (.LUI .x28 0x81)) 16
  · have hp : s1.pc = 0x20a4 := by simp [s1,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x28 .x28 0)) 15
  · have hp : s2.pc = 0x20a8 := by simp [s1,s2,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x6 .x28 0)) 14
  · have hp : s3.pc = 0x20ac := by simp [s1,s2,s3,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c3
  · simp [advanceState,s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x6 .x6 1)) 13
  · have hp : s4.pc = 0x20b0 := by simp [s1,s2,s3,s4,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x28 0x81)) 12
  · have hp : s5.pc = 0x20b4 := by simp [s1,s2,s3,s4,s5,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x28 .x28 0)) 11
  · have hp : s6.pc = 0x20b8 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x28 .x6 0)) 10
  · have hp : s7.pc = 0x20bc := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c7
  · simp [advanceState,s1,s2,s3,s4,s5,s6,s7,s8,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s8 s9 _ (.base (.LUI .x28 0x81)) 9
  · have hp : s8.pc = 0x20c0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x28 .x28 0x50)) 8
  · have hp : s9.pc = 0x20c4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LD .x6 .x28 0)) 7
  · have hp : s10.pc = 0x20c8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c10
  · simp [advanceState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x6 .x6 1)) 6
  · have hp : s11.pc = 0x20cc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c11
  · rfl
  apply OrdinarySteps.step s12 s13 _ (.base (.LUI .x28 0x81)) 5
  · have hp : s12.pc = 0x20d0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c12
  · rfl
  apply OrdinarySteps.step s13 s14 _ (.base (.ADDI .x28 .x28 0x50)) 4
  · have hp : s13.pc = 0x20d4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c13
  · rfl
  apply OrdinarySteps.step s14 s15 _ (.base (.SD .x28 .x6 0)) 3
  · have hp : s14.pc = 0x20d8 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c14
  · simp [advanceState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  apply OrdinarySteps.step s15 s16 _ (.base (.LUI .x28 0x81)) 2
  · have hp : s15.pc = 0x20dc := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c15
  · rfl
  apply OrdinarySteps.step s16 s17 _ (.base (.ADDI .x28 .x28 0x60)) 1
  · have hp : s16.pc = 0x20e0 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c16
  · rfl
  apply OrdinarySteps.step s17 (advanceState s) _ (.base (.LD .x7 .x28 0)) 0
  · have hp : s17.pc = 0x20e4 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,execInstrBr,pc,signExtend12,signExtend13]
    simpa only [Keygen.fetch_at,hp] using c17
  · simp [advanceState,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,accessValid,rangeValid,MEMORY_BYTES,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
  exact OrdinarySteps.refl _
theorem advance_pc (s : MachineState) (pc : s.pc = 0x20a0) : (advanceState s).pc = 0x20e8 := by
  simp [advanceState,execInstrBr,pc,signExtend12,signExtend13]
theorem advance_half_count (s : MachineState) (ptr : s.getReg .x28 = 0x810d0) :
    (advanceState s).getMem 0x810d0 = s.getReg .x6 := by
  simp [advanceState,execInstrBr,signExtend12,ptr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem advance_height (s : MachineState) (ptr : s.getReg .x28 = 0x810d0) :
    (advanceState s).getMem 0x81000 = s.getMem 0x81000 + 1 := by
  simp [advanceState,execInstrBr,signExtend12,ptr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem advance_witness_level (s : MachineState) (ptr : s.getReg .x28 = 0x810d0) :
    (advanceState s).getMem 0x81050 = s.getMem 0x81050 + 1 := by
  simp [advanceState,execInstrBr,signExtend12,ptr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem advance_regs (s : MachineState) (ptr : s.getReg .x28 = 0x810d0) :
    (advanceState s).getReg .x6 = s.getMem 0x81050 + 1 ∧
    (advanceState s).getReg .x7 = s.getMem 0x81060 := by
  simp [advanceState,execInstrBr,signExtend12,ptr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem advance_frame (s : MachineState) (a : Word)
    (ptr : s.getReg .x28 = 0x810d0)
    (h0 : a ≠ 0x810d0) (h1 : a ≠ 0x81000) (h2 : a ≠ 0x81050) :
    (advanceState s).getMem a = s.getMem a := by
  change a ≠ 528592#64 at h0
  change a ≠ 528384#64 at h1
  change a ≠ 528464#64 at h2
  simp [advanceState,execInstrBr,signExtend12,ptr,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2]
#print axioms advance_steps
#print axioms advance_half_count
#print axioms advance_height
#print axioms advance_witness_level
#print axioms advance_regs
#print axioms advance_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelAdvance67
