import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67
import SigGolfCandidate.Hypertree.KeygenBlocks

/-! Copy the completed bottom root into CURRENT and reset the selected-index shift count. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomRootCopy67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image

def copyState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xc0)
  let s := execInstrBr s (.LD .x7 .x28 0)
  let s := execInstrBr s (.LD .x10 .x7 0)
  let s := execInstrBr s (.LD .x11 .x7 8)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x500)
  let s := execInstrBr s (.SD .x7 .x10 0)
  let s := execInstrBr s (.SD .x7 .x11 8)
  let s := execInstrBr s (.ADDI .x6 .x0 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x100)
  execInstrBr s (.SD .x28 .x6 0)

private theorem copy_code :
    Keygen.instructionAt image 0x14f0 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x14f4 = some (.base (.ADDI .x28 .x28 0xc0)) ∧
    Keygen.instructionAt image 0x14f8 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x14fc = some (.base (.LD .x10 .x7 0)) ∧
    Keygen.instructionAt image 0x1500 = some (.base (.LD .x11 .x7 8)) ∧
    Keygen.instructionAt image 0x1504 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x1508 = some (.base (.ADDI .x7 .x7 0x500)) ∧
    Keygen.instructionAt image 0x150c = some (.base (.SD .x7 .x10 0)) ∧
    Keygen.instructionAt image 0x1510 = some (.base (.SD .x7 .x11 8)) ∧
    Keygen.instructionAt image 0x1514 = some (.base (.ADDI .x6 .x0 0)) ∧
    Keygen.instructionAt image 0x1518 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x151c = some (.base (.ADDI .x28 .x28 0x100)) ∧
    Keygen.instructionAt image 0x1520 = some (.base (.SD .x28 .x6 0)) := by decide

theorem copy_steps (s : MachineState)
    (pc : s.pc = 0x14f0) (source : s.getMem 0x810c0 = 0x83000) :
    OrdinarySteps image s 13 (copyState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xc0)
  let s3 := execInstrBr s2 (.LD .x7 .x28 0)
  let s4 := execInstrBr s3 (.LD .x10 .x7 0)
  let s5 := execInstrBr s4 (.LD .x11 .x7 8)
  let s6 := execInstrBr s5 (.LUI .x7 0x80)
  let s7 := execInstrBr s6 (.ADDI .x7 .x7 0x500)
  let s8 := execInstrBr s7 (.SD .x7 .x10 0)
  let s9 := execInstrBr s8 (.SD .x7 .x11 8)
  let s10 := execInstrBr s9 (.ADDI .x6 .x0 0)
  let s11 := execInstrBr s10 (.LUI .x28 0x81)
  let s12 := execInstrBr s11 (.ADDI .x28 .x28 0x100)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12⟩ := copy_code
  have hv0 : accessValid (s.getMem 0x810c0) 8 = true := by rw [source]; decide
  have hv8 : accessValid (s.getMem 0x810c0 + 8) 8 = true := by rw [source]; decide
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 12
  · simpa [Keygen.fetch_at, execInstrBr, pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xc0)) 11
  · simpa [Keygen.fetch_at, s1, execInstrBr, pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x7 .x28 0)) 10
  · simpa [Keygen.fetch_at, s1, s2, execInstrBr, pc] using c2
  · simp [ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, source, s1, s2, s3]
  apply OrdinarySteps.step s3 s4 _ (.base (.LD .x10 .x7 0)) 9
  · simpa [Keygen.fetch_at, s1, s2, s3, execInstrBr, pc] using c3
  · simpa [s1,s2,s3,s4,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using hv0
  apply OrdinarySteps.step s4 s5 _ (.base (.LD .x11 .x7 8)) 8
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, execInstrBr, pc] using c4
  · simpa [s1,s2,s3,s4,s5,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne] using hv8
  apply OrdinarySteps.step s5 s6 _ (.base (.LUI .x7 0x80)) 7
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, execInstrBr, pc] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.ADDI .x7 .x7 0x500)) 6
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, execInstrBr, pc] using c6
  · rfl
  apply OrdinarySteps.step s7 s8 _ (.base (.SD .x7 .x10 0)) 5
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc] using c7
  · simp [ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, source, s1, s2, s3, s4, s5, s6, s7, s8]
  apply OrdinarySteps.step s8 s9 _ (.base (.SD .x7 .x11 8)) 4
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc] using c8
  · simp [ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, source, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  apply OrdinarySteps.step s9 s10 _ (.base (.ADDI .x6 .x0 0)) 3
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, execInstrBr, pc] using c9
  · rfl
  apply OrdinarySteps.step s10 s11 _ (.base (.LUI .x28 0x81)) 2
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, execInstrBr, pc] using c10
  · rfl
  apply OrdinarySteps.step s11 s12 _ (.base (.ADDI .x28 .x28 0x100)) 1
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, execInstrBr, pc] using c11
  · rfl
  apply OrdinarySteps.step s12 (copyState s) _ (.base (.SD .x28 .x6 0)) 0
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, execInstrBr, pc] using c12
  · simp [copyState, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, source, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]
  exact OrdinarySteps.refl _

theorem copy_pc (s : MachineState) (pc : s.pc = 0x14f0) :
    (copyState s).pc = 0x1524 := by
  simp [copyState,execInstrBr,pc]

theorem copy_words (s : MachineState) (source : s.getMem 0x810c0 = 0x83000) :
    (copyState s).getMem 0x80500 = s.getMem 0x83000 ∧
    (copyState s).getMem 0x80508 = s.getMem 0x83008 ∧
    (copyState s).getMem 0x81100 = 0 := by
  have source' : s.getMem (528576#64) = (536576#64) := source
  simp [copyState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,source']

theorem copy_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x80500) (h1 : a ≠ 0x80508) (h2 : a ≠ 0x81100) :
    (copyState s).getMem a = s.getMem a := by
  change a ≠ 525568#64 at h0
  change a ≠ 525576#64 at h1
  change a ≠ 528640#64 at h2
  simp [copyState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2]

#print axioms copy_steps
#print axioms copy_words
#print axioms copy_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomRootCopy67
