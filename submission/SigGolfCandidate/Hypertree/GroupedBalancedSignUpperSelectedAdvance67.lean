import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedShift67
import SigGolfCandidate.Hypertree.SignShift

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedAdvance67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image
def fullState (s : MachineState) : MachineState :=
  GroupedBalancedSignUpperSelectedShift67.shiftState
    (GroupedBalancedSignUpperSelectedLoad67.loadState s)
theorem full_steps (s : MachineState) (pc : s.pc = 0x1c94) :
    OrdinarySteps image s 25 (fullState s) := by
  have a := GroupedBalancedSignUpperSelectedLoad67.load_steps s pc
  have b := GroupedBalancedSignUpperSelectedShift67.shift_steps
    (GroupedBalancedSignUpperSelectedLoad67.loadState s)
    (GroupedBalancedSignUpperSelectedLoad67.load_pc s pc)
  exact Keygen.ordinary_trans image s
    (GroupedBalancedSignUpperSelectedLoad67.loadState s)
    (fullState s) 9 16 a b
theorem full_pc (s : MachineState) (pc : s.pc = 0x1c94) :
    (fullState s).pc = 0x1cf8 := by
  exact GroupedBalancedSignUpperSelectedShift67.shift_pc
    (GroupedBalancedSignUpperSelectedLoad67.loadState s)
    (GroupedBalancedSignUpperSelectedLoad67.load_pc s pc)
theorem shifted_low (s : MachineState) :
    (fullState s).getMem 0x81090 =
      (s.getMem 0x81090 >>> 1) + (s.getMem 0x81098 <<< 63) := by
  simp [fullState,GroupedBalancedSignUpperSelectedLoad67.loadState,
    GroupedBalancedSignUpperSelectedShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shifted_mid (s : MachineState) :
    (fullState s).getMem 0x81098 =
      (s.getMem 0x81098 >>> 1) + (s.getMem 0x810a0 <<< 63) := by
  simp [fullState,GroupedBalancedSignUpperSelectedLoad67.loadState,
    GroupedBalancedSignUpperSelectedShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shifted_high (s : MachineState) :
    (fullState s).getMem 0x810a0 = s.getMem 0x810a0 >>> 1 := by
  simp [fullState,GroupedBalancedSignUpperSelectedLoad67.loadState,
    GroupedBalancedSignUpperSelectedShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shift_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81090) (h1 : a ≠ 0x81098) (h2 : a ≠ 0x810a0) :
    (fullState s).getMem a = s.getMem a := by
  change a ≠ 528528#64 at h0
  change a ≠ 528536#64 at h1
  change a ≠ 528544#64 at h2
  simp [fullState,GroupedBalancedSignUpperSelectedLoad67.loadState,
    GroupedBalancedSignUpperSelectedShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2]
theorem shifted_index (s : MachineState) (index : BitVec 192)
    (stored : ∀ i : Fin 3,
      s.getMem (Signing.wordAddress 0x81090 i.val) =
        index.extractLsb' (64*i.val) 64) :
    ∀ i : Fin 3,
      (fullState s).getMem (Signing.wordAddress 0x81090 i.val) =
        (index >>> 1).extractLsb' (64*i.val) 64 := by
  have w0 : s.getMem 0x81090 = index.extractLsb' 0 64 := stored 0
  have w1 : s.getMem 0x81098 = index.extractLsb' 64 64 := stored 1
  have w2 : s.getMem 0x810a0 = index.extractLsb' 128 64 := stored 2
  intro i
  fin_cases i
  · change (fullState s).getMem 0x81090 = _
    rw [shifted_low,w0,w1]
    exact Signing.shifted_limb index 0
  · change (fullState s).getMem 0x81098 = _
    rw [shifted_mid,w1,w2]
    exact Signing.shifted_limb index 1
  · change (fullState s).getMem 0x810a0 = _
    rw [shifted_high,w2]
    exact Signing.shifted_high_limb index
#print axioms full_steps
#print axioms shifted_index
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedData67

end

/-! Advance the 3/4-bit upper-group selected-index shift counter. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67Byte.image

def advanceState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x100)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x100)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x60)
  let s := execInstrBr s (.LD .x7 .x28 0)
  execInstrBr s (.BNE .x6 .x7 (-140))

theorem advance_count (s : MachineState) :
    (advanceState s).getMem 0x81100 = s.getMem 0x81100 + 1 := by
  simp [advanceState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem advance_frame (s : MachineState) (a : Word) (ha : a ≠ 0x81100) :
    (advanceState s).getMem a = s.getMem a := by
  change a ≠ 528640#64 at ha
  simp [advanceState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

theorem advance_pc (s : MachineState) (pc : s.pc = 0x1cf8) :
    (advanceState s).pc =
      if s.getMem 0x81100 + 1 = s.getMem 0x81060 then 0x1d24 else 0x1c94 := by
  have raw : (advanceState s).pc =
      if (advanceState s).getMem 0x81100 =
          (advanceState s).getMem 0x81060
      then 0x1d24 else 0x1c94 := by
    simp [advanceState,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,pc]
  rw [raw,advance_count,advance_frame s 0x81060 (by decide)]

private theorem advance_code :
    Keygen.instructionAt image 0x1cf8 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1cfc = some (.base (.ADDI .x28 .x28 0x100)) ∧
    Keygen.instructionAt image 0x1d00 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1d04 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1d08 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1d0c = some (.base (.ADDI .x28 .x28 0x100)) ∧
    Keygen.instructionAt image 0x1d10 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x1d14 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x1d18 = some (.base (.ADDI .x28 .x28 0x60)) ∧
    Keygen.instructionAt image 0x1d1c = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x1d20 = some (.base (.BNE .x6 .x7 (-140))) := by decide

theorem advance_steps (s : MachineState) (pc : s.pc = 0x1cf8) :
    OrdinarySteps image s 11 (advanceState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x100)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x100)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.LUI .x28 0x81)
  let s9 := execInstrBr s8 (.ADDI .x28 .x28 0x60)
  let s10 := execInstrBr s9 (.LD .x7 .x28 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10⟩ := advance_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 10
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x100)) 9
  · have hp : s1.pc = 0x1cfc := by simp [s1,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 8
  · have hp : s2.pc = 0x1d00 := by simp [s1,s2,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c2
  · simpa [s1,s2,s3,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using
      (by decide : accessValid (0x81100 : Word) 8 = true)
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 7
  · have hp : s3.pc = 0x1d04 := by simp [s1,s2,s3,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 6
  · have hp : s4.pc = 0x1d08 := by simp [s1,s2,s3,s4,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x100)) 5
  · have hp : s5.pc = 0x1d0c := by simp [s1,s2,s3,s4,s5,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 4
  · have hp : s6.pc = 0x1d10 := by simp [s1,s2,s3,s4,s5,s6,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c6
  · simpa [s1,s2,s3,s4,s5,s6,s7,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using
      (by decide : accessValid (0x81100 : Word) 8 = true)
  apply OrdinarySteps.step s7 s8 _ (.base (.LUI .x28 0x81)) 3
  · have hp : s7.pc = 0x1d14 := by simp [s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c7
  · rfl
  apply OrdinarySteps.step s8 s9 _ (.base (.ADDI .x28 .x28 0x60)) 2
  · have hp : s8.pc = 0x1d18 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c8
  · rfl
  apply OrdinarySteps.step s9 s10 _ (.base (.LD .x7 .x28 0)) 1
  · have hp : s9.pc = 0x1d1c := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c9
  · simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ordinaryStep,memoryArgumentsValid,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      accessValid,rangeValid,MEMORY_BYTES] using
      (by decide : accessValid (0x81060 : Word) 8 = true)
  apply OrdinarySteps.step s10 (advanceState s) _ (.base (.BNE .x6 .x7 (-140))) 0
  · have hp : s10.pc = 0x1d20 := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,execInstrBr,pc]
    simpa only [Keygen.fetch_at,hp] using c10
  · rfl
  exact OrdinarySteps.refl _

#print axioms advance_steps
#print axioms advance_count
#print axioms advance_frame
#print axioms advance_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperSelectedAdvance67
