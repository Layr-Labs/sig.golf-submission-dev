import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedShift67
import SigGolfCandidate.Hypertree.SignShift

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedData67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedAdvance67. -/
section
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image
def fullState (s : MachineState) : MachineState :=
  GroupedBalancedSignBottomSelectedShift67.shiftState
    (GroupedBalancedSignBottomSelectedLoad67.loadState s)
theorem full_steps (s : MachineState) (pc : s.pc = 0x1524) :
    OrdinarySteps image s 25 (fullState s) := by
  have a := GroupedBalancedSignBottomSelectedLoad67.load_steps s pc
  have b := GroupedBalancedSignBottomSelectedShift67.shift_steps
    (GroupedBalancedSignBottomSelectedLoad67.loadState s)
    (GroupedBalancedSignBottomSelectedLoad67.load_pc s pc)
  exact Keygen.ordinary_trans image s
    (GroupedBalancedSignBottomSelectedLoad67.loadState s)
    (fullState s) 9 16 a b
theorem full_pc (s : MachineState) (pc : s.pc = 0x1524) :
    (fullState s).pc = 0x1588 := by
  exact GroupedBalancedSignBottomSelectedShift67.shift_pc
    (GroupedBalancedSignBottomSelectedLoad67.loadState s)
    (GroupedBalancedSignBottomSelectedLoad67.load_pc s pc)
theorem shifted_low (s : MachineState) :
    (fullState s).getMem 0x81090 =
      (s.getMem 0x81090 >>> 1) + (s.getMem 0x81098 <<< 63) := by
  simp [fullState,GroupedBalancedSignBottomSelectedLoad67.loadState,
    GroupedBalancedSignBottomSelectedShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shifted_mid (s : MachineState) :
    (fullState s).getMem 0x81098 =
      (s.getMem 0x81098 >>> 1) + (s.getMem 0x810a0 <<< 63) := by
  simp [fullState,GroupedBalancedSignBottomSelectedLoad67.loadState,
    GroupedBalancedSignBottomSelectedShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shifted_high (s : MachineState) :
    (fullState s).getMem 0x810a0 = s.getMem 0x810a0 >>> 1 := by
  simp [fullState,GroupedBalancedSignBottomSelectedLoad67.loadState,
    GroupedBalancedSignBottomSelectedShift67.shiftState,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
theorem shift_frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x81090) (h1 : a ≠ 0x81098) (h2 : a ≠ 0x810a0) :
    (fullState s).getMem a = s.getMem a := by
  change a ≠ 528528#64 at h0
  change a ≠ 528536#64 at h1
  change a ≠ 528544#64 at h2
  simp [fullState,GroupedBalancedSignBottomSelectedLoad67.loadState,
    GroupedBalancedSignBottomSelectedShift67.shiftState,execInstrBr,signExtend12,
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
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedData67

end

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedAdvance67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67.image

def advanceState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x100)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.ADDI .x6 .x6 1)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x100)
  let s := execInstrBr s (.SD .x28 .x6 0)
  let s := execInstrBr s (.ADDI .x7 .x0 10)
  execInstrBr s (.BNE .x6 .x7 0x1f7c)

private theorem advance_code :
    Keygen.instructionAt image 0x1588 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x158c = some (.base (.ADDI .x28 .x28 0x100)) ∧
    Keygen.instructionAt image 0x1590 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x1594 = some (.base (.ADDI .x6 .x6 1)) ∧
    Keygen.instructionAt image 0x1598 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x159c = some (.base (.ADDI .x28 .x28 0x100)) ∧
    Keygen.instructionAt image 0x15a0 = some (.base (.SD .x28 .x6 0)) ∧
    Keygen.instructionAt image 0x15a4 = some (.base (.ADDI .x7 .x0 10)) ∧
    Keygen.instructionAt image 0x15a8 = some (.base (.BNE .x6 .x7 0x1f7c)) := by decide

theorem advance_steps (s : MachineState) (pc : s.pc = 0x1588) :
    OrdinarySteps image s 9 (advanceState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x100)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.ADDI .x6 .x6 1)
  let s5 := execInstrBr s4 (.LUI .x28 0x81)
  let s6 := execInstrBr s5 (.ADDI .x28 .x28 0x100)
  let s7 := execInstrBr s6 (.SD .x28 .x6 0)
  let s8 := execInstrBr s7 (.ADDI .x7 .x0 10)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8⟩ := advance_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 8
  · simpa [Keygen.fetch_at, execInstrBr, pc, signExtend12, signExtend13] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x100)) 7
  · simpa [Keygen.fetch_at, s1, execInstrBr, pc, signExtend12, signExtend13] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 6
  · simpa [Keygen.fetch_at, s1, s2, execInstrBr, pc, signExtend12, signExtend13] using c2
  · simp [advanceState, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, s1, s2, s3]
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x6 .x6 1)) 5
  · simpa [Keygen.fetch_at, s1, s2, s3, execInstrBr, pc, signExtend12, signExtend13] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.LUI .x28 0x81)) 4
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, execInstrBr, pc, signExtend12, signExtend13] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADDI .x28 .x28 0x100)) 3
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, execInstrBr, pc, signExtend12, signExtend13] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.SD .x28 .x6 0)) 2
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, execInstrBr, pc, signExtend12, signExtend13] using c6
  · simp [advanceState, ordinaryStep, memoryArgumentsValid, execInstrBr, signExtend12, accessValid, rangeValid, MEMORY_BYTES, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, s1, s2, s3, s4, s5, s6, s7]
  apply OrdinarySteps.step s7 s8 _ (.base (.ADDI .x7 .x0 10)) 1
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, execInstrBr, pc, signExtend12, signExtend13] using c7
  · rfl
  apply OrdinarySteps.step s8 (advanceState s) _ (.base (.BNE .x6 .x7 0x1f7c)) 0
  · simpa [Keygen.fetch_at, s1, s2, s3, s4, s5, s6, s7, s8, execInstrBr, pc, signExtend12, signExtend13] using c8
  · rfl
  exact OrdinarySteps.refl _

theorem advance_count (s : MachineState) :
    (advanceState s).getMem 0x81100 = s.getMem 0x81100 + 1 := by
  simp [advanceState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem advance_pc (s : MachineState) (pc : s.pc = 0x1588) :
    (advanceState s).pc =
      if s.getMem 0x81100 + 1 = (10 : Word) then 0x15ac else 0x1524 := by
  simp [advanceState,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem advance_frame (s : MachineState) (a : Word) (ha : a ≠ 0x81100) :
    (advanceState s).getMem a = s.getMem a := by
  change a ≠ 528640#64 at ha
  simp [advanceState,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,ha]

#print axioms advance_steps
#print axioms advance_count
#print axioms advance_pc
#print axioms advance_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomSelectedAdvance67
