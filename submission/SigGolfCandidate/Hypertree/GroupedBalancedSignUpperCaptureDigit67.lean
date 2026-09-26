import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Prepared67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureSelector67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureDigit67. -/
section
/-! Skip the witness capture unless this is the selected upper leaf. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureSelector67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def selectorState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe0)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0xe8)
  let s := execInstrBr s (.LD .x7 .x28 0)
  execInstrBr s (.BNE .x6 .x7 0x50)

private theorem selector_code :
    Keygen.instructionAt image 0x19d0 = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x19d4 = some (.base (.ADDI .x28 .x28 0xe0)) ∧
    Keygen.instructionAt image 0x19d8 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x19dc = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x19e0 = some (.base (.ADDI .x28 .x28 0xe8)) ∧
    Keygen.instructionAt image 0x19e4 = some (.base (.LD .x7 .x28 0)) ∧
    Keygen.instructionAt image 0x19e8 = some (.base (.BNE .x6 .x7 0x50)) := by decide

theorem selector_steps (s : MachineState) (pc : s.pc = 0x19d0) :
    OrdinarySteps image s 7 (selectorState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0xe0)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x28 0x81)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 0xe8)
  let s6 := execInstrBr s5 (.LD .x7 .x28 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6⟩ := selector_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 6
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0xe0)) 5
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 4
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · have haddr : s2.getReg .x28 = 0x810e0 := by
      simp [s1,s2,execInstrBr,signExtend12,MachineState.getReg_setReg_eq]
    change (if accessValid (s2.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s3 else none) = some s3
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x28 0x81)) 3
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x28 .x28 0xe8)) 2
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.LD .x7 .x28 0)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,execInstrBr,pc] using c5
  · have haddr : s5.getReg .x28 = 0x810e8 := by
      simp [s1,s2,s3,s4,s5,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    change (if accessValid (s5.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s6 else none) = some s6
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s6 (selectorState s) _ (.base (.BNE .x6 .x7 0x50)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,execInstrBr,pc] using c6
  · rfl
  exact OrdinarySteps.refl _

theorem selector_pc (s : MachineState) (pc : s.pc = 0x19d0) :
    (selectorState s).pc =
      if s.getMem 0x810e0 ≠ s.getMem 0x810e8 then 0x1a38 else 0x19ec := by
  simp [selectorState,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem selector_frame (s : MachineState) (a : Word) :
    (selectorState s).getMem a = s.getMem a := by
  simp [selectorState,execInstrBr]

theorem selector_byte (s : MachineState) (a : Word) :
    (selectorState s).getByte a = s.getByte a := by
  simp only [MachineState.getByte,selector_frame]

theorem selector_regs (s : MachineState) :
    (selectorState s).getReg .x19 = s.getReg .x19 ∧
    (selectorState s).getReg .x20 = s.getReg .x20 ∧
    (selectorState s).getReg .x21 = s.getReg .x21 := by
  simp [selectorState,execInstrBr,MachineState.getReg_setReg_ne]

#print axioms selector_steps
#print axioms selector_pc
#print axioms selector_byte
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureSelector67

end

/-! Compare the selected witness digit against the current H2 step. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureDigit67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

private theorem getByte_setPC (s : MachineState) (pc a : Word) :
    (s.setPC pc).getByte a = s.getByte a := by
  simp [MachineState.getByte]

def digitState (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LUI .x28 0x81)
  let s := execInstrBr s (.ADDI .x28 .x28 0x30)
  let s := execInstrBr s (.LD .x6 .x28 0)
  let s := execInstrBr s (.LUI .x7 0x80)
  let s := execInstrBr s (.ADDI .x7 .x7 0x600)
  let s := execInstrBr s (.ADD .x7 .x7 .x6)
  let s := execInstrBr s (.LBU .x7 .x7 0)
  execInstrBr s (.BNE .x7 .x21 0x30)

private theorem digit_code :
    Keygen.instructionAt image 0x19ec = some (.base (.LUI .x28 0x81)) ∧
    Keygen.instructionAt image 0x19f0 = some (.base (.ADDI .x28 .x28 0x30)) ∧
    Keygen.instructionAt image 0x19f4 = some (.base (.LD .x6 .x28 0)) ∧
    Keygen.instructionAt image 0x19f8 = some (.base (.LUI .x7 0x80)) ∧
    Keygen.instructionAt image 0x19fc = some (.base (.ADDI .x7 .x7 0x600)) ∧
    Keygen.instructionAt image 0x1a00 = some (.base (.ADD .x7 .x7 .x6)) ∧
    Keygen.instructionAt image 0x1a04 = some (.base (.LBU .x7 .x7 0)) ∧
    Keygen.instructionAt image 0x1a08 = some (.base (.BNE .x7 .x21 0x30)) := by decide

theorem digit_steps (s : MachineState) (pc : s.pc = 0x19ec)
    (safe : accessValid (0x80600 + s.getMem 0x81030) 1 = true) :
    OrdinarySteps image s 8 (digitState s) := by
  let s1 := execInstrBr s (.LUI .x28 0x81)
  let s2 := execInstrBr s1 (.ADDI .x28 .x28 0x30)
  let s3 := execInstrBr s2 (.LD .x6 .x28 0)
  let s4 := execInstrBr s3 (.LUI .x7 0x80)
  let s5 := execInstrBr s4 (.ADDI .x7 .x7 0x600)
  let s6 := execInstrBr s5 (.ADD .x7 .x7 .x6)
  let s7 := execInstrBr s6 (.LBU .x7 .x7 0)
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩ := digit_code
  apply OrdinarySteps.step s s1 _ (.base (.LUI .x28 0x81)) 7
  · simpa only [Keygen.fetch_at,pc] using c0
  · rfl
  apply OrdinarySteps.step s1 s2 _ (.base (.ADDI .x28 .x28 0x30)) 6
  · simpa [Keygen.fetch_at,s1,execInstrBr,pc] using c1
  · rfl
  apply OrdinarySteps.step s2 s3 _ (.base (.LD .x6 .x28 0)) 5
  · simpa [Keygen.fetch_at,s1,s2,execInstrBr,pc] using c2
  · have haddr : s2.getReg .x28 = 0x81030 := by
      simp [s1,s2,execInstrBr,signExtend12,MachineState.getReg_setReg_eq]
    change (if accessValid (s2.getReg .x28 + signExtend12 (0 : BitVec 12)) 8
      then some s3 else none) = some s3
    simp [haddr,signExtend12,accessValid,rangeValid,MEMORY_BYTES]
  apply OrdinarySteps.step s3 s4 _ (.base (.LUI .x7 0x80)) 4
  · simpa [Keygen.fetch_at,s1,s2,s3,execInstrBr,pc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x7 .x7 0x600)) 3
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,execInstrBr,pc] using c4
  · rfl
  apply OrdinarySteps.step s5 s6 _ (.base (.ADD .x7 .x7 .x6)) 2
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,execInstrBr,pc] using c5
  · rfl
  apply OrdinarySteps.step s6 s7 _ (.base (.LBU .x7 .x7 0)) 1
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,execInstrBr,pc] using c6
  · change (if accessValid (s6.getReg .x7 + signExtend12 (0 : BitVec 12)) 1
      then some s7 else none) = some s7
    have haddr : s6.getReg .x7 = 0x80600 + s.getMem 0x81030 := by
      simp [s1,s2,s3,s4,s5,s6,execInstrBr,signExtend12,
        MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]
    simpa [haddr,signExtend12] using safe
  apply OrdinarySteps.step s7 (digitState s) _ (.base (.BNE .x7 .x21 0x30)) 0
  · simpa [Keygen.fetch_at,s1,s2,s3,s4,s5,s6,s7,execInstrBr,pc] using c7
  · rfl
  exact OrdinarySteps.refl _

theorem digit_pc (s : MachineState) (pc : s.pc = 0x19ec) :
    (digitState s).pc =
      if (s.getByte (0x80600 + s.getMem 0x81030)).zeroExtend 64 ≠
          s.getReg .x21 then 0x1a38 else 0x1a0c := by
  simp [digitState,execInstrBr,signExtend12,signExtend13,pc,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
    SigGolfCandidate.Memory.getByte_setReg,getByte_setPC]

theorem digit_frame (s : MachineState) (a : Word) :
    (digitState s).getMem a = s.getMem a := by
  simp [digitState,execInstrBr]

theorem digit_regs (s : MachineState) :
    (digitState s).getReg .x19 = s.getReg .x19 ∧
    (digitState s).getReg .x20 = s.getReg .x20 ∧
    (digitState s).getReg .x21 = s.getReg .x21 := by
  simp [digitState,execInstrBr,MachineState.getReg_setReg_ne]

#print axioms digit_steps
#print axioms digit_pc
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureDigit67
