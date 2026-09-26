import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWriteAfter67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Tick67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureComposeAfter67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Exit67. -/
section
/-! Complete selected-value capture control flow before each H2 call. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureComposeAfter67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev selector := GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState
private abbrev digit := GroupedBalancedSignUpperCaptureDigitAfter67.digitState
private abbrev write := GroupedBalancedSignUpperCaptureWriteAfter67.writeState

def DigitMatches (s : MachineState) : Prop :=
  (s.getByte (0x80600 + s.getMem 0x81030)).zeroExtend 64 =
    s.getReg .x21

theorem matches_selector (s : MachineState) :
    DigitMatches (selector s) ↔ DigitMatches s := by
  simp only [DigitMatches,
    GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame,
    GroupedBalancedSignUpperCaptureSelectorAfter67.selector_byte,
    GroupedBalancedSignUpperCaptureSelectorAfter67.selector_regs]

theorem unselected (s : MachineState) (pc : s.pc = 0x1a44)
    (other : s.getMem 0x810e0 ≠ s.getMem 0x810e8) :
    OrdinarySteps image s 7 (selector s) ∧
    (selector s).pc = 0x1aac ∧
    (∀ a, (selector s).getMem a = s.getMem a) := by
  refine ⟨GroupedBalancedSignUpperCaptureSelectorAfter67.selector_steps s pc,?_,?_⟩
  · rw [GroupedBalancedSignUpperCaptureSelectorAfter67.selector_pc s pc,if_pos other]
  · exact GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame s

theorem selected_unmatched (s : MachineState) (pc : s.pc = 0x1a44)
    (selected : s.getMem 0x810e0 = s.getMem 0x810e8)
    (unmatched : ¬ DigitMatches s)
    (safeDigit : accessValid (0x80600 + s.getMem 0x81030) 1 = true) :
    OrdinarySteps image s 15 (digit (selector s)) ∧
    (digit (selector s)).pc = 0x1aac ∧
    (∀ a, (digit (selector s)).getMem a = s.getMem a) := by
  have selpc : (selector s).pc = 0x1a60 := by
    rw [GroupedBalancedSignUpperCaptureSelectorAfter67.selector_pc s pc]
    change s.getMem 528608#64 = s.getMem 528616#64 at selected
    simp [selected]
  have safe' : accessValid (0x80600 + (selector s).getMem 0x81030) 1 = true := by
    simpa only [GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame] using safeDigit
  have first := GroupedBalancedSignUpperCaptureSelectorAfter67.selector_steps s pc
  have second := GroupedBalancedSignUpperCaptureDigitAfter67.digit_steps
    (selector s) selpc safe'
  refine ⟨?_,?_,?_⟩
  · have full := Keygen.ordinary_trans image s (selector s)
      (digit (selector s)) 7 8 first second
    simpa only [Nat.reduceAdd] using full
  · rw [GroupedBalancedSignUpperCaptureDigitAfter67.digit_pc _ selpc]
    have h : ¬ DigitMatches (selector s) :=
      (matches_selector s).not.mpr unmatched
    simp only [DigitMatches] at h
    rw [if_pos h]
  · intro a
    rw [GroupedBalancedSignUpperCaptureDigitAfter67.digit_frame,
      GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame]

theorem selected_matched (s : MachineState) (pc : s.pc = 0x1a44)
    (selected : s.getMem 0x810e0 = s.getMem 0x810e8)
    (matched : DigitMatches s)
    (safeDigit : accessValid (0x80600 + s.getMem 0x81030) 1 = true)
    (safeWitness : accessValid
      (GroupedBalancedSignUpperCaptureWriteAfter67.pointer (digit (selector s))) 8 = true)
    (safeWitnessNext : accessValid
      (GroupedBalancedSignUpperCaptureWriteAfter67.pointer (digit (selector s)) + 8) 8 = true) :
    OrdinarySteps image s 26 (write (digit (selector s))) ∧
    (write (digit (selector s))).pc = 0x1aac ∧
    (write (digit (selector s))).getMem
        (GroupedBalancedSignUpperCaptureWriteAfter67.pointer (digit (selector s))) =
      s.getMem 0x80020 ∧
    (write (digit (selector s))).getMem
        (GroupedBalancedSignUpperCaptureWriteAfter67.pointer (digit (selector s)) + 8) =
      s.getMem 0x80028 := by
  have selpc : (selector s).pc = 0x1a60 := by
    rw [GroupedBalancedSignUpperCaptureSelectorAfter67.selector_pc s pc]
    change s.getMem 528608#64 = s.getMem 528616#64 at selected
    simp [selected]
  have safe' : accessValid (0x80600 + (selector s).getMem 0x81030) 1 = true := by
    simpa only [GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame] using safeDigit
  have digitpc : (digit (selector s)).pc = 0x1a80 := by
    rw [GroupedBalancedSignUpperCaptureDigitAfter67.digit_pc _ selpc]
    have h : DigitMatches (selector s) := (matches_selector s).mpr matched
    simp only [DigitMatches] at h
    rw [if_neg (by simpa using h)]
  have first := GroupedBalancedSignUpperCaptureSelectorAfter67.selector_steps s pc
  have second := GroupedBalancedSignUpperCaptureDigitAfter67.digit_steps
    (selector s) selpc safe'
  have third := GroupedBalancedSignUpperCaptureWriteAfter67.write_steps
    (digit (selector s)) digitpc safeWitness safeWitnessNext
  obtain ⟨w0,w1⟩ := GroupedBalancedSignUpperCaptureWriteAfter67.write_values
    (digit (selector s))
  refine ⟨?_,GroupedBalancedSignUpperCaptureWriteAfter67.write_pc _ digitpc,?_,?_⟩
  · have mid := Keygen.ordinary_trans image s (selector s)
      (digit (selector s)) 7 8 first second
    have full := Keygen.ordinary_trans image s (digit (selector s))
      (write (digit (selector s))) 15 11
      (by simpa only [Nat.reduceAdd] using mid) third
    simpa only [Nat.reduceAdd] using full
  · rw [w0,GroupedBalancedSignUpperCaptureDigitAfter67.digit_frame,
      GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame]
  · rw [w1,GroupedBalancedSignUpperCaptureDigitAfter67.digit_frame,
      GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame]

theorem matched_high_frame (s : MachineState) (a : Word)
    (high : 0x80000 ≤ a.toNat)
    (low0 : (GroupedBalancedSignUpperCaptureWriteAfter67.pointer
      (digit (selector s))).toNat < 0x80000)
    (low1 : (GroupedBalancedSignUpperCaptureWriteAfter67.pointer
      (digit (selector s)) + 8).toNat < 0x80000) :
    (write (digit (selector s))).getMem a = s.getMem a := by
  have ne0 : a ≠ GroupedBalancedSignUpperCaptureWriteAfter67.pointer
      (digit (selector s)) := by
    intro eq
    have := congrArg BitVec.toNat eq
    omega
  have ne1 : a ≠ GroupedBalancedSignUpperCaptureWriteAfter67.pointer
      (digit (selector s)) + 8 := by
    intro eq
    have := congrArg BitVec.toNat eq
    omega
  rw [GroupedBalancedSignUpperCaptureWriteAfter67.write_frame _ a ne0 ne1,
    GroupedBalancedSignUpperCaptureDigitAfter67.digit_frame,
    GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame]

#print axioms unselected
#print axioms selected_unmatched
#print axioms selected_matched
#print axioms matched_high_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureComposeAfter67

end

/-! The H2 loop branch after the selected-value capture. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Exit67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image

def branchState (s : MachineState) : MachineState :=
  execInstrBr s (.BNE .x21 .x20 0x1f8c)

private theorem branch_code :
    Keygen.instructionAt image 0x1aac =
      some (.base (.BNE .x21 .x20 0x1f8c)) := by decide

theorem branch_steps (s : MachineState) (pc : s.pc = 0x1aac) :
    OrdinarySteps image s 1 (branchState s) := by
  apply OrdinarySteps.step s (branchState s) _
    (.base (.BNE .x21 .x20 0x1f8c)) 0
  · simpa only [Keygen.fetch_at,pc] using branch_code
  · rfl
  exact OrdinarySteps.refl _

theorem branch_fields (s : MachineState) (pc : s.pc = 0x1aac) :
    (branchState s).pc =
      (if s.getReg .x21 ≠ s.getReg .x20 then 0x1a38 else 0x1ab0) ∧
    (∀ r : Reg, (branchState s).getReg r = s.getReg r) ∧
    (∀ a : Word, (branchState s).getMem a = s.getMem a) := by
  simp [branchState, execInstrBr, pc, signExtend13]

theorem unselected (s : MachineState) (pc : s.pc = 0x1a44)
    (other : s.getMem 0x810e0 ≠ s.getMem 0x810e8) :
    ∃ final, OrdinarySteps image s 8 final ∧
      final.pc =
        (if s.getReg .x21 ≠ s.getReg .x20 then 0x1a38 else 0x1ab0) ∧
      (∀ a, final.getMem a = s.getMem a) ∧
      final = branchState
        (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s) := by
  obtain ⟨capture, capturePc, captureFrame⟩ :=
    GroupedBalancedSignUpperCaptureComposeAfter67.unselected s pc other
  let middle := GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s
  let final := branchState middle
  have branch := branch_steps middle capturePc
  have fields := branch_fields middle capturePc
  have regs := GroupedBalancedSignUpperCaptureSelectorAfter67.selector_regs s
  refine ⟨final,?_,?_,?_,rfl⟩
  · have both := Keygen.ordinary_trans image s middle final 7 1 capture branch
    simpa only [Nat.reduceAdd] using both
  · rw [fields.1,regs.2.2,regs.2.1]
  · intro a
    rw [fields.2.2 a,captureFrame]

theorem selected_unmatched (s : MachineState) (pc : s.pc = 0x1a44)
    (selected : s.getMem 0x810e0 = s.getMem 0x810e8)
    (unmatched : ¬ GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches s)
    (safeDigit : accessValid (0x80600 + s.getMem 0x81030) 1 = true) :
    ∃ final, OrdinarySteps image s 16 final ∧
      final.pc =
        (if s.getReg .x21 ≠ s.getReg .x20 then 0x1a38 else 0x1ab0) ∧
      (∀ a, final.getMem a = s.getMem a) ∧
      final = branchState
        (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
          (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s)) := by
  obtain ⟨capture, capturePc, captureFrame⟩ :=
    GroupedBalancedSignUpperCaptureComposeAfter67.selected_unmatched
      s pc selected unmatched safeDigit
  let middle := GroupedBalancedSignUpperCaptureDigitAfter67.digitState
    (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s)
  let final := branchState middle
  have branch := branch_steps middle capturePc
  have fields := branch_fields middle capturePc
  have selectorRegs := GroupedBalancedSignUpperCaptureSelectorAfter67.selector_regs s
  have digitRegs := GroupedBalancedSignUpperCaptureDigitAfter67.digit_regs
    (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s)
  refine ⟨final,?_,?_,?_,rfl⟩
  · have both := Keygen.ordinary_trans image s middle final 15 1 capture branch
    simpa only [Nat.reduceAdd] using both
  · rw [fields.1,digitRegs.2.2,selectorRegs.2.2,
      digitRegs.2.1,selectorRegs.2.1]
  · intro a
    rw [fields.2.2 a,captureFrame]

theorem selected_matched (s : MachineState) (pc : s.pc = 0x1a44)
    (selected : s.getMem 0x810e0 = s.getMem 0x810e8)
    (matched : GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches s)
    (safeDigit : accessValid (0x80600 + s.getMem 0x81030) 1 = true)
    (safeWitness : accessValid
      (GroupedBalancedSignUpperCaptureWriteAfter67.pointer
        (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
          (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s))) 8 = true)
    (safeWitnessNext : accessValid
      (GroupedBalancedSignUpperCaptureWriteAfter67.pointer
        (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
          (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s)) + 8) 8 = true) :
    ∃ final, OrdinarySteps image s 27 final ∧
      final.pc =
        (if s.getReg .x21 ≠ s.getReg .x20 then 0x1a38 else 0x1ab0) ∧
      final = branchState
        (GroupedBalancedSignUpperCaptureWriteAfter67.writeState
          (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
            (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s))) := by
  obtain ⟨capture, capturePc, _, _⟩ :=
    GroupedBalancedSignUpperCaptureComposeAfter67.selected_matched
      s pc selected matched safeDigit safeWitness safeWitnessNext
  let middle := GroupedBalancedSignUpperCaptureWriteAfter67.writeState
    (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
      (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s))
  let final := branchState middle
  have branch := branch_steps middle capturePc
  have fields := branch_fields middle capturePc
  have selectorRegs := GroupedBalancedSignUpperCaptureSelectorAfter67.selector_regs s
  have digitRegs := GroupedBalancedSignUpperCaptureDigitAfter67.digit_regs
    (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s)
  have writeRegs := GroupedBalancedSignUpperCaptureWriteAfter67.write_regs
    (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
      (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s))
  refine ⟨final,?_,?_,rfl⟩
  · have both := Keygen.ordinary_trans image s middle final 26 1 capture branch
    simpa only [Nat.reduceAdd] using both
  · rw [fields.1,writeRegs.2.2.1,digitRegs.2.2,selectorRegs.2.2,
      writeRegs.2.1,digitRegs.2.1,selectorRegs.2.1]

theorem selected_matched_high_frame (s : MachineState) (a : Word)
    (high : 0x80000 ≤ a.toNat)
    (low0 : (GroupedBalancedSignUpperCaptureWriteAfter67.pointer
      (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
        (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s))).toNat < 0x80000)
    (low1 : (GroupedBalancedSignUpperCaptureWriteAfter67.pointer
      (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
        (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s)) + 8).toNat < 0x80000) :
    (branchState
      (GroupedBalancedSignUpperCaptureWriteAfter67.writeState
        (GroupedBalancedSignUpperCaptureDigitAfter67.digitState
          (GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState s)))).getMem a =
      s.getMem a := by
  have frame := GroupedBalancedSignUpperCaptureComposeAfter67.matched_high_frame
    s a high low0 low1
  simpa [branchState,execInstrBr] using frame

#print axioms branch_steps
#print axioms branch_fields
#print axioms unselected
#print axioms selected_unmatched
#print axioms selected_matched
#print axioms selected_matched_high_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Exit67
