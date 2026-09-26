import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2Exit67

/-! Uniform bounded capture/branch step after any upper WOTS H2 answer. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2CaptureAny67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private abbrev image := GroupedBalancedSignImage67Byte.image
private abbrev selector := GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState
private abbrev digit := GroupedBalancedSignUpperCaptureDigitAfter67.digitState
private abbrev write := GroupedBalancedSignUpperCaptureWriteAfter67.writeState
private abbrev branch := GroupedBalancedSignUpperH2Exit67.branchState
private abbrev pointer := GroupedBalancedSignUpperCaptureWriteAfter67.pointer

noncomputable def captureResult (s : MachineState) : MachineState := by
  classical
  exact if s.getMem 0x810e0 = s.getMem 0x810e8 then
    if GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches s then
      branch (write (digit (selector s)))
    else branch (digit (selector s))
  else branch (selector s)

theorem capture_pointer (s : MachineState) :
    pointer (digit (selector s)) =
      s.getMem 0x810f0 + (s.getMem 0x81030 <<< 4) := by
  simp [pointer,GroupedBalancedSignUpperCaptureWriteAfter67.pointer,
    digit,GroupedBalancedSignUpperCaptureDigitAfter67.digitState,
    selector,GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState,
    execInstrBr,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,
    GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame,
    GroupedBalancedSignUpperCaptureDigitAfter67.digit_frame,
    signExtend12]

theorem capture_any (s : MachineState) (pc : s.pc = 0x1a44)
    (safeDigit : accessValid (0x80600 + s.getMem 0x81030) 1 = true)
    (safeWitness : accessValid (pointer (digit (selector s))) 8 = true)
    (safeWitnessNext : accessValid (pointer (digit (selector s)) + 8) 8 = true)
    (low0 : (pointer (digit (selector s))).toNat < 0x80000)
    (low1 : (pointer (digit (selector s)) + 8).toNat < 0x80000) :
    ∃ (n : Nat) (final : MachineState),
      OrdinarySteps image s n final ∧ n ≤ 27 ∧
      final.pc =
        (if s.getReg .x21 ≠ s.getReg .x20 then 0x1a38 else 0x1ab0) ∧
      (∀ a : Word, 0x80000 ≤ a.toNat → final.getMem a = s.getMem a) ∧
      final = captureResult s := by
  by_cases selected : s.getMem 0x810e0 = s.getMem 0x810e8
  · by_cases matched :
        GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches s
    · obtain ⟨final,path,pcFinal,finalEq⟩ :=
        GroupedBalancedSignUpperH2Exit67.selected_matched s pc selected matched
          safeDigit safeWitness safeWitnessNext
      refine ⟨27,final,path,by decide,pcFinal,?_,?_⟩
      · intro a high
        rw [finalEq]
        exact GroupedBalancedSignUpperH2Exit67.selected_matched_high_frame
          s a high low0 low1
      · rw [finalEq]
        change s.getMem 528608#64 = s.getMem 528616#64 at selected
        simp [captureResult,selected,matched]
    · obtain ⟨final,path,pcFinal,frame,finalEq⟩ :=
        GroupedBalancedSignUpperH2Exit67.selected_unmatched s pc selected
          matched safeDigit
      refine ⟨16,final,path,by decide,pcFinal,fun a _ => frame a,?_⟩
      rw [finalEq]
      change s.getMem 528608#64 = s.getMem 528616#64 at selected
      simp [captureResult,selected,matched]
  · obtain ⟨final,path,pcFinal,frame,finalEq⟩ :=
      GroupedBalancedSignUpperH2Exit67.unselected s pc selected
    refine ⟨8,final,path,by decide,pcFinal,fun a _ => frame a,?_⟩
    rw [finalEq]
    change s.getMem 528608#64 ≠ s.getMem 528616#64 at selected
    simp [captureResult,selected]

theorem capture_regs (s : MachineState) :
    (captureResult s).getReg .x5 = s.getReg .x5 ∧
    (captureResult s).getReg .x10 = s.getReg .x10 ∧
    (captureResult s).getReg .x11 = s.getReg .x11 ∧
    (captureResult s).getReg .x12 = s.getReg .x12 ∧
    (captureResult s).getReg .x19 = s.getReg .x19 ∧
    (captureResult s).getReg .x20 = s.getReg .x20 ∧
    (captureResult s).getReg .x21 = s.getReg .x21 := by
  classical
  unfold captureResult
  split_ifs <;>
    simp [branch,selector,digit,write,
      GroupedBalancedSignUpperH2Exit67.branchState,
      GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState,
      GroupedBalancedSignUpperCaptureDigitAfter67.digitState,
      GroupedBalancedSignUpperCaptureWriteAfter67.writeState,
      execInstrBr,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem capture_stack (s : MachineState) :
    (captureResult s).getReg .x2 = s.getReg .x2 := by
  classical
  unfold captureResult
  split_ifs <;>
    simp [branch,selector,digit,write,
      GroupedBalancedSignUpperH2Exit67.branchState,
      GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState,
      GroupedBalancedSignUpperCaptureDigitAfter67.digitState,
      GroupedBalancedSignUpperCaptureWriteAfter67.writeState,
      execInstrBr,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]

theorem capture_high_frame (s : MachineState) (a : Word)
    (high : 0x80000 ≤ a.toNat)
    (low0 : (pointer (digit (selector s))).toNat < 0x80000)
    (low1 : (pointer (digit (selector s)) + 8).toNat < 0x80000) :
    (captureResult s).getMem a = s.getMem a := by
  classical
  by_cases selected : s.getMem 0x810e0 = s.getMem 0x810e8
  · change s.getMem 528608#64 = s.getMem 528616#64 at selected
    by_cases matched : GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches s
    · simpa [captureResult,selected,matched] using
        GroupedBalancedSignUpperH2Exit67.selected_matched_high_frame
          s a high low0 low1
    · simp [captureResult,selected,matched,
        GroupedBalancedSignUpperH2Exit67.branchState,execInstrBr,
        GroupedBalancedSignUpperCaptureDigitAfter67.digit_frame,
        GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame]
  · change s.getMem 528608#64 ≠ s.getMem 528616#64 at selected
    simp [captureResult,selected,
      GroupedBalancedSignUpperH2Exit67.branchState,execInstrBr,
      GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame]

#print axioms capture_any
#print axioms capture_pointer
#print axioms capture_regs
#print axioms capture_high_frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2CaptureAny67
