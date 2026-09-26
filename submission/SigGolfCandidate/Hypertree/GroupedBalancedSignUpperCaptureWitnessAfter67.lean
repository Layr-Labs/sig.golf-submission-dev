import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperH2CaptureAny67

/-! Exact low witness-memory effect of the post-hash prefix capture. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWitnessAfter67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
private noncomputable abbrev result := GroupedBalancedSignUpperH2CaptureAny67.captureResult
private abbrev selector := GroupedBalancedSignUpperCaptureSelectorAfter67.selectorState
private abbrev digit := GroupedBalancedSignUpperCaptureDigitAfter67.digitState
private abbrev write := GroupedBalancedSignUpperCaptureWriteAfter67.writeState
private abbrev branch := GroupedBalancedSignUpperH2Exit67.branchState

def target (s : MachineState) : Word :=
  GroupedBalancedSignUpperCaptureWriteAfter67.pointer (digit (selector s))

noncomputable def expectedMem (s : MachineState) (a : Word) : Word := by
  classical
  exact if s.getMem 0x810e0 = s.getMem 0x810e8 ∧
      GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches s then
    if a = target s + 8 then s.getMem 0x80028
    else if a = target s then s.getMem 0x80020
    else s.getMem a
  else s.getMem a

theorem capture_mem (s : MachineState) (a : Word) :
    (result s).getMem a = expectedMem s a := by
  classical
  by_cases selected : s.getMem 0x810e0 = s.getMem 0x810e8
  · by_cases matched :
        GroupedBalancedSignUpperCaptureComposeAfter67.DigitMatches s
    · change s.getMem 528608#64 = s.getMem 528616#64 at selected
      simp [expectedMem,selected,matched]
      simp [result,GroupedBalancedSignUpperH2CaptureAny67.captureResult,
        selected,matched,target,branch,
        GroupedBalancedSignUpperH2Exit67.branchState,
        GroupedBalancedSignUpperCaptureWriteAfter67.write_mem,
        GroupedBalancedSignUpperCaptureDigitAfter67.digit_frame,
        GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame,
        execInstrBr]
      rfl
    · change s.getMem 528608#64 = s.getMem 528616#64 at selected
      simp [expectedMem,selected,matched]
      simp [result,GroupedBalancedSignUpperH2CaptureAny67.captureResult,
        selected,matched,branch,
        GroupedBalancedSignUpperH2Exit67.branchState,
        GroupedBalancedSignUpperCaptureDigitAfter67.digit_frame,
        GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame,
        execInstrBr]
  · change s.getMem 528608#64 ≠ s.getMem 528616#64 at selected
    simp [expectedMem,selected]
    simp [result,GroupedBalancedSignUpperH2CaptureAny67.captureResult,
      selected,branch,
      GroupedBalancedSignUpperH2Exit67.branchState,
      GroupedBalancedSignUpperCaptureSelectorAfter67.selector_frame,
      execInstrBr]

#print axioms capture_mem
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperCaptureWitnessAfter67
