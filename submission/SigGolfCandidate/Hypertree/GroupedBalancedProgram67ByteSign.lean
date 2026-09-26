import SigGolfCandidate.Hypertree.GroupedBalancedProgram67Byte
import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67Byte

/-! Isolated full direct67 candidate with the checked byte decoder in both images. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
open SigGolf
set_option maxRecDepth 8192

def submission : Submission where
  sizes := GroupedBalancedProgram67.sizes
  layout := Riscv.standardLayout GroupedBalancedProgram67.sizes
  image
    | .keygen => GroupedBalancedKeygenImage67.image
    | .sign => GroupedBalancedSignImage67Byte.image
    | .expand => GroupedBalancedExpandImage67.image
    | .verify => GroupedBalancedVerifyImage67Fast2Byte.image

theorem admissible : submission.Admissible := by
  constructor
  · change 1 ≤ 50848 ∧ 50848 ≤ MAX_WITNESS_BYTES
    decide
  · intro phase
    cases phase with
    | keygen => exact GroupedBalancedKeygenImage67.image_valid
    | sign => exact GroupedBalancedSignImage67Byte.image_valid
    | expand => exact GroupedBalancedExpandImage67.image_valid
    | verify => exact GroupedBalancedVerifyImage67Fast2Byte.image_valid

#print axioms admissible
end SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
