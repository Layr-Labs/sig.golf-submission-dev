import SigGolfCandidate.Hypertree.GroupedBalancedProgram67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyImage67Fast2Byte

/-! The direct 67-chain candidate with the table decoder in its verifier. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedProgram67Byte
open SigGolf
set_option maxRecDepth 8192

def submission : Submission where
  sizes := GroupedBalancedProgram67.sizes
  layout := Riscv.standardLayout GroupedBalancedProgram67.sizes
  image
    | .keygen => GroupedBalancedKeygenImage67.image
    | .sign => GroupedBalancedSignImage67.image
    | .expand => GroupedBalancedExpandImage67.image
    | .verify => GroupedBalancedVerifyImage67Fast2Byte.image

theorem admissible : submission.Admissible := by
  constructor
  · change 1 ≤ 50848 ∧ 50848 ≤ MAX_WITNESS_BYTES
    decide
  · intro phase
    cases phase with
    | keygen => exact GroupedBalancedKeygenImage67.image_valid
    | sign => exact GroupedBalancedSignImage67.image_valid
    | expand => exact GroupedBalancedExpandImage67.image_valid
    | verify => exact GroupedBalancedVerifyImage67Fast2Byte.image_valid

end SigGolfCandidate.Hypertree.GroupedBalancedProgram67Byte
