import SigGolf
import SigGolfCandidate.Hypertree.GroupedBalancedKeygenImage67
import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyImage67Fast2


/-! Witness-copy image for the 50,848-byte direct signature. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedExpandImage67
open SigGolf

def code : List (BitVec 32) := [
  0x00020337, 0x06030313, 0x0002c3b7, 0x70038393, 0x00002537, 0x8d450513, 0x00033583, 0x00b3b023,
  0x00830313, 0x00838393, 0xfff50513, 0xfe0516e3, 0x00000293, 0x00100513, 0x00000073
]

def image : Riscv.Image where
  code := code
  data := []

theorem code_length : code.length = 15 := by decide

theorem image_bytes : image.byteSize = 60 := by
  simp [image, Riscv.Image.byteSize, code_length]

theorem image_valid :
    image.Valid ⟨50848, 50848⟩ (Riscv.standardLayout ⟨50848, 50848⟩) := by
  have base : Riscv.dataBase image = 16777216 := by
    simp [Riscv.dataBase, image, MEMORY_BYTES]
  constructor
  · rw [image_bytes]
    decide
  · unfold Riscv.layoutValid
    rw [base]
    decide

end SigGolfCandidate.Hypertree.GroupedBalancedExpandImage67


/-! Concrete four-image assembly for the direct 67-chain candidate.
It remains separate from the accepted submission while execution, security,
and scored-cycle refinements are proved. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedProgram67
open SigGolf
set_option maxRecDepth 8192

def sizes : Sizes := ⟨50848, 50848⟩

def submission : Submission where
  sizes := sizes
  layout := Riscv.standardLayout sizes
  image
    | .keygen => GroupedBalancedKeygenImage67.image
    | .sign => GroupedBalancedSignImage67.image
    | .expand => GroupedBalancedExpandImage67.image
    | .verify => GroupedBalancedVerifyImage67Fast2.image

theorem admissible : submission.Admissible := by
  constructor
  · change 1 ≤ 50848 ∧ 50848 ≤ MAX_WITNESS_BYTES
    decide
  · intro phase
    cases phase with
    | keygen => exact GroupedBalancedKeygenImage67.image_valid
    | sign => exact GroupedBalancedSignImage67.image_valid
    | expand => exact GroupedBalancedExpandImage67.image_valid
    | verify => exact GroupedBalancedVerifyImage67Fast2.image_valid

end SigGolfCandidate.Hypertree.GroupedBalancedProgram67
