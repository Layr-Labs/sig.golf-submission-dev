import SigGolfCandidate.Hypertree.GroupedBalancedVerifyImage67Fast2
import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67

/-! Functional splice of the byte-table decoder into the full prototype
verifier. The call target remains at word 659; only the callee and embedded
table change. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyImage67Fast2Byte
open SigGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def code : List (BitVec 32) :=
  GroupedBalancedVerifyImage67Fast2.code.take 659 ++
  GroupedBalancedDecoderByte67.code.take 42 ++
  [0x00008067]

def image : Riscv.Image where
  code := code
  data := GroupedBalancedDecoderByte67.data

theorem code_length : code.length = 702 := by
  simp [code, GroupedBalancedVerifyImage67Fast2.code_length,
    GroupedBalancedDecoderByte67.code_length]

theorem image_bytes : image.byteSize = 5112 := by
  simp only [image, Riscv.Image.byteSize, code_length,
    GroupedBalancedDecoderByte67.data_length]

theorem image_valid :
    image.Valid ⟨50848, 50848⟩ (Riscv.standardLayout ⟨50848, 50848⟩) := by
  have base : Riscv.dataBase image = 0xfff700 := by
    simp [Riscv.dataBase, image, GroupedBalancedDecoderByte67.data_length,
      MEMORY_BYTES]
  constructor
  · rw [image_bytes]
    decide
  · unfold Riscv.layoutValid
    rw [base]
    decide

#print axioms image_valid
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyImage67Fast2Byte
