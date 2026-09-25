import SigGolfCandidate.Hypertree.GroupedUniformMaterialized
import SigGolf

namespace SigGolfCandidate.Hypertree.GroupedUniformDecoderImage
open SigGolf

/-- Standalone 52-digit RV64 greedy decoder. Input rank is at 0x80500,
output digit bytes begin at 0x80600. PC 0x1000 is the entry. -/
def code : List (BitVec 32) := [
    0x00080e37, 0x500e0e13, 0x000e3303, 0x008e3383, 0x00080537, 0x60050513, 0x09300593,
    0x03400613, 0x010006b7, 0xfb068693, 0x00001737, 0x94070713, 0x00600813, 0x00100a13,
    0x00000793, 0x06f5e063, 0x0006b883, 0x0086b903, 0x0323e663, 0x00796463, 0x03136263,
    0x011339b3, 0x41130333, 0x412383b3, 0x413383b3, 0xff068693, 0x00178793, 0xfd07e8e3,
    0x02c0006f, 0x00f50023, 0x00150513, 0x40f585b3, 0x40e686b3, 0xfff60613, 0xfb4618e3,
    0x00b50023, 0x00000293, 0x00100513, 0x00000073, 0x00000293, 0x00000513, 0x00000073]

def image : Riscv.Image where
  code := code
  data := GroupedUniformMaterialized.data

theorem code_length : code.length = 42 := by decide

theorem encoded_bytes : 4 * code.length + GroupedUniformTableLayout.totalBytes = 123368 := by
  rw [code_length]
  decide

theorem all_words_decode :
    ∀ i : Fin 42, Riscv.decodeInstruction
      (code[i.val]'(by rw [code_length]; exact i.isLt)) ≠ none := by
  intro i
  fin_cases i <;> decide

end SigGolfCandidate.Hypertree.GroupedUniformDecoderImage
