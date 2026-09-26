import SigGolfCandidate.Hypertree.GroupedBalancedSignImage67
import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67

/-! Signer image with the kernel-refined byte-table decoder substituted at
the existing decoder entry, PC 0x20f8. All earlier instructions are shared. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignImage67Byte
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def code : List (BitVec 32) :=
  GroupedBalancedSignImage67.code

def image : Riscv.Image := GroupedBalancedSignImage67.image

theorem code_length : code.length = 1129 :=
  GroupedBalancedSignImage67.code_length

theorem image_bytes : image.byteSize = 6820 :=
  GroupedBalancedSignImage67.image_bytes

theorem same_prefix :
    code.take 1086 = GroupedBalancedSignImage67.code.take 1086 := rfl

theorem prefix_word (i : Nat) (hi : i < 1086) :
    code[i]'(by rw [code_length]; omega) =
      GroupedBalancedSignImage67.code[i]'(by rw [GroupedBalancedSignImage67.code_length]; omega) := by
  rfl

theorem prefix_option (i : Nat) (hi : i < 1086) :
    code[i]? = GroupedBalancedSignImage67.code[i]? := by
  rfl

theorem fetch_prefix (s : MachineState)
    (low : 0x1000 ≤ s.pc.toNat) (high : s.pc.toNat < 0x20f8) :
    Riscv.fetch image s = Riscv.fetch GroupedBalancedSignImage67.image s := by
  rfl

theorem decoder_entry :
    code[1086]'(by rw [code_length]; decide) =
      GroupedBalancedDecoderByte67.code[0]'(by rw [GroupedBalancedDecoderByte67.code_length]; decide) := by
  decide

theorem data_base : Riscv.dataBase image = 0xfff700 := by
  simp only [Riscv.dataBase, image, GroupedBalancedSignImage67.image,
    GroupedBalancedDecoderByte67.data_length, SigGolf.MEMORY_BYTES]
  decide

theorem image_valid :
    image.Valid ⟨50848, 50848⟩ (Riscv.standardLayout ⟨50848, 50848⟩) := by
  exact GroupedBalancedSignImage67.image_valid

#print axioms same_prefix
#print axioms fetch_prefix
#print axioms image_valid
end SigGolfCandidate.Hypertree.GroupedBalancedSignImage67Byte
