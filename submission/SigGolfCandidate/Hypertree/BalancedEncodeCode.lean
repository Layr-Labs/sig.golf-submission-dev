import SigGolfCandidate.Hypertree.BalancedPatchRest

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

def EncodePatchCode (image : Image) (base : Word) : Prop :=
  ∃ (start : Word) (forward back : BitVec 21),
    PatchCode image (base+88) start forward back ∧
    base+88+signExtend21 forward = start ∧
    start+144+signExtend21 back = base+92

theorem sign_encode_patch_code : EncodePatchCode sign 0x1340 := by
  refine ⟨0x1c70, 0x8d8, -2404, sign_patch_code, ?_, ?_⟩ <;> decide

theorem verify_encode_patch_code : EncodePatchCode verify 0x1268 := by
  refine ⟨0x1948, 0x688, -1812, verify_patch_code, ?_, ?_⟩ <;> decide

theorem sign_checksum_rest_code : ChecksumRestCode sign 0x139c := by
  intro s i pc
  simp only [fetch,pc]
  fin_cases i <;> decide

theorem verify_checksum_rest_code : ChecksumRestCode verify 0x12c4 := by
  intro s i pc
  simp only [fetch,pc]
  fin_cases i <;> decide

end SigGolfCandidate.Hypertree.Signing
