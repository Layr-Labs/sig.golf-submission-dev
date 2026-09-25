import SigGolfCandidate.Hypertree.BalancedPatchRefinesCore
import SigGolfCandidate.Hypertree.BalancedPatchFlipRefines
import SigGolfCandidate.Hypertree.BalancedPatchNoFlipRefines

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

theorem patch_refines (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (message : Reference.Digest)
    (pc : s.pc = entry)
    (forwardPC : entry + signExtend21 forward = start)
    (backPC : start+144+signExtend21 back = entry+4)
    (sum : s.getReg .x12 = BitVec.ofNat 64 (301 - Reference.rawSum message))
    (rawDigits : ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i)) :
    ∃ final,
      OrdinarySteps image s (if Reference.needsFlip message then 38 else 6) final ∧
      final.pc = entry+4 ∧
      final.getReg .x12 = BitVec.ofNat 64 (Reference.checksum message) ∧
      final.getReg .x13 = final.getReg .x12 &&& 7 ∧
      final.getReg .x10 = s.getReg .x10 ∧
      final.getReg .x1 = s.getReg .x1 ∧
      final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 43,
        final.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
          BitVec.ofNat 8 (Reference.payloadDigit message i)) ∧
      (∀ a, (∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600+i.val)) →
        final.getByte a = s.getByte a) := by
  by_cases flip : Reference.needsFlip message
  · obtain ⟨final, fields⟩ := patch_refines_flip image entry start forward back
      code s message pc forwardPC backPC sum rawDigits flip
    exact ⟨final, by simpa only [if_pos flip] using fields⟩
  · have fields := patch_no_flip_refines image entry start forward back
      code s message pc forwardPC backPC sum rawDigits flip
    exact ⟨noFlipResult s forward back, by simpa only [if_neg flip] using fields⟩

end SigGolfCandidate.Hypertree.Signing
