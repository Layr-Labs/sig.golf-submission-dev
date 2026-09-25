import SigGolfCandidate.Hypertree.BalancedPatchRefinesCore

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

theorem patch_no_flip_refines (image : Image) (entry start : Word)
    (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (message : Reference.Digest)
    (pc : s.pc = entry)
    (forwardPC : entry + signExtend21 forward = start)
    (backPC : start+144+signExtend21 back = entry+4)
    (sum : s.getReg .x12 = BitVec.ofNat 64 (301 - Reference.rawSum message))
    (rawDigits : ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i))
    (noFlip : ¬Reference.needsFlip message) :
    OrdinarySteps image s 6 (noFlipResult s forward back) ∧
    (noFlipResult s forward back).pc = entry+4 ∧
    (noFlipResult s forward back).getReg .x12 =
      BitVec.ofNat 64 (Reference.checksum message) ∧
    (noFlipResult s forward back).getReg .x13 =
      (noFlipResult s forward back).getReg .x12 &&& 7 ∧
    (noFlipResult s forward back).getReg .x10 = s.getReg .x10 ∧
    (noFlipResult s forward back).getReg .x1 = s.getReg .x1 ∧
    (noFlipResult s forward back).getReg .x2 = s.getReg .x2 ∧
    (∀ i : Fin 43,
      (noFlipResult s forward back).getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.payloadDigit message i)) ∧
    (∀ a, (∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600+i.val)) →
      (noFlipResult s forward back).getByte a = s.getByte a) := by
  have hc : 301 - Reference.rawSum message < 151 := by
    have h := Reference.needsFlip_iff_rawChecksum_gt_150 message
    have nh : ¬150 < 301 - Reference.rawSum message := fun x => noFlip (h.mpr x)
    omega
  obtain ⟨steps,pcFinal,sumFinal,lowFinal,frame,ptr,ra,sp⟩ :=
    noFlip_block image entry start forward back code s pc forwardPC backPC
      (301 - Reference.rawSum message) (Nat.sub_le _ _) sum hc
  refine ⟨steps,pcFinal,?_,?_,ptr,ra,sp,?_,?_⟩
  · simpa only [Reference.checksum_of_no_flip message noFlip] using sumFinal
  · rw [lowFinal,sumFinal]
  · intro i
    rw [frame]
    exact rawDigits_payload_no_flip s message rawDigits noFlip i
  · intro a _; exact frame a

end SigGolfCandidate.Hypertree.Signing
