import SigGolfCandidate.Hypertree.BalancedPatchRefinesCore

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Expansion
set_option maxRecDepth 4096

theorem flip_checksum_nat (message : Reference.Digest)
    (flip : Reference.needsFlip message) :
    301 - (301 - Reference.rawSum message) = Reference.checksum message := by
  rw [Reference.checksum_of_flip message flip]
  have h := Balanced.raw_sum_le message
  omega

theorem patch_refines_flip (image : Image) (entry start : Word) (forward back : BitVec 21)
    (code : PatchCode image entry start forward back)
    (s : MachineState) (message : Reference.Digest)
    (pc : s.pc = entry)
    (forwardPC : entry + signExtend21 forward = start)
    (backPC : start+144+signExtend21 back = entry+4)
    (sum : s.getReg .x12 = BitVec.ofNat 64 (301 - Reference.rawSum message))
    (rawDigits : ∀ i : Fin 43,
      s.getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.messageDigit message i))
    (flip : Reference.needsFlip message) :
    ∃ final,
      OrdinarySteps image s 38 final ∧
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
  have hc : ¬ 301 - Reference.rawSum message < 151 := by
    have h := (Reference.needsFlip_iff_rawChecksum_gt_150 message).mp flip
    omega
  obtain ⟨steps,pcFinal,sumFinal⟩ :=
    flip_block image entry start forward back code s pc forwardPC backPC
      (301 - Reference.rawSum message) (Nat.sub_le _ _) sum hc
  have checksum : (flipResult s forward back).getReg .x12 =
      BitVec.ofNat 64 (Reference.checksum message) :=
    sumFinal.trans (congrArg (BitVec.ofNat 64) (flip_checksum_nat message flip))
  have low := flipResult_low s forward back
  have x10 := flipResult_x10 s forward back
  have ra := flipResult_ra s forward back
  have sp := flipResult_sp s forward back
  have payload : ∀ i : Fin 43,
      (flipResult s forward back).getByte (BitVec.ofNat 64 (0x80600+i.val)) =
        BitVec.ofNat 8 (Reference.payloadDigit message i) := by
    intro i
    exact flipResult_byte s forward back message rawDigits flip i
  have frame : ∀ a, (∀ i : Fin 43, a ≠ BitVec.ofNat 64 (0x80600+i.val)) →
      (flipResult s forward back).getByte a = s.getByte a := by
    intro a outside
    exact flipResult_frame s forward back a outside
  exact ⟨flipResult s forward back, steps, pcFinal, checksum, low, x10, ra, sp, payload, frame⟩

#print axioms patch_refines_flip
end SigGolfCandidate.Hypertree.Signing
