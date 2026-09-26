import SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreePost67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperIndexedInitial67

/-! The verifier decodes the current two-word root and returns at PC 0x1518. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeDecoderHandoff67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedVerifyImage67Fast2Byte.image

def currentRoot (s : MachineState) : Reference.Digest :=
  s.getMem 0x80508 ++ s.getMem 0x80500

theorem root_words (s : MachineState) :
    ∀ half : Fin 2,
      s.getMem (Signing.wordAddress 0x80500 half.val) =
        (currentRoot s).extractLsb' (64*half.val) 64 := by
  intro half
  fin_cases half
  · change s.getMem 0x80500 =
      (s.getMem 0x80508 ++ s.getMem 0x80500).extractLsb' 0 64
    exact BitVec.extractLsb'_append_eq_right.symm
  · change s.getMem 0x80508 =
      (s.getMem 0x80508 ++ s.getMem 0x80500).extractLsb' 64 64
    exact BitVec.extractLsb'_append_eq_left.symm

theorem root_bytes (s : MachineState) :
    ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        (currentRoot s).extractLsb' (8*j.val) 8 :=
  GroupedBalancedByteFastDigestBytes67.digest_words_bytes s (currentRoot s) (root_words s)

theorem decode_from_call (s : MachineState)
    (pc : s.pc = 0x1a4c)
    (stack : s.getReg .x2 = 0xfff700)
    (link : s.getReg .x1 = 0x1518)
    (tables : GroupedBalancedVerifyByteContract67.Tables s) :
    let message := currentRoot s
    OrdinarySteps image s
      (8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6)
      (GroupedBalancedVerifyByteFull67.fullDecoderState s message) ∧
    (∀ chain : Fin 67,
      (GroupedBalancedVerifyByteFull67.fullDecoderState s message).getByte
        (BitVec.ofNat 64 (0x80600+chain.val)) =
      BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val) ∧
    (GroupedBalancedVerifyByteFull67.fullDecoderState s message).pc = 0x1518 ∧
    GroupedBalancedVerifyByteContract67.Tables
      (GroupedBalancedVerifyByteFull67.fullDecoderState s message) := by
  exact GroupedBalancedVerifyByteContract67.decoder_contract s (currentRoot s)
    pc stack link (root_bytes s) tables

#print axioms decode_from_call
end SigGolfCandidate.Hypertree.GroupedBalancedVerifyTreeDecoderHandoff67
