import SigGolfCandidate.Hypertree.GroupedBalancedSignByteCompose67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteFull67

/-! Inlined from SigGolfCandidate.Hypertree.GroupedBalancedSignByteDigits67; its only importer was SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullDigits67. -/
section
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteCompose67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteDigits67

theorem postSum_digits (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x2134)
    (sum : s.getReg .x14 = BitVec.ofNat 64
      (GroupedBalancedQuaternary.rawSum message))
    (stack : s.getReg .x2 = 0xfff700)
    (input : s.getReg .x10 = 0x80500)
    (output : s.getReg .x11 = 0x80600)
    (hmsg : ∀ j : Fin 16,
      s.getByte (s.getReg .x10 + BitVec.ofNat 64 j.val) =
        message.extractLsb' (8*j.val) 8)
    (hplain : ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfff800+4*entry.val+k.val)) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val))
    (hflip : ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfffc00+4*entry.val+k.val)) =
        BitVec.ofNat 8 (3-GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val)) :
    ∀ chain : Fin 67,
      (postSumState s message).getByte
        (BitVec.ofNat 64 (0x80600+chain.val)) =
      BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val := by
  intro chain
  by_cases hp : chain.val < 64
  · let j : Fin 16 := ⟨chain.val / 4, by omega⟩
    let k : Fin 4 := ⟨chain.val % 4, by omega⟩
    have h := postSum_payload_bytes s message pc sum stack input output
      hmsg hplain hflip j k
    have haddr : 0x80600 + 4*j.val+k.val = 0x80600+chain.val := by
      simp only [j,k]
      omega
    rw [haddr] at h
    have hindex : (⟨4*j.val+k.val, by omega⟩ : Fin 64) =
        ⟨chain.val, hp⟩ := by
      apply Fin.ext
      simp only [j,k]
      omega
    rw [hindex] at h
    have hdigit : (GroupedBalancedChecksum67.digit message chain).val =
        GroupedBalancedQuaternary.payloadDigit message ⟨chain.val, hp⟩ := by
      simp only [GroupedBalancedChecksum67.digit, dif_pos hp, Fin.val_mk]
    rw [hdigit]
    exact h
  · by_cases h64 : chain.val = 64
    · have h := postSum_flag s message pc sum stack output
      have haddr : 0x80600 + chain.val = 0x80640 := by omega
      have hdigit : (GroupedBalancedChecksum67.digit message chain).val =
          GroupedBalancedQuaternary.flagDigit message := by
        simp only [GroupedBalancedChecksum67.digit, dif_neg hp, if_pos h64]
      rw [haddr, hdigit]
      exact h
    · by_cases h65 : chain.val = 65
      · have h := (postSum_checksum_bytes s message pc sum stack output).1
        have haddr : 0x80600 + chain.val = 0x80641 := by omega
        have hdigit : (GroupedBalancedChecksum67.digit message chain).val =
            GroupedBalancedQuaternary.checksum message % 9 := by
          simp only [GroupedBalancedChecksum67.digit, dif_neg hp,
            if_neg (by omega : chain.val ≠ 64), if_pos h65]
        rw [haddr, hdigit]
        exact h
      · have h := (postSum_checksum_bytes s message pc sum stack output).2
        have h66 : chain.val = 66 := by have := chain.isLt; omega
        have haddr : 0x80600 + chain.val = 0x80642 := by omega
        have hdigit : (GroupedBalancedChecksum67.digit message chain).val =
            GroupedBalancedQuaternary.checksum message / 9 := by
          simp only [GroupedBalancedChecksum67.digit, dif_neg hp,
            if_neg h64, if_neg h65]
        rw [haddr, hdigit]
        exact h

#print axioms postSum_digits

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteDigits67

end

open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteSetup67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteFull67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteDigits67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullDigits67

theorem fullDecoder_digits (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x20f8)
    (stack : s.getReg .x2 = 0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (hsum : ∀ entry : Fin 256,
      s.getByte (BitVec.ofNat 64 (0xfff700+entry.val)) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.byteSum entry.val))
    (hplain : ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfff800+4*entry.val+k.val)) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val))
    (hflip : ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfffc00+4*entry.val+k.val)) =
        BitVec.ofNat 8 (3-GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val)) :
    ∀ chain : Fin 67,
      (fullDecoderState s message).getByte
        (BitVec.ofNat 64 (0x80600+chain.val)) =
      BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val := by
  let p := setupState s
  let q := sumLoop p 16
  have hs := setup_fields s pc stack
  rcases hs with ⟨hpc,hx10,hx11,hx6,hx14,hx18,hx17,hx2⟩
  have hmsg_p : ∀ j : Fin 16,
      p.getByte (p.getReg .x6 + BitVec.ofNat 64 j.val) =
        message.extractLsb' (8*j.val) 8 := by
    intro j
    change (setupState s).getByte _ = _
    rw [hx6, setup_byte]
    have ha : (0x80500 : Word) + BitVec.ofNat 64 j.val =
        BitVec.ofNat 64 (0x80500+j.val) := by
      rw [BitVec.ofNat_add]
      rfl
    rw [ha]
    exact hmsg j
  have hsum_p : ∀ entry : Fin 256,
      p.getByte (p.getReg .x17 + BitVec.ofNat 64 entry.val) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.byteSum entry.val) := by
    intro entry
    change (setupState s).getByte _ = _
    rw [hx17, setup_byte]
    have ha : (0xfff700 : Word) + BitVec.ofNat 64 entry.val =
        BitVec.ofNat 64 (0xfff700+entry.val) := by
      rw [BitVec.ofNat_add]
      rfl
    rw [ha]
    exact hsum entry
  have hsumloop := sumLoop_interface_fast p message hpc hx18 hx6 hx17 hx14
    hmsg_p hsum_p
  rcases hsumloop with ⟨_,hqpc,hqsum⟩
  have hq2 : q.getReg .x2 = 0xfff700 := by
    rw [sumLoop_x2, hx2]
  have hq10 : q.getReg .x10 = 0x80500 := by
    rw [sumLoop_x10, hx10]
  have hq11 : q.getReg .x11 = 0x80600 := by
    rw [sumLoop_x11, hx11]
  have hmsg_q : ∀ j : Fin 16,
      q.getByte (q.getReg .x10 + BitVec.ofNat 64 j.val) =
        message.extractLsb' (8*j.val) 8 := by
    intro j
    rw [hq10, sumLoop_byte, setup_byte]
    have ha : (0x80500 : Word) + BitVec.ofNat 64 j.val =
        BitVec.ofNat 64 (0x80500+j.val) := by
      rw [BitVec.ofNat_add]
      rfl
    rw [ha]
    exact hmsg j
  have hplain_q : ∀ entry : Fin 256, ∀ k : Fin 4,
      q.getByte (BitVec.ofNat 64 (0xfff800+4*entry.val+k.val)) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val) := by
    intro entry k
    rw [sumLoop_byte, setup_byte]
    exact hplain entry k
  have hflip_q : ∀ entry : Fin 256, ∀ k : Fin 4,
      q.getByte (BitVec.ofNat 64 (0xfffc00+4*entry.val+k.val)) =
        BitVec.ofNat 8 (3-GroupedBalancedDecoderByte67.rawByteDigit entry.val k.val) := by
    intro entry k
    rw [sumLoop_byte, setup_byte]
    exact hflip entry k
  change ∀ chain : Fin 67,
    (GroupedBalancedSignByteCompose67.postSumState q message).getByte
      (BitVec.ofNat 64 (0x80600+chain.val)) =
    BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val
  exact postSum_digits q message hqpc hqsum hq2 hq10 hq11
    hmsg_q hplain_q hflip_q

#print axioms fullDecoder_digits

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullDigits67
