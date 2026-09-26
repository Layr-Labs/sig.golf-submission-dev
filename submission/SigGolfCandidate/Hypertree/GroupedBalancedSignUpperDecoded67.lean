import SigGolfCandidate.Hypertree.GroupedBalancedSignByteTableFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullDigits67
import SigGolfCandidate.Hypertree.GroupedBalancedSignByteReturn67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
import SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoderCall67


namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteSetup67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteFull67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteTableFrame67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem fullDecoder_table_byte (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x20f8)
    (stack : s.getReg .x2 = 0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (hsum : ∀ entry : Fin 256,
      s.getByte (BitVec.ofNat 64 (0xfff700+entry.val)) =
        BitVec.ofNat 8 (GroupedBalancedDecoderByte67.byteSum entry.val))
    (i : Nat) (hi : i < 2304) :
    (fullDecoderState s message).getByte (BitVec.ofNat 64 (0xfff700+i)) =
      s.getByte (BitVec.ofNat 64 (0xfff700+i)) := by
  let p := setupState s
  let q := sumLoop p 16
  have hs := setup_fields s pc stack
  rcases hs with ⟨hpc,_,hx11,hx6,hx14,hx18,hx17,hx2⟩
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
  have hq11 : q.getReg .x11 = 0x80600 := by
    rw [sumLoop_x11, hx11]
  have hpost := postSum_table_byte q message hqpc hqsum hq2 hq11 i hi
  change (GroupedBalancedSignByteCompose67.postSumState q message).getByte _ = _
  rw [hpost, sumLoop_byte, setup_byte]

#print axioms fullDecoder_table_byte

end SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullFrame67



/-! Contract for the relocated signer table decoder at PC 0x20f8. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignByteContract67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteFull67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullDigits67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteFullFrame67
open SigGolfCandidate.Hypertree.GroupedBalancedSignByteReturn67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem decoder_contract (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x20f8)
    (stack : s.getReg .x2 = 0xfff700)
    (link : s.getReg .x1 = 0x1740)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : Tables s) :
    OrdinarySteps GroupedBalancedSignImage67Byte.image s
      (8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6)
      (fullDecoderState s message) ∧
    (∀ chain : Fin 67,
      (fullDecoderState s message).getByte
        (BitVec.ofNat 64 (0x80600+chain.val)) =
      BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val) ∧
    (fullDecoderState s message).pc = 0x1740 ∧
    Tables (fullDecoderState s message) := by
  have hsum := tables_sum s tables
  have hplain := tables_plain s tables
  have hflip := tables_flipped s tables
  refine ⟨fullDecoder_steps s message pc stack hmsg hsum,
    fullDecoder_digits s message pc stack hmsg hsum hplain hflip,
    fullDecoder_return_pc s message link, ?_⟩
  intro i hi
  exact (fullDecoder_table_byte s message pc stack hmsg hsum i hi).trans
    (tables i hi)

#print axioms decoder_contract
end SigGolfCandidate.Hypertree.GroupedBalancedSignByteContract67


/-! The complete upper signer decoder call, including its digit and table contract. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoded67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
open SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoderCall67
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67Byte.image

def decodedState (s : MachineState) (message : BitVec 128) : MachineState :=
  GroupedBalancedSignByteFull67.fullDecoderState (callState s) message

theorem decode_group (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1720)
    (stack : s.getReg .x2 = 0xfff700)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : Tables s) :
    OrdinarySteps image s
      (8 + (8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6))
      (decodedState s message) ∧
    (decodedState s message).pc = 0x1740 ∧
    (∀ chain : Fin 67,
      (decodedState s message).getByte
        (BitVec.ofNat 64 (0x80600+chain.val)) =
      BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val) ∧
    Tables (decodedState s message) := by
  have hcall := call_steps s pc (by decide)
  have htable : Tables (callState s) := by
    intro i hi
    rw [call_table_byte s i hi]
    exact tables i hi
  have hmessage : ∀ j : Fin 16,
      (callState s).getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8 := by
    intro j
    rw [call_digest_byte]
    exact hmsg j
  obtain ⟨hdecode,hdigits,hpc,htables⟩ :=
    GroupedBalancedSignByteContract67.decoder_contract
      (callState s) message (call_pc s pc)
      (by rw [call_stack,stack]) (call_link s pc) hmessage htable
  refine ⟨?_,hpc,hdigits,htables⟩
  exact GroupedBalancedDecoderByteSumLoop67.steps_comp hcall hdecode

#print axioms decode_group
end SigGolfCandidate.Hypertree.GroupedBalancedSignUpperDecoded67
