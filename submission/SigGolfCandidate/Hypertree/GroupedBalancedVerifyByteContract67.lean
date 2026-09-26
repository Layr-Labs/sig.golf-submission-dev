import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTableFrame67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFullDigits67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteReturn67
import SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteLoader67


namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFullFrame67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteSetup67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFull67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteTableFrame67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem fullDecoder_table_byte (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a4c)
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
  change (GroupedBalancedVerifyByteCompose67.postSumState q message).getByte _ = _
  rw [hpost, sumLoop_byte, setup_byte]

#print axioms fullDecoder_table_byte

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFullFrame67


/-! Reusable interface for every call to the real table decoder. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFull67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFullDigits67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteFullFrame67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteReturn67
open SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteLoader67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def Tables (s : MachineState) : Prop :=
  ∀ (i : Nat) (hi : i < 2304),
    s.getByte (BitVec.ofNat 64 (0xfff700+i)) =
      data[i]'(by rw [data_length]; exact hi)

private abbrev byteSubmission := GroupedBalancedProgram67Byte.submission

theorem initial_tables (input : Input byteSubmission.sizes .verify)
    (s : MachineState)
    (loaded : initialState byteSubmission .verify input = some s) :
    Tables s := by
  intro i hi
  exact initial_data_byte input s loaded i hi

theorem tables_sum (s : MachineState) (tables : Tables s) :
    ∀ entry : Fin 256,
      s.getByte (BitVec.ofNat 64 (0xfff700+entry.val)) =
        BitVec.ofNat 8 (byteSum entry.val) := by
  intro entry
  exact (tables entry.val (by omega)).trans (pair_table_byte entry)

theorem tables_plain (s : MachineState) (tables : Tables s) :
    ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfff800+4*entry.val+k.val)) =
        BitVec.ofNat 8 (rawByteDigit entry.val k.val) := by
  intro entry k
  rw [show 0xfff800+4*entry.val+k.val =
      0xfff700+(256+4*entry.val+k.val) by omega]
  exact (tables (256+4*entry.val+k.val) (by omega)).trans
    (plain_table_byte entry k)

theorem tables_flipped (s : MachineState) (tables : Tables s) :
    ∀ entry : Fin 256, ∀ k : Fin 4,
      s.getByte (BitVec.ofNat 64 (0xfffc00+4*entry.val+k.val)) =
        BitVec.ofNat 8 (3-rawByteDigit entry.val k.val) := by
  intro entry k
  rw [show 0xfffc00+4*entry.val+k.val =
      0xfff700+(1280+4*entry.val+k.val) by omega]
  exact (tables (1280+4*entry.val+k.val) (by omega)).trans
    (flipped_table_byte entry k)

theorem decoder_contract (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1a4c)
    (stack : s.getReg .x2 = 0xfff700)
    (link : s.getReg .x1 = 0x1518)
    (hmsg : ∀ j : Fin 16,
      s.getByte (BitVec.ofNat 64 (0x80500+j.val)) =
        message.extractLsb' (8*j.val) 8)
    (tables : Tables s) :
    OrdinarySteps GroupedBalancedVerifyImage67Fast2Byte.image s
      (8+112+(if GroupedBalancedQuaternary.rawSum message < 96 then 9 else 10)+144+6)
      (fullDecoderState s message) ∧
    (∀ chain : Fin 67,
      (fullDecoderState s message).getByte
        (BitVec.ofNat 64 (0x80600+chain.val)) =
      BitVec.ofNat 8 (GroupedBalancedChecksum67.digit message chain).val) ∧
    (fullDecoderState s message).pc = 0x1518 ∧
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

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteContract67
