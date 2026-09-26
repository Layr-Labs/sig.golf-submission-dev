import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
import SigGolfCandidate.Hypertree.GroupedBalancedByteSum67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteSumLoop67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
open SigGolfCandidate.Hypertree.GroupedBalancedByteSum67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteInterface67

private theorem widen_byte_sum (value : Nat) :
    BitVec.setWidth 64 (BitVec.ofNat 8 (byteSum value)) =
      BitVec.ofNat 64 (byteSum value) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hb := byteSum_le value
  omega

private theorem tableByte_from_message (s : MachineState) (message : BitVec 128)
    (hmsg : ∀ j : Fin 16, s.getByte
      (s.getReg .x6 + BitVec.ofNat 64 j.val) = message.extractLsb' (8*j.val) 8)
    (htable : ∀ entry : Fin 256, s.getByte
      (s.getReg .x17 + BitVec.ofNat 64 entry.val) =
        BitVec.ofNat 8 (byteSum entry.val))
    (j : Nat) (hj : j < 16) :
    tableByte s j = BitVec.ofNat 64
      (byteSum (message.extractLsb' (8*j) 8).toNat) := by
  unfold tableByte
  rw [hmsg ⟨j,hj⟩]
  let value := (message.extractLsb' (8*j) 8).toNat
  have haddr : BitVec.setWidth 64 (message.extractLsb' (8*j) 8) =
      BitVec.ofNat 64 value := by
    apply BitVec.eq_of_toNat_eq
    simp [value, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [haddr]
  have he := htable ⟨value, (message.extractLsb' (8*j) 8).isLt⟩
  rw [he]
  exact widen_byte_sum value

private def messageSumPrefix (message : BitVec 128) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, byteSum (message.extractLsb' (8*j) 8).toNat

theorem tableTotal_from_message (s : MachineState) (message : BitVec 128)
    (hmsg : ∀ j : Fin 16, s.getByte
      (s.getReg .x6 + BitVec.ofNat 64 j.val) = message.extractLsb' (8*j.val) 8)
    (htable : ∀ entry : Fin 256, s.getByte
      (s.getReg .x17 + BitVec.ofNat 64 entry.val) =
        BitVec.ofNat 8 (byteSum entry.val))
    (n : Nat) (hn : n ≤ 16) :
    tableTotal s n = BitVec.ofNat 64 (messageSumPrefix message n) := by
  induction n with
  | zero => simp [tableTotal, messageSumPrefix]
  | succ n ih =>
    have hn0 : n ≤ 16 := by omega
    have hn1 : n < 16 := by omega
    simp only [tableTotal, ih hn0, tableByte_from_message s message hmsg htable n hn1]
    rw [show messageSumPrefix message (n+1) = messageSumPrefix message n +
      byteSum (message.extractLsb' (8*n) 8).toNat by
        simp [messageSumPrefix, Finset.sum_range_succ]]
    exact (BitVec.ofNat_add _ _).symm

theorem tableTotal_eq_rawSum (s : MachineState) (message : BitVec 128)
    (hmsg : ∀ j : Fin 16, s.getByte
      (s.getReg .x6 + BitVec.ofNat 64 j.val) = message.extractLsb' (8*j.val) 8)
    (htable : ∀ entry : Fin 256, s.getByte
      (s.getReg .x17 + BitVec.ofNat 64 entry.val) =
        BitVec.ofNat 8 (byteSum entry.val)) :
    tableTotal s 16 = BitVec.ofNat 64 (SigGolfCandidate.Hypertree.GroupedBalancedQuaternary.rawSum message) := by
  rw [tableTotal_from_message s message hmsg htable 16 (by decide)]
  have hrange : messageSumPrefix message 16 = sumBytes message := by
    simpa [messageSumPrefix, sumBytes] using
      (Fin.sum_univ_eq_sum_range
        (fun j : Nat => byteSum (message.extractLsb' (8*j) 8).toNat) 16).symm
  rw [hrange, sumBytes_eq_rawSum]

theorem sumLoop_interface (s : MachineState) (message : BitVec 128)
    (pc : s.pc = 0x1020) (rem : s.getReg .x18 = 16)
    (input : s.getReg .x6 = 0x80500) (table : s.getReg .x17 = 0xfff700)
    (total : s.getReg .x14 = 0)
    (hmsg : ∀ j : Fin 16, s.getByte
      (s.getReg .x6 + BitVec.ofNat 64 j.val) = message.extractLsb' (8*j.val) 8)
    (htable : ∀ entry : Fin 256, s.getByte
      (s.getReg .x17 + BitVec.ofNat 64 entry.val) =
        BitVec.ofNat 8 (byteSum entry.val)) :
    OrdinarySteps SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67.image
      s 112 (sumLoop s 16) ∧
    (sumLoop s 16).pc = 0x103c ∧
    (sumLoop s 16).getReg .x14 =
      BitVec.ofNat 64 (SigGolfCandidate.Hypertree.GroupedBalancedQuaternary.rawSum message) ∧
    (sumLoop s 16).getReg .x18 = 0 ∧
    (sumLoop s 16).getReg .x6 = 0x80510 ∧
    (sumLoop s 16).getReg .x17 = 0xfff700 ∧
    (∀ a : Word, (sumLoop s 16).getByte a = s.getByte a) := by
  constructor
  · simpa using sumLoop_steps s pc rem input table 16 (by decide)
  constructor
  · exact sumLoop_exit_pc s pc rem
  constructor
  · rw [sumLoop_total, total, tableTotal_eq_rawSum s message hmsg htable]
    simp
  constructor
  · rw [sumLoop_remaining, rem]
    decide
  constructor
  · rw [sumLoop_input_pointer, input]
    decide
  constructor
  · rw [sumLoop_table_pointer, table]
  · exact sumLoop_byte s 16

#print axioms tableTotal_eq_rawSum
#print axioms sumLoop_interface

end SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteInterface67
