import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
import SigGolfCandidate.Memory

/-! The organizer's loader reads the formula-defined byte-sum table exactly. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteMemory67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem loaded_sum_byte (s : MachineState) (entry : Fin 256) :
    (s.writeBytesAsWords (BitVec.ofNat 64 0xfff700) data).getByte
      (BitVec.ofNat 64 (0xfff700 + entry.val)) =
        BitVec.ofNat 8 (byteSum entry.val) := by
  have h := SigGolfCandidate.Memory.write_byte s 0xfff700 data entry.val
    (by decide) (by rw [data_length]; decide) (by rw [data_length]; omega)
  rw [h]
  exact pair_table_byte entry

#print axioms loaded_sum_byte

theorem loaded_plain_byte (s : MachineState) (entry : Fin 256) (j : Fin 4) :
    (s.writeBytesAsWords (BitVec.ofNat 64 0xfff700) data).getByte
      (BitVec.ofNat 64 (0xfff700 + 256 + 4 * entry.val + j.val)) =
        BitVec.ofNat 8 (rawByteDigit entry.val j.val) := by
  have h := SigGolfCandidate.Memory.write_byte s 0xfff700 data
    (256 + 4 * entry.val + j.val)
    (by decide) (by rw [data_length]; decide) (by rw [data_length]; omega)
  rw [show 0xfff700 + 256 + 4 * entry.val + j.val =
      0xfff700 + (256 + 4 * entry.val + j.val) by omega, h]
  exact plain_table_byte entry j

theorem loaded_flipped_byte (s : MachineState) (entry : Fin 256) (j : Fin 4) :
    (s.writeBytesAsWords (BitVec.ofNat 64 0xfff700) data).getByte
      (BitVec.ofNat 64 (0xfff700 + 1280 + 4 * entry.val + j.val)) =
        BitVec.ofNat 8 (3 - rawByteDigit entry.val j.val) := by
  have h := SigGolfCandidate.Memory.write_byte s 0xfff700 data
    (1280 + 4 * entry.val + j.val)
    (by decide) (by rw [data_length]; decide) (by rw [data_length]; omega)
  rw [show 0xfff700 + 1280 + 4 * entry.val + j.val =
      0xfff700 + (1280 + 4 * entry.val + j.val) by omega, h]
  exact flipped_table_byte entry j

#print axioms loaded_plain_byte
#print axioms loaded_flipped_byte

theorem loaded_table_interface (s : MachineState)
    (hbase : s.getReg .x17 = 0xfff700) :
    ∀ entry : Fin 256,
      (s.writeBytesAsWords (BitVec.ofNat 64 0xfff700) data).getByte
        ((s.writeBytesAsWords (BitVec.ofNat 64 0xfff700) data).getReg .x17 +
          BitVec.ofNat 64 entry.val) =
          BitVec.ofNat 8 (byteSum entry.val) := by
  intro entry
  rw [MachineState.getReg_writeBytesAsWords, hbase]
  have haddr : (0xfff700 : Word) + BitVec.ofNat 64 entry.val =
      BitVec.ofNat 64 (0xfff700 + entry.val) := by
    rw [BitVec.ofNat_add]
    rfl
  rw [haddr]
  exact loaded_sum_byte s entry

#print axioms loaded_table_interface

end SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteMemory67
