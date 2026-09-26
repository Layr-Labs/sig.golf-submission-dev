import SigGolfCandidate.Hypertree.GroupedBalancedProgram67Byte
import SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteMemory67
import SigGolfCandidate.Memory

/-! The public decoder tables survive the official verifier input loader. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteLoader67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByte67
open SigGolfCandidate.Hypertree.GroupedBalancedDecoderByteMemory67
set_option maxRecDepth 8192
set_option maxHeartbeats 0

private abbrev byteSubmission := GroupedBalancedProgram67Byte.submission

private theorem image_data_byte (blank : MachineState) (i : Nat)
    (hi : i < 2304) :
    (blank.writeBytesAsWords
      (BitVec.ofNat 64 (Riscv.dataBase GroupedBalancedVerifyImage67Fast2Byte.image))
      GroupedBalancedVerifyImage67Fast2Byte.image.data).getByte
      (BitVec.ofNat 64 (0xfff700+i)) =
        data[i]'(by rw [data_length]; exact hi) := by
  have hbase : Riscv.dataBase GroupedBalancedVerifyImage67Fast2Byte.image = 0xfff700 := by
    simp [Riscv.dataBase, GroupedBalancedVerifyImage67Fast2Byte.image,
      GroupedBalancedDecoderByte67.data_length, MEMORY_BYTES]
  rw [hbase]
  exact SigGolfCandidate.Memory.write_byte _ 0xfff700 data i
    (by decide) (by rw [data_length]; decide) (by rw [data_length]; exact hi)

theorem initial_data_byte (input : Input byteSubmission.sizes .verify) (s : MachineState)
    (loaded : initialState byteSubmission .verify input = some s)
    (i : Nat) (hi : i < 2304) :
    s.getByte (BitVec.ofNat 64 (0xfff700+i)) =
      data[i]'(by rw [data_length]; exact hi) := by
  rcases input with ⟨message, pk, witness⟩
  simp only [initialState, if_pos (GroupedBalancedProgram67Byte.admissible.2 .verify)] at loaded
  cases Option.some.inj loaded
  rw [SigGolfCandidate.Memory.getByte_setReg]
  dsimp only [inputBuffers, List.foldl_cons, List.foldl_nil,
    byteSubmission, GroupedBalancedProgram67Byte.submission,
    GroupedBalancedProgram67.sizes, Riscv.standardLayout,
    Riscv.witnessBase, Riscv.signatureBase]
  have hwbase : BitVec.ofNat 64 (131168 + 8 * ((50848 + 7) / 8)) =
      (0x2c700 : Word) := by decide
  rw [hwbase]
  let blank : MachineState :=
    { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  let d := blank.writeBytesAsWords
    (BitVec.ofNat 64 (Riscv.dataBase GroupedBalancedVerifyImage67Fast2Byte.image))
    GroupedBalancedVerifyImage67Fast2Byte.image.data
  let m := d.writeBytesAsWords 0 (bytes message)
  let t := m.writeBytesAsWords 0x40 (bytes pk)
  change (t.writeBytesAsWords (BitVec.ofNat 64 0x2c700) (bytes witness)).getByte
    (BitVec.ofNat 64 (0xfff700+i)) = _
  rw [SigGolfCandidate.Memory.write_preserves_byte _ 0x2c700 (bytes witness)
    0xfff700 i (by decide) (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by omega) (by right; rw [SigGolfCandidate.Memory.bytes_length]; simp only [byteSubmission, GroupedBalancedProgram67Byte.submission, GroupedBalancedProgram67.sizes]; decide)]
  change (m.writeBytesAsWords (BitVec.ofNat 64 0x40) (bytes pk)).getByte
    (BitVec.ofNat 64 (0xfff700+i)) = _
  rw [SigGolfCandidate.Memory.write_preserves_byte _ 0x40 (bytes pk)
    0xfff700 i (by decide) (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by omega) (by right; simp)]
  change (d.writeBytesAsWords (BitVec.ofNat 64 0) (bytes message)).getByte
    (BitVec.ofNat 64 (0xfff700+i)) = _
  rw [SigGolfCandidate.Memory.write_preserves_byte _ 0 (bytes message)
    0xfff700 i (by decide) (by rw [SigGolfCandidate.Memory.bytes_length]; decide)
    (by omega) (by right; simp)]
  exact image_data_byte blank i hi

#print axioms initial_data_byte

end SigGolfCandidate.Hypertree.GroupedBalancedVerifyByteLoader67
