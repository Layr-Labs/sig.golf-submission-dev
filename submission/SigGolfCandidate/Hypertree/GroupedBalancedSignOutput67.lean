import SigGolfCandidate.Hypertree.GroupedBalancedProgram67ByteSign
import SigGolfCandidate.Hypertree.KeygenNode
import SigGolfCandidate.Memory

/-! Convert word-wise signer output equality to the official 50,848-byte wire. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignOutput67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem read_signature (s : MachineState) (wire : Bytes 50848)
    (words : ∀ i : Fin 6356,
      s.getMem (Signing.wordAddress 0x20060 i.val) =
        wire.extractLsb' (64*i.val) 64) :
    readBuffer s 0x20060 50848 = wire := by
  apply SigGolfCandidate.Memory.readBuffer_of_bytes
  intro i hi
  rw [Signing.getByte_word s 0x20060 i (by decide) (by omega),
    words ⟨i/8,by omega⟩]
  exact KeygenNode.extractByte_slice wire i

#print axioms read_signature
end SigGolfCandidate.Hypertree.GroupedBalancedSignOutput67
