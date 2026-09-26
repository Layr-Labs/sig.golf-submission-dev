import SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPrelude67

/-! Complete Fast2Byte upper-leaf compression and two-word result copy. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeaf67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
open SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeafPrelude67
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

def leafState (hash : Hash) (s : MachineState) : MachineState :=
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  GroupedBalancedByteFastLeafCopy67.copyState hashed

/-- One direct67 leaf hash costs 37 setup instructions, one 18-block query,
and 18 copy instructions. The certificate uses the actual Fast2Byte image. -/
theorem leaf_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1684) :
    Trace hash image s 56 199 1 18 (leafState hash s) ∧
    (leafState hash s).pc = 0x174c := by
  let prepared := preludeState s
  let hashed := writeHash prepared (hash (hashInput prepared))
  have first := prelude_block s pc
  have fields := prelude_fields s pc
  have second := GroupedBalancedByteFastLeafQuery67.hash_trace hash prepared fields
  have hashPC := GroupedBalancedByteFastLeafQuery67.hash_pc hash prepared fields
  have third := GroupedBalancedByteFastLeafCopy67.copy_trace hash hashed hashPC
  constructor
  · have total := first.trace.trans (second.trans third)
    simpa [leafState,prepared,hashed,image,
      GroupedBalancedByteFastLeafPrelude67.image] using total
  · exact GroupedBalancedByteFastLeafCopy67.copy_pc hashed hashPC

theorem leaf_cycles_45 : 45 * 199 = 8955 := by decide

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastLeaf67
