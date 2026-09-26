import SigGolfCandidate.Hypertree.GroupedBalancedByteFastCopyFrame67


/-! Exact left/right sibling arrangement before the common node core. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeSides67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem right_side (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x17dc)
    (src0 : accessValid (s.getMem 0x81048) 8 = true)
    (src8 : accessValid (s.getMem 0x81048 + 8) 8 = true) :
    ∃ final, Trace hash image s 27 27 0 0 final ∧
      final.pc = 0x1880 := by
  obtain ⟨copied,first,copiedPC,frame⟩ :=
    GroupedBalancedByteFastCopyFrame67.witness_copy_frame hash s pc
  have valid0 : accessValid (copied.getMem 0x81048) 8 = true := by
    rw [frame]; exact src0
  have valid8 : accessValid (copied.getMem 0x81048 + 8) 8 = true := by
    rw [frame]; exact src8
  have second := GroupedBalancedByteFastEdgeRoute67.right_route
    hash copied copiedPC valid0 valid8
  refine ⟨_,?_,second.2⟩
  have path := first.trans second.1
  simpa [image,GroupedBalancedByteFastCopies67.image,
    GroupedBalancedByteFastEdgeRoute67.image] using path

theorem left_side (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1830)
    (src0 : accessValid (s.getMem 0x81048) 8 = true)
    (src8 : accessValid (s.getMem 0x81048 + 8) 8 = true) :
    ∃ final, Trace hash image s 26 26 0 0 final ∧
      final.pc = 0x1880 := by
  obtain ⟨copied,first,copiedPC,frame⟩ :=
    GroupedBalancedByteFastCopyFrame67.sibling_copy_frame hash s pc
  have valid0 : accessValid (copied.getMem 0x81048) 8 = true := by
    rw [frame]; exact src0
  have valid8 : accessValid (copied.getMem 0x81048 + 8) 8 = true := by
    rw [frame]; exact src8
  have second := GroupedBalancedByteFastEdgeRoute67.left_route
    hash copied copiedPC valid0 valid8
  refine ⟨_,?_,second.2⟩
  have path := first.trans second.1
  simpa [image,GroupedBalancedByteFastCopies67.image,
    GroupedBalancedByteFastEdgeRoute67.image] using path

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdgeSides67


/-! Complete per-edge cycle traces for the Fast2Byte upper Merkle path. -/

namespace SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdge67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

def image : Image := GroupedBalancedVerifyImage67Fast2Byte.image

theorem left_edge (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1758)
    (side : (GroupedBalancedByteFastEdgeIndex67.indexState s).getReg .x6 = 0)
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true) :
    ∃ final, Trace hash image s 164 171 1 1 final ∧
      final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4 := by
  let indexed := GroupedBalancedByteFastEdgeIndex67.indexState s
  have first := GroupedBalancedByteFastEdgeIndex67.index_block s pc
  have indexedPC : indexed.pc = 0x1830 := by
    rw [GroupedBalancedByteFastEdgeIndex67.index_pc s pc]
    simp [side]
  have indexFrame := GroupedBalancedByteFastEdgeIndex67.index_pointer_frame s
  have valid0 : accessValid (indexed.getMem 0x81048) 8 = true := by
    rw [indexFrame]; exact ptr0
  have valid8 : accessValid (indexed.getMem 0x81048 + 8) 8 = true := by
    rw [indexFrame]; exact ptr8
  obtain ⟨arranged,second,arrangedPC⟩ :=
    GroupedBalancedByteFastEdgeSides67.left_side hash indexed
      indexedPC valid0 valid8
  obtain ⟨node,third,_,nodePC⟩ :=
    GroupedBalancedByteFastNodeCore67.node_core hash arranged arrangedPC
  have fourth := GroupedBalancedByteFastEdgeUpdate67.update_block node nodePC
  let final := GroupedBalancedByteFastEdgeUpdate67.updateState node
  refine ⟨final,?_,GroupedBalancedByteFastEdgeUpdate67.update_pc node nodePC⟩
  have path := first.trace.trans
    (second.trans (third.trans fourth.trace))
  simpa [image,GroupedBalancedByteFastEdgeIndex67.image,
    GroupedBalancedByteFastEdgeSides67.image,
    GroupedBalancedByteFastNodeCore67.image,
    GroupedBalancedByteFastEdgeUpdate67.image] using path

theorem right_edge (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x1758)
    (side : (GroupedBalancedByteFastEdgeIndex67.indexState s).getReg .x6 ≠ 0)
    (ptr0 : accessValid (s.getMem 0x81048) 8 = true)
    (ptr8 : accessValid (s.getMem 0x81048 + 8) 8 = true) :
    ∃ final, Trace hash image s 165 172 1 1 final ∧
      final.pc = if final.getReg .x6 ≠ final.getReg .x7
        then 0x1758 else 0x19c4 := by
  let indexed := GroupedBalancedByteFastEdgeIndex67.indexState s
  have first := GroupedBalancedByteFastEdgeIndex67.index_block s pc
  have indexedPC : indexed.pc = 0x17dc := by
    rw [GroupedBalancedByteFastEdgeIndex67.index_pc s pc]
    exact if_neg side
  have indexFrame := GroupedBalancedByteFastEdgeIndex67.index_pointer_frame s
  have valid0 : accessValid (indexed.getMem 0x81048) 8 = true := by
    rw [indexFrame]; exact ptr0
  have valid8 : accessValid (indexed.getMem 0x81048 + 8) 8 = true := by
    rw [indexFrame]; exact ptr8
  obtain ⟨arranged,second,arrangedPC⟩ :=
    GroupedBalancedByteFastEdgeSides67.right_side hash indexed
      indexedPC valid0 valid8
  obtain ⟨node,third,_,nodePC⟩ :=
    GroupedBalancedByteFastNodeCore67.node_core hash arranged arrangedPC
  have fourth := GroupedBalancedByteFastEdgeUpdate67.update_block node nodePC
  let final := GroupedBalancedByteFastEdgeUpdate67.updateState node
  refine ⟨final,?_,GroupedBalancedByteFastEdgeUpdate67.update_pc node nodePC⟩
  have path := first.trace.trans
    (second.trans (third.trans fourth.trace))
  simpa [image,GroupedBalancedByteFastEdgeIndex67.image,
    GroupedBalancedByteFastEdgeSides67.image,
    GroupedBalancedByteFastNodeCore67.image,
    GroupedBalancedByteFastEdgeUpdate67.image] using path

theorem edge_fixed_150 : 150 * 171 = 25650 := by decide

end SigGolfCandidate.Hypertree.GroupedBalancedByteFastEdge67
