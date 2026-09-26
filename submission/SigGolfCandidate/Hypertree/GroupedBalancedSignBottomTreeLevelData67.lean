import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelAdvance67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelControl67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev image := GroupedBalancedSignImage67.image
def branchState (s : MachineState) : MachineState :=
  execInstrBr s (.BNE .x6 .x7 (-740))
theorem branch_steps (s : MachineState) (pc : s.pc = 0x20e8) :
    OrdinarySteps image s 1 (branchState s) := by
  have code : Keygen.instructionAt image 0x20e8 =
    some (.base (.BNE .x6 .x7 (-740))) := by decide
  apply OrdinarySteps.step s (branchState s) _
    (.base (.BNE .x6 .x7 (-740))) 0
  · simpa only [Keygen.fetch_at,pc] using code
  · rfl
  exact OrdinarySteps.refl _
theorem branch_pc (s : MachineState) (pc : s.pc = 0x20e8) :
    (branchState s).pc =
      if s.getReg .x6 ≠ s.getReg .x7 then 0x1e04 else 0x20ec := by
  simp [branchState,execInstrBr,pc,signExtend13]
def transitionState (s : MachineState) : MachineState :=
  branchState
    (GroupedBalancedSignBottomTreeLevelAdvance67.advanceState
      (GroupedBalancedSignBottomTreeLevelSwap67.swapState s))
theorem transition_steps (s : MachineState) (pc : s.pc = 0x2058) :
    OrdinarySteps image s 37 (transitionState s) := by
  let t1 := GroupedBalancedSignBottomTreeLevelSwap67.swapState s
  let t2 := GroupedBalancedSignBottomTreeLevelAdvance67.advanceState t1
  have p1 := GroupedBalancedSignBottomTreeLevelSwap67.swap_pc s pc
  have p2 := GroupedBalancedSignBottomTreeLevelAdvance67.advance_pc t1 p1
  have a := GroupedBalancedSignBottomTreeLevelSwap67.swap_steps s pc
  have b := GroupedBalancedSignBottomTreeLevelAdvance67.advance_steps
    t1 p1 (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s)
  have c := branch_steps t2 p2
  have ab := Keygen.ordinary_trans image s t1 t2 18 18 a b
  have abc := Keygen.ordinary_trans image s t2 (transitionState s) 36 1
    (by simpa only [show 18 + 18 = 36 by decide] using ab) c
  simpa only [show 1 + 36 = 37 by decide] using abc
theorem branch_frame (s : MachineState) (a : Word) :
    (branchState s).getMem a = s.getMem a := by
  simp [branchState,execInstrBr]
#print axioms transition_steps
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelControl67

namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
private abbrev swap := GroupedBalancedSignBottomTreeLevelSwap67.swapState
private abbrev advance := GroupedBalancedSignBottomTreeLevelAdvance67.advanceState
private abbrev transition := GroupedBalancedSignBottomTreeLevelControl67.transitionState
theorem source (s : MachineState) :
    (transition s).getMem 0x810c0 = s.getMem 0x810c8 := by
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState
    (advance (swap s))).getMem 0x810c0 = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_frame,
    GroupedBalancedSignBottomTreeLevelAdvance67.advance_frame
      (swap s) 0x810c0 (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s)]
  · exact GroupedBalancedSignBottomTreeLevelSwap67.swap_source s
  · decide
  · decide
  · decide
theorem target (s : MachineState) :
    (transition s).getMem 0x810c8 = s.getMem 0x810c0 := by
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState
    (advance (swap s))).getMem 0x810c8 = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_frame,
    GroupedBalancedSignBottomTreeLevelAdvance67.advance_frame
      (swap s) 0x810c8 (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s)]
  · exact GroupedBalancedSignBottomTreeLevelSwap67.swap_target s
  · decide
  · decide
  · decide
theorem count (s : MachineState) :
    (transition s).getMem 0x810d0 = s.getMem 0x810d0 >>> 1 := by
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState
    (advance (swap s))).getMem 0x810d0 = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_frame,
    GroupedBalancedSignBottomTreeLevelAdvance67.advance_half_count
      (swap s) (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s),
    GroupedBalancedSignBottomTreeLevelSwap67.swap_half_count]
theorem height (s : MachineState) :
    (transition s).getMem 0x81000 = s.getMem 0x81000 + 1 := by
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState
    (advance (swap s))).getMem 0x81000 = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_frame,
    GroupedBalancedSignBottomTreeLevelAdvance67.advance_height
      (swap s) (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s),
    GroupedBalancedSignBottomTreeLevelSwap67.swap_frame]
  · decide
  · decide
theorem witness_level (s : MachineState) :
    (transition s).getMem 0x81050 = s.getMem 0x81050 + 1 := by
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState
    (advance (swap s))).getMem 0x81050 = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_frame,
    GroupedBalancedSignBottomTreeLevelAdvance67.advance_witness_level
      (swap s) (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s),
    GroupedBalancedSignBottomTreeLevelSwap67.swap_frame]
  · decide
  · decide
theorem frame (s : MachineState) (a : Word)
    (h0 : a ≠ 0x810c0) (h1 : a ≠ 0x810c8)
    (h2 : a ≠ 0x810d0) (h3 : a ≠ 0x81000)
    (h4 : a ≠ 0x81050) :
    (transition s).getMem a = s.getMem a := by
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState
    (advance (swap s))).getMem a = _
  rw [GroupedBalancedSignBottomTreeLevelControl67.branch_frame,
    GroupedBalancedSignBottomTreeLevelAdvance67.advance_frame
      (swap s) a (GroupedBalancedSignBottomTreeLevelSwap67.swap_ptr s) h2 h3 h4,
    GroupedBalancedSignBottomTreeLevelSwap67.swap_frame s a h0 h1]
#print axioms source
#print axioms target
#print axioms count
#print axioms height
#print axioms witness_level
#print axioms frame
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelData67
