import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeTickStack67
import SigGolfCandidate.Hypertree.KeygenCopyFrame
import SigGolfCandidate.TraceDeterminism

/-! Stack preservation across the level swap and next-level prelude. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelStack67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 0
private abbrev image := GroupedBalancedSignImage67.image

theorem swap_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeLevelSwap67.swapState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeLevelSwap67.swapState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem advance_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeLevelAdvance67.advanceState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeLevelAdvance67.advanceState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem branch_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeLevelControl67.branchState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeLevelControl67.branchState,execInstrBr]

theorem transition_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeLevelControl67.transitionState s).getReg .x2 =
      s.getReg .x2 := by
  change (GroupedBalancedSignBottomTreeLevelControl67.branchState
    (GroupedBalancedSignBottomTreeLevelAdvance67.advanceState
      (GroupedBalancedSignBottomTreeLevelSwap67.swapState s))).getReg .x2 = _
  exact (branch_sp _).trans ((advance_sp _).trans (swap_sp s))

theorem index_full_sp (s : MachineState) :
    (GroupedBalancedSignBottomTreeIndexData67.fullState s).getReg .x2 =
      s.getReg .x2 := by
  simp [GroupedBalancedSignBottomTreeIndexData67.fullState,
    GroupedBalancedSignBottomTreeIndexLoad67.loadState,
    GroupedBalancedSignBottomTreeIndexShift67.shiftState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem header_copy_sp (s final : MachineState) (pc : s.pc = 0x1e68)
    (trace : OrdinarySteps image s 23 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let begun := GroupedBalancedSignBottomTreeHeaderCopy67.setupState s
  obtain ⟨other,loop,_,_,_,_,sp⟩ := Keygen.copy_all_frame image 0x1e7c
    GroupedBalancedSignBottomTreeHeaderCopy67.copy_code 0x810a8 0x81008 3 begun
    (GroupedBalancedSignBottomTreeHeaderCopy67.copy_inv s pc)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have setup := GroupedBalancedSignBottomTreeHeaderCopy67.setup_steps s pc
  have constructed : OrdinarySteps image s 23 other := by
    simpa only [show 5+18=23 by decide] using
      Keygen.ordinary_trans image s begun other 5 18 setup loop
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same,sp]
  simp [begun,GroupedBalancedSignBottomTreeHeaderCopy67.setupState,
    execInstrBr,MachineState.getReg_setReg_ne]

theorem prelude_sp (s final : MachineState) (pc : s.pc = 0x1e04)
    (trace : OrdinarySteps image s 48 final) :
    final.getReg .x2 = s.getReg .x2 := by
  let shifted := GroupedBalancedSignBottomTreeIndexData67.fullState s
  have first := GroupedBalancedSignBottomTreeIndexData67.full_steps s pc
  have shiftedPc := GroupedBalancedSignBottomTreeIndexData67.full_pc s pc
  obtain ⟨copied,second,_,_,_⟩ :=
    GroupedBalancedSignBottomTreeHeaderCopy67.header_copy shifted shiftedPc
  have constructed : OrdinarySteps image s 48 copied := by
    simpa only [show 25+23=48 by decide] using
      Keygen.ordinary_trans image s shifted copied 25 23 first second
  have same := Keygen.ordinary_deterministic trace constructed
  rw [same]
  exact (header_copy_sp shifted copied shiftedPc second).trans (index_full_sp s)

#print axioms transition_sp
#print axioms prelude_sp
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeLevelStack67
