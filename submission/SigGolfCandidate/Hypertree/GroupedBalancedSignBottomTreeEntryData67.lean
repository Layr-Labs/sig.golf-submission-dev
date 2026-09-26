import SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeCall67

/-! Control and memory frame of the bottom-tree function prologue. -/
namespace SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntryData67
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Hypertree
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

private abbrev entry := GroupedBalancedSignBottomTreeEntry67.entryState

private theorem neg_sixteen : (-16 : Word) = 18446744073709551600#64 := by
  decide

theorem entry_frame (s : MachineState) (a : Word)
    (hstack : a ≠ s.getReg .x2 - 16) (hlevel : a ≠ 0x81050) :
    (entry s).getMem a = s.getMem a := by
  change a ≠ (528464#64) at hlevel
  have hstack' : a ≠ s.getReg .x2 + 18446744073709551600#64 := by
    simpa only [BitVec.sub_eq_add_neg, neg_sixteen] using hstack
  simp [entry, GroupedBalancedSignBottomTreeEntry67.entryState,
    execInstrBr, signExtend12, BitVec.sub_eq_add_neg,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    hstack', hlevel]

theorem entry_stack (s : MachineState) :
    (entry s).getReg .x2 = s.getReg .x2 - 16 := by
  simp [entry, GroupedBalancedSignBottomTreeEntry67.entryState,
    execInstrBr, signExtend12, BitVec.sub_eq_add_neg,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem entry_link (s : MachineState) :
    (entry s).getReg .x1 = s.getReg .x1 := by
  simp [entry, GroupedBalancedSignBottomTreeEntry67.entryState,
    execInstrBr, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

theorem entry_saved_link (s : MachineState)
    (separate : s.getReg .x2 - 16 ≠ 0x81050) :
    (entry s).getMem (s.getReg .x2 - 16) = s.getReg .x1 := by
  change s.getReg .x2 - 16 ≠ (528464#64) at separate
  have separate' :
      s.getReg .x2 + 18446744073709551600#64 ≠ 528464#64 := by
    simpa only [BitVec.sub_eq_add_neg, neg_sixteen] using separate
  simp [entry, GroupedBalancedSignBottomTreeEntry67.entryState,
    execInstrBr, signExtend12, BitVec.sub_eq_add_neg,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    separate']

#print axioms entry_frame
#print axioms entry_stack
#print axioms entry_saved_link
end SigGolfCandidate.Hypertree.GroupedBalancedSignBottomTreeEntryData67
